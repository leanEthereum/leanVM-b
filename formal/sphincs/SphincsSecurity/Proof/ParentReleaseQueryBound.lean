import SphincsSecurity.Proof.ParentReleaseLocality
import SphincsSecurity.Proof.PreExceptionChargeMonotonicity

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition parentReserve directParentRelease
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
  (eligible : Position → Prop)

noncomputable def directParentQueryCharge (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if cache input = none then (directParentRelease parameter otsSecret ftsSecret eligible cache input : ENNReal) else 0

noncomputable def parentSettlementReleaseCharge (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if cache input = none then
    ∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      if ParentSettlement parameter otsSecret ftsSecret cache input answer then
        (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) else 0
  else 0

theorem parentSettlementReleaseCharge_eq_mul_prob
    {cache : QueryCache HashSpec} {input : HashInput} (hfresh : cache input = none) :
    parentSettlementReleaseCharge parameter otsSecret ftsSecret eligible cache input =
      (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) *
        Pr[ParentSettlement parameter otsSecret ftsSecret cache input | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  rw [parentSettlementReleaseCharge, if_pos hfresh, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro answer
  split_ifs
  · exact mul_comm _ _
  · simp only [mul_zero]

theorem releasedParentQueryCharge_le_direct_add_settlement
    (cache : QueryCache HashSpec) (input : HashInput) :
    releasedParentQueryCharge parameter otsSecret ftsSecret eligible cache input ≤
      directParentQueryCharge parameter otsSecret ftsSecret eligible cache input +
        parentSettlementReleaseCharge parameter otsSecret ftsSecret eligible cache input := by
  by_cases hfresh : cache input = none
  · rw [releasedParentQueryCharge, randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul,
      directParentQueryCharge, parentSettlementReleaseCharge, if_pos hfresh, if_pos hfresh]
    calc
      _ ≤ ∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
          ((directParentRelease parameter otsSecret ftsSecret eligible cache input : ENNReal) +
            if ParentSettlement parameter otsSecret ftsSecret cache input answer then
              (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) else 0) := by
        apply ENNReal.tsum_le_tsum
        intro answer
        apply mul_le_mul' le_rfl
        have h := Nat.cast_le (α := ENNReal).mpr
          (releasedParentReserve_le_direct_add_exception parameter otsSecret ftsSecret eligible (answer := answer) hfresh)
        simpa only [Nat.cast_add, Nat.cast_ite, Nat.cast_zero] using h
      _ = _ := by
        simp only [mul_add, ENNReal.tsum_add]
        rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
  · obtain ⟨answer, ha⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [releasedParentQueryCharge, randomOracle, QueryImpl.withCaching_run_some _ ha, tsum_probOutput_pure_mul,
      releasedParentReserve_refl, Nat.cast_zero, directParentQueryCharge, parentSettlementReleaseCharge, if_neg hfresh, if_neg hfresh, zero_add]

theorem expectedPreExceptionRelease_le_direct_add_settlement
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (releasedParentQueryCharge parameter otsSecret ftsSecret eligible) computation cache hit ≤
      expectedPreExceptionCharge exception (directParentQueryCharge parameter otsSecret ftsSecret eligible) computation cache hit +
        expectedPreExceptionCharge exception (parentSettlementReleaseCharge parameter otsSecret ftsSecret eligible) computation cache hit := by
  rw [← expectedPreExceptionCharge_add]
  exact expectedPreExceptionCharge_mono exception _ _ (releasedParentQueryCharge_le_direct_add_settlement parameter otsSecret ftsSecret eligible)
    computation cache hit

end SphincsSecurity
