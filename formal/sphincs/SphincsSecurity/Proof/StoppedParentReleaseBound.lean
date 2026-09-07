import SphincsSecurity.Proof.ParentReleaseProbability
import SphincsSecurity.Proof.StoppedPotentialConservation

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition parentReserve directParentRelease
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
  (eligible : Position → Prop)
  (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
  (hsub : ∀ cache input answer, exception cache input answer → ParentSettlement parameter otsSecret ftsSecret cache input answer)

include hsub

theorem releasedParentQueryCharge_add_discard_le_direct_add_settlement
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) :
    releasedParentQueryCharge parameter otsSecret ftsSecret eligible cache input +
      exceptionDiscardCharge exception (fun current => (parentReserve parameter otsSecret ftsSecret eligible current : ENNReal)) cache input ≤
      directParentQueryCharge parameter otsSecret ftsSecret eligible cache input +
        parentSettlementReleaseCharge parameter otsSecret ftsSecret eligible cache input := by
  rw [releasedParentQueryCharge, exceptionDiscardCharge, ← ENNReal.tsum_add]
  simp_rw [← mul_add]
  by_cases hfresh : cache input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul,
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
          (releasedParentReserve_add_discard_le_direct_add_exception parameter otsSecret ftsSecret eligible exception hsub
            (answer := answer) hfinite hfresh)
        simpa only [queryException, hfresh, true_and, decide_eq_true_eq, Nat.cast_add, Nat.cast_ite, Nat.cast_zero] using h
      _ = _ := by
        simp only [mul_add, ENNReal.tsum_add]
        rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
  · obtain ⟨answer, ha⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ha, tsum_probOutput_pure_mul, releasedParentReserve_refl]
    simp only [Nat.cast_zero, queryException, hfresh, false_and, decide_false, Bool.false_eq_true, if_false,
      add_zero, directParentQueryCharge, parentSettlementReleaseCharge, le_refl]

theorem releasedParentQueryCharge_add_discard_le_direct_add_scaled
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) :
    releasedParentQueryCharge parameter otsSecret ftsSecret eligible cache input +
      exceptionDiscardCharge exception (fun current => (parentReserve parameter otsSecret ftsSecret eligible current : ENNReal)) cache input ≤
      directParentQueryCharge parameter otsSecret ftsSecret eligible cache input +
        (parentReserve parameter otsSecret ftsSecret eligible cache : ENNReal) *
          directParentQueryCharge parameter otsSecret ftsSecret (fun _ => True) cache input * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
  (releasedParentQueryCharge_add_discard_le_direct_add_settlement parameter otsSecret ftsSecret eligible exception hsub cache hfinite input).trans
    (add_le_add le_rfl (parentSettlementReleaseCharge_le_direct_scaled parameter otsSecret ftsSecret eligible hfinite input))

end SphincsSecurity
