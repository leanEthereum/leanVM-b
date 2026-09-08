import SphincsSecurity.Proof.DoubleSharedParentRefundRun
import SphincsSecurity.Proof.InitializedSharedParentRefund
import SphincsSecurity.Proof.RetainedCollisionCacheReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

theorem expected_collisionPotential_add_twice_sharedParentDiscard_retained_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    (∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] *
      collisionSurvivingStructuralPotential (secretKey parameter default otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) +
      initializedSharedParentDiscard adversary parameter otsTable ftsTable q fuel * (2 * (Fintype.card Digest : ENNReal)⁻¹) ≤
      initializedBeforeFailureCollisionCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [runRetainedWithFailure, tsum_probOutput_bind_mul, initializedSharedParentDiscard, initializedBeforeFailureCollisionCharge,
    ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro initial
  simp only [mul_assoc]
  rw [← mul_add]
  by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
  · apply mul_le_mul' le_rfl
    have ha := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
    have hfin := finite_cache_of_mem_support _ ∅ initial.2.1 initial.2.2 ha finite_empty
    have hz := collisionStructuralRecordPotential_treeRoot_eq_zero (secretKey parameter initial.2.1 otsTable ftsTable) topLayer rootTree initial.2 ha
    have hcharge : collisionSigningStructuralCharge (secretKey parameter initial.2.1 otsTable ftsTable) =
        collisionSigningStructuralCharge (secretKey parameter default otsTable ftsTable) := rfl
    have hreserve : survivingFtsParentReserve (secretKey parameter initial.2.1 otsTable ftsTable) =
        survivingFtsParentReserve (secretKey parameter default otsTable ftsTable) := rfl
    cases hf : initial.1 with
    | none =>
        simp only [Option.isNone_none]
        have hzero := expected_collisionSurvivingStructuralPotential_failed_eq_zero (parentException parameter otsTable ftsTable)
          parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q) none initial.2.2 false
        simp_rw [collisionSurvivingStructuralPotential_root_irrel parameter otsTable ftsTable initial.2.1 default] at hzero
        rw [hzero, expectedSharedFailureDiscard_failed_eq_zero, zero_mul, zero_add]
        exact zero_le
    | some frame =>
        have hv := initializeRoot_valid parameter otsTable ftsTable q fuel initial hi frame hf
        have hb : (retainedComputation adversary parameter initial.2.1 q).IsQueryBoundP OtsProbeSimulation.IsOuterHash frame.ftsFuel := by
          rw [hv.1.1]
          exact retainedComputation_hashBound adversary parameter initial.2.1 q
        have hcap : ∀ result ∈ support (runWithFailure (parentException parameter otsTable ftsTable) parameter initial.2.1 otsTable ftsTable
            (retainedComputation adversary parameter initial.2.1 q) (some frame) initial.2.2 false false),
            QueryCache.enncard result.1.2.1.2 ≤ (Fintype.card Digest : ENNReal) := by
          intro result hr
          have hfull : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable)
              adversary parameter otsTable ftsTable q fuel) := by
            rw [runRetainedWithFailure, mem_support_bind_iff]
            refine ⟨initial, hi, ?_⟩
            simpa only [hf, Option.isNone_some] using hr
          apply (runRetainedWithFailure_cache_le_queryBound _ adversary q hq parameter hp otsTable ftsTable hfts fuel result hfull).trans
          apply Nat.cast_le.mpr
          rw [show Fintype.card Digest = 2 ^ 128 from card_bitVec digestBits]
          omega
        have h := expected_collisionPotential_add_twice_sharedParentDiscard_run_le parameter initial.2.1 otsTable ftsTable _ frame initial.2.2 hfin hv.2 hb
          (initializeRoot_computed parameter otsTable ftsTable q fuel initial hi frame hf) hcap
        rw [hz, zero_add, hcharge, hreserve] at h
        simp_rw [collisionSurvivingStructuralPotential_root_irrel parameter otsTable ftsTable initial.2.1 default] at h
        exact h
  · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
