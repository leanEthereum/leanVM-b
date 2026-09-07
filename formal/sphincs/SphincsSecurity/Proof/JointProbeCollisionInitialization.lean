import SphincsSecurity.Proof.CollisionStructuralRootPotential
import SphincsSecurity.Proof.JointProbeCollisionBeforeFailure
import SphincsSecurity.Proof.JointProbeOriginalStructuralInitialization

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem collisionSurvivingStructuralPotential_root_irrel
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (left right : Digest)
    (cache : QueryCache HashSpec) (hit failed : Bool) :
    collisionSurvivingStructuralPotential (secretKey parameter left otsTable ftsTable) cache hit failed =
      collisionSurvivingStructuralPotential (secretKey parameter right otsTable ftsTable) cache hit failed := by
  unfold collisionSurvivingStructuralPotential
  rw [show collisionStructuralRecordPotential (secretKey parameter left otsTable ftsTable) cache none =
    collisionStructuralRecordPotential (secretKey parameter right otsTable ftsTable) cache none from
      collisionStructuralRecordPotential_root_irrel parameter _ _ left right cache none]

noncomputable def initializedBeforeFailureCollisionCharge
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : ENNReal :=
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    expectedBeforeFailureCharge (parentException parameter otsTable ftsTable) (collisionSigningStructuralCharge (secretKey parameter default otsTable ftsTable))
      parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone

theorem expected_collisionSurvivingStructuralPotential_retained_le
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    (∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] *
      collisionSurvivingStructuralPotential (secretKey parameter default otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) ≤
    initializedBeforeFailureCollisionCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [runRetainedWithFailure, tsum_probOutput_bind_mul, initializedBeforeFailureCollisionCharge, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro initial
  rw [mul_assoc]
  by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
  · apply mul_le_mul' le_rfl
    have ha := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
    have hfin := finite_cache_of_mem_support _ ∅ initial.2.1 initial.2.2 ha finite_empty
    have hz := collisionStructuralRecordPotential_treeRoot_eq_zero (secretKey parameter initial.2.1 otsTable ftsTable) topLayer rootTree initial.2 ha
    have hcharge : collisionSigningStructuralCharge (secretKey parameter initial.2.1 otsTable ftsTable) =
        collisionSigningStructuralCharge (secretKey parameter default otsTable ftsTable) := rfl
    cases hf : initial.1 with
    | none =>
        simp only [Option.isNone_none]
        have hzero := expected_collisionSurvivingStructuralPotential_failed_eq_zero (parentException parameter otsTable ftsTable)
          parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q) none initial.2.2 false
        simp_rw [collisionSurvivingStructuralPotential_root_irrel parameter otsTable ftsTable initial.2.1 default] at hzero
        rw [hzero]
        exact zero_le
    | some frame =>
        have hv := initializeRoot_valid parameter otsTable ftsTable q fuel initial hi frame hf
        have hb : (retainedComputation adversary parameter initial.2.1 q).IsQueryBoundP OtsProbeSimulation.IsOuterHash frame.ftsFuel := by
          rw [hv.1.1]
          exact retainedComputation_hashBound adversary parameter initial.2.1 q
        have h := expected_collisionSurvivingStructuralPotential_run_le parameter initial.2.1 otsTable ftsTable _ frame initial.2.2 hfin hv.2 hb
          (initializeRoot_computed parameter otsTable ftsTable q fuel initial hi frame hf)
        rw [hz, zero_add, hcharge] at h
        simp_rw [collisionSurvivingStructuralPotential_root_irrel parameter otsTable ftsTable initial.2.1 default] at h
        exact h
  · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]

theorem probEvent_survivingStructuralFailure_le_beforeFailureCollisionCharge
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    Pr[SurvivingStructuralFailure parameter otsTable ftsTable |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] ≤
    initializedBeforeFailureCollisionCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ := by
  apply le_trans _ (expected_collisionSurvivingStructuralPotential_retained_le adversary parameter otsTable ftsTable q fuel)
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel)
  · by_cases he : SurvivingStructuralFailure parameter otsTable ftsTable result
    · rw [if_pos he]
      conv_lhs => rw [← mul_one (Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable)
        adversary parameter otsTable ftsTable q fuel])]
      apply mul_le_mul' le_rfl
      obtain ⟨hf, ho | hb⟩ := he
      · simp [collisionSurvivingStructuralPotential, hf, ho]
      · cases ho : result.1.2.2 with
        | true => simp [collisionSurvivingStructuralPotential, hf]
        | false =>
            simp only [collisionSurvivingStructuralPotential, hf, Bool.false_eq_true, if_false]
            exact collisionStructuralRecordPotential_none_ge_bad (secretKey parameter default otsTable ftsTable) result.1.2.1.2
              (runRetainedWithFailure_cache_finite _ adversary parameter otsTable ftsTable q fuel result hr) hb
    · rw [if_neg he]
      exact zero_le
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]
    split_ifs <;> rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
