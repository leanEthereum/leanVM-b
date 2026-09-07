import SphincsSecurity.Proof.OriginalStructuralRootPotential
import SphincsSecurity.Proof.JointProbeOriginalBeforeFailureCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem runWithFailure_cache_finite
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hfinite : Finite cache) (result) (hr : result ∈ support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed)) :
    Finite result.1.2.1.2 := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed result with
  | pure value =>
      simp only [runWithFailure_pure, mem_support_pure_iff] at hr
      subst result
      exact hfinite
  | query_bind input next ih =>
      rw [runWithFailure_query_bind, mem_support_bind_iff] at hr
      obtain ⟨head, hh, ht⟩ := hr
      have ha := stepWithFailure_original_support exception parameter root otsTable ftsTable input frame cache hit failed head hh
      have hfin := finite_cache_of_mem_support _ cache head.1.2.1.1 head.1.2.1.2
        (runExceptionMonitor_support_project exception _ cache hit ha) hfinite
      exact ih head.1.2.1.1 head.1.1 head.1.2.1.2 head.1.2.2 head.2 hfin result ht

theorem runRetainedWithFailure_cache_finite
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) (result) (hr : result ∈ support (runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel)) :
    Finite result.1.2.1.2 := by
  rw [runRetainedWithFailure, mem_support_bind_iff] at hr
  obtain ⟨initial, hi, ht⟩ := hr
  have ha := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
  have hfin := finite_cache_of_mem_support _ ∅ initial.2.1 initial.2.2 ha finite_empty
  exact runWithFailure_cache_finite exception parameter initial.2.1 otsTable ftsTable _ initial.1 initial.2.2 false initial.1.isNone hfin result ht

theorem survivingStructuralPotential_root_irrel
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (left right : Digest)
    (cache : QueryCache HashSpec) (hit failed : Bool) :
    survivingStructuralPotential (secretKey parameter left otsTable ftsTable) cache hit failed =
      survivingStructuralPotential (secretKey parameter right otsTable ftsTable) cache hit failed := by
  unfold survivingStructuralPotential
  rw [show structuralRecordPotential (secretKey parameter left otsTable ftsTable) cache none =
    structuralRecordPotential (secretKey parameter right otsTable ftsTable) cache none from
      structuralRecordPotential_root_irrel parameter _ _ left right cache none]

noncomputable def initializedBeforeFailureStructuralCharge
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : ENNReal :=
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    expectedBeforeFailureCharge (parentException parameter otsTable ftsTable) (signingStructuralCharge (secretKey parameter default otsTable ftsTable))
      parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone

theorem expected_survivingStructuralPotential_retained_le
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    (∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] *
      survivingStructuralPotential (secretKey parameter default otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) ≤
    initializedBeforeFailureStructuralCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [runRetainedWithFailure, tsum_probOutput_bind_mul, initializedBeforeFailureStructuralCharge, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro initial
  rw [mul_assoc]
  by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
  · apply mul_le_mul' le_rfl
    have ha := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
    have hfin := finite_cache_of_mem_support _ ∅ initial.2.1 initial.2.2 ha finite_empty
    have hz := structuralRecordPotential_treeRoot_eq_zero (secretKey parameter initial.2.1 otsTable ftsTable) topLayer rootTree initial.2 ha
    have hcharge : signingStructuralCharge (secretKey parameter initial.2.1 otsTable ftsTable) =
        signingStructuralCharge (secretKey parameter default otsTable ftsTable) := rfl
    cases hf : initial.1 with
    | none =>
        simp only [Option.isNone_none]
        have hzero := expected_survivingStructuralPotential_failed_eq_zero (parentException parameter otsTable ftsTable)
          parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q) none initial.2.2 false
        simp_rw [survivingStructuralPotential_root_irrel parameter otsTable ftsTable initial.2.1 default] at hzero
        rw [hzero]
        exact zero_le
    | some frame =>
        have hv := initializeRoot_valid parameter otsTable ftsTable q fuel initial hi frame hf
        have hb : (retainedComputation adversary parameter initial.2.1 q).IsQueryBoundP OtsProbeSimulation.IsOuterHash frame.ftsFuel := by
          rw [hv.1.1]
          exact retainedComputation_hashBound adversary parameter initial.2.1 q
        have h := expected_survivingStructuralPotential_run_le parameter initial.2.1 otsTable ftsTable _ frame initial.2.2 hfin hv.2 hb
          (initializeRoot_computed parameter otsTable ftsTable q fuel initial hi frame hf)
        rw [hz, zero_add, hcharge] at h
        simp_rw [survivingStructuralPotential_root_irrel parameter otsTable ftsTable initial.2.1 default] at h
        exact h
  · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]

def SurvivingStructuralFailure (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool) : Prop :=
  result.2 = false ∧ (result.1.2.2 = true ∨
    Bad parameter (secretKey parameter default otsTable ftsTable).otsSecret (secretKey parameter default otsTable ftsTable).ftsSecret result.1.2.1.2 ∨
      EncodingBad result.1.2.1.2 (secretKey parameter default otsTable ftsTable))

theorem probEvent_survivingStructuralFailure_le_beforeFailureCharge
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    Pr[SurvivingStructuralFailure parameter otsTable ftsTable |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] ≤
    initializedBeforeFailureStructuralCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ := by
  apply le_trans _ (expected_survivingStructuralPotential_retained_le adversary parameter otsTable ftsTable q fuel)
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
      · simp [survivingStructuralPotential, hf, ho]
      · cases ho : result.1.2.2 with
        | true => simp [survivingStructuralPotential, hf]
        | false =>
            simp only [survivingStructuralPotential, hf, Bool.false_eq_true, if_false]
            exact structuralRecordPotential_none_ge_bad (secretKey parameter default otsTable ftsTable) result.1.2.1.2
              (runRetainedWithFailure_cache_finite _ adversary parameter otsTable ftsTable q fuel result hr) hb
    · rw [if_neg he]
      exact zero_le
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]
    split_ifs <;> rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
