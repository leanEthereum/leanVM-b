import SphincsSecurity.Proof.JointProbeOriginalBeforeFailureCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def jointSurvivingCachePotential (potential : QueryCache HashSpec → Bool → ENNReal)
    (cache : QueryCache HashSpec) (hit failed : Bool) : ENNReal :=
  if failed then 0 else potential cache hit

noncomputable def sharedFailureDiscardStep
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : QueryCache HashSpec → Bool → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) : ENNReal :=
  if failed then 0 else
    ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
      if result.2 then potential result.1.2.1.2 result.1.2.2 else 0

theorem stepWithFailure_potential_add_discard
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : QueryCache HashSpec → Bool → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
      jointSurvivingCachePotential potential result.1.2.1.2 result.1.2.2 result.2) +
      sharedFailureDiscardStep exception potential parameter root otsTable ftsTable input frame cache hit failed =
      if failed then 0 else ∑' result, Pr[= result | runExceptionMonitor exception
        (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit] * potential result.1.2 result.2 := by
  cases failed with
  | true =>
      simp only [sharedFailureDiscardStep, if_true, add_zero]
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit true)
      · simp only [jointSurvivingCachePotential, stepWithFailure_failed exception parameter root otsTable ftsTable input frame cache hit result hr,
          if_true, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]
  | false =>
      simp only [sharedFailureDiscardStep, Bool.false_eq_true, if_false]
      rw [← ENNReal.tsum_add]
      have heq : (∑' result, (Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit false] *
          jointSurvivingCachePotential potential result.1.2.1.2 result.1.2.2 result.2 +
          Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit false] *
            (if result.2 then potential result.1.2.1.2 result.1.2.2 else 0))) =
          ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit false] *
            potential result.1.2.1.2 result.1.2.2 := by
        apply tsum_congr
        intro result
        rw [← mul_add, jointSurvivingCachePotential]
        split_ifs <;> simp only [zero_add, add_zero]
      rw [heq]
      have hm := tsum_probOutput_map_mul (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit false)
        Prod.fst (fun result => potential result.2.1.2 result.2.2)
      rw [stepWithFailure_project, step_expect_original exception parameter root otsTable ftsTable input frame cache hit
        (fun result => potential result.1.2 result.2)] at hm
      exact hm.symm

noncomputable def expectedSharedFailureDiscard
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : QueryCache HashSpec → Bool → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : Option Frame → QueryCache HashSpec → Bool → Bool → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ => 0)
    (fun input _ next frame cache hit failed =>
      sharedFailureDiscardStep exception potential parameter root otsTable ftsTable input frame cache hit failed +
      ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
        next result.1.2.1.1 result.1.1 result.1.2.1.2 result.1.2.2 result.2) computation

@[simp] theorem expectedSharedFailureDiscard_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : QueryCache HashSpec → Bool → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (value : α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedSharedFailureDiscard exception potential parameter root otsTable ftsTable (pure value) frame cache hit failed = 0 := rfl

theorem expectedSharedFailureDiscard_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : QueryCache HashSpec → Bool → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedSharedFailureDiscard exception potential parameter root otsTable ftsTable (OracleSpec.query input >>= next) frame cache hit failed =
      sharedFailureDiscardStep exception potential parameter root otsTable ftsTable input frame cache hit failed +
      ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
        expectedSharedFailureDiscard exception potential parameter root otsTable ftsTable (next result.1.2.1.1)
          result.1.1 result.1.2.1.2 result.1.2.2 result.2 := rfl

theorem expected_runWithFailure_potential_add_discard_charge_eq
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : QueryCache HashSpec → Bool → ENNReal)
    (release funding : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hbalance : ∀ input cache, Finite cache → ∀ hit,
      (∑' result, Pr[= result | runExceptionMonitor exception
        (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit] * potential result.1.2 result.2) +
        expectedPreExceptionCharge exception release (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit =
        potential cache hit + expectedPreExceptionCharge exception funding (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hit failed : Bool) :
    (∑' result, Pr[= result | runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed] *
      jointSurvivingCachePotential potential result.1.2.1.2 result.1.2.2 result.2) +
      expectedSharedFailureDiscard exception potential parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureCharge exception release parameter root otsTable ftsTable computation frame cache hit failed =
      jointSurvivingCachePotential potential cache hit failed +
        expectedBeforeFailureCharge exception funding parameter root otsTable ftsTable computation frame cache hit failed := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => simp
  | query_bind input next ih =>
      rw [runWithFailure_query_bind, tsum_probOutput_bind_mul, expectedSharedFailureDiscard_query_bind,
        expectedBeforeFailureCharge_query_bind, expectedBeforeFailureCharge_query_bind]
      have hhead : ((∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          jointSurvivingCachePotential potential result.1.2.1.2 result.1.2.2 result.2) +
          sharedFailureDiscardStep exception potential parameter root otsTable ftsTable input frame cache hit failed) +
          (if failed then 0 else expectedPreExceptionCharge exception release (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit) =
          jointSurvivingCachePotential potential cache hit failed +
            (if failed then 0 else expectedPreExceptionCharge exception funding (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit) := by
        rw [stepWithFailure_potential_add_discard, jointSurvivingCachePotential]
        cases failed with
        | true => simp
        | false => exact hbalance input cache hfinite hit
      calc
        _ = (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
            ((∑' final, Pr[= final | runWithFailure exception parameter root otsTable ftsTable (next result.1.2.1.1)
                result.1.1 result.1.2.1.2 result.1.2.2 result.2] * jointSurvivingCachePotential potential final.1.2.1.2 final.1.2.2 final.2) +
              expectedSharedFailureDiscard exception potential parameter root otsTable ftsTable (next result.1.2.1.1)
                result.1.1 result.1.2.1.2 result.1.2.2 result.2 +
              expectedBeforeFailureCharge exception release parameter root otsTable ftsTable (next result.1.2.1.1)
                result.1.1 result.1.2.1.2 result.1.2.2 result.2)) +
            sharedFailureDiscardStep exception potential parameter root otsTable ftsTable input frame cache hit failed +
            (if failed then 0 else expectedPreExceptionCharge exception release (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit) := by
          simp only [mul_add, ENNReal.tsum_add]
          ac_rfl
        _ = (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
            (jointSurvivingCachePotential potential result.1.2.1.2 result.1.2.2 result.2 +
              expectedBeforeFailureCharge exception funding parameter root otsTable ftsTable (next result.1.2.1.1)
                result.1.1 result.1.2.1.2 result.1.2.2 result.2)) +
            sharedFailureDiscardStep exception potential parameter root otsTable ftsTable input frame cache hit failed +
            (if failed then 0 else expectedPreExceptionCharge exception release (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit) := by
          congr 2
          apply tsum_congr
          intro result
          by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed)
          · have hm := stepWithFailure_original_support exception parameter root otsTable ftsTable input frame cache hit failed result hr
            have hf := finite_cache_of_mem_support _ cache result.1.2.1.1 result.1.2.1.2
              (runExceptionMonitor_support_project exception _ cache hit hm) hfinite
            rw [ih result.1.2.1.1 result.1.1 result.1.2.1.2 hf result.1.2.2 result.2]
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        _ = _ := by
          simp only [mul_add, ENNReal.tsum_add]
          calc
            _ = ((∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
                  jointSurvivingCachePotential potential result.1.2.1.2 result.1.2.2 result.2) +
                sharedFailureDiscardStep exception potential parameter root otsTable ftsTable input frame cache hit failed +
                (if failed then 0 else expectedPreExceptionCharge exception release (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit)) +
                ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
                  expectedBeforeFailureCharge exception funding parameter root otsTable ftsTable (next result.1.2.1.1)
                    result.1.1 result.1.2.1.2 result.1.2.2 result.2 := by ac_rfl
            _ = _ := by rw [hhead, add_assoc]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
