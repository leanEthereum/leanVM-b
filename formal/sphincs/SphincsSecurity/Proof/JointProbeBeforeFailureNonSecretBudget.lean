import SphincsSecurity.Proof.JointProbeOriginalBeforeFailureCharge
import SphincsSecurity.Proof.PreExceptionOuterCharge
import SphincsSecurity.Proof.JointProbeOriginalStoppedBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedBeforeFailureOuterCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Option Frame → QueryCache HashSpec → Bool → Bool → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ => 0)
    (fun input _ next frame cache hit failed =>
      (if hit || failed then 0 else outerHashQueryCharge charge input cache) +
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          next result.1.2.1.1 result.1.1 result.1.2.1.2 result.1.2.2 result.2) computation

@[simp] theorem expectedBeforeFailureOuterCharge_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (value : α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureOuterCharge exception charge parameter root otsTable ftsTable (pure value) frame cache hit failed = 0 := rfl

theorem expectedBeforeFailureOuterCharge_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureOuterCharge exception charge parameter root otsTable ftsTable (OracleSpec.query input >>= next) frame cache hit failed =
      (if hit || failed then 0 else outerHashQueryCharge charge input cache) +
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          expectedBeforeFailureOuterCharge exception charge parameter root otsTable ftsTable (next result.1.2.1.1)
            result.1.1 result.1.2.1.2 result.1.2.2 result.2 := rfl

theorem expectedBeforeFailureOuterCharge_failed_eq_zero
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedBeforeFailureOuterCharge exception charge parameter root otsTable ftsTable computation frame cache hit true = 0 := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [expectedBeforeFailureOuterCharge_query_bind, Bool.or_true, if_true, zero_add]
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit true)
      · rw [stepWithFailure_failed exception parameter root otsTable ftsTable input frame cache hit result hr, ih, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

theorem expectedBeforeFailureCharge_le_add_outer
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (first second outer : QueryCache HashSpec → HashInput → ENNReal)
    (hhash : ∀ cache input, first cache input ≤ second cache input + outer cache input)
    (hsign : ∀ message cache hit,
      expectedPreExceptionCharge exception first (sign (secretKey parameter root otsTable ftsTable) message) cache hit ≤
        expectedPreExceptionCharge exception second (sign (secretKey parameter root otsTable ftsTable) message) cache hit)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureCharge exception first parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedBeforeFailureCharge exception second parameter root otsTable ftsTable computation frame cache hit failed +
        expectedBeforeFailureOuterCharge exception outer parameter root otsTable ftsTable computation frame cache hit failed := by
  let key := secretKey parameter root otsTable ftsTable
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedBeforeFailureCharge_query_bind, expectedBeforeFailureCharge_query_bind, expectedBeforeFailureOuterCharge_query_bind]
      have hhead : (if failed then 0 else expectedPreExceptionCharge exception first (expandedAdversaryImpl key input) cache hit) ≤
          (if failed then 0 else expectedPreExceptionCharge exception second (expandedAdversaryImpl key input) cache hit) +
            if hit || failed then 0 else outerHashQueryCharge outer input cache := by
        cases failed with
        | true => simp
        | false =>
            simp only [Bool.false_eq_true, if_false, Bool.or_false]
            cases input with
            | inl query =>
                change expectedPreExceptionCharge exception first (liftM (OracleWorld.query query) : OracleComp OracleWorld _) cache hit ≤
                  expectedPreExceptionCharge exception second (liftM (OracleWorld.query query) : OracleComp OracleWorld _) cache hit +
                    if hit then 0 else hashQueryCharge outer cache query
                rw [expectedPreExceptionCharge_query, expectedPreExceptionCharge_query]
                cases hit with
                | true => simp
                | false =>
                    cases query with
                    | inl sample => simp [hashQueryCharge]
                    | inr input => exact hhash cache input
            | inr message =>
                simpa only [expandedAdversaryImpl, outerHashQueryCharge, ite_self, add_zero, scheme] using hsign message cache hit
      calc
        _ ≤ ((if failed then 0 else expectedPreExceptionCharge exception second (expandedAdversaryImpl key input) cache hit) +
              if hit || failed then 0 else outerHashQueryCharge outer input cache) +
            ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
              (expectedBeforeFailureCharge exception second parameter root otsTable ftsTable (next result.1.2.1.1)
                  result.1.1 result.1.2.1.2 result.1.2.2 result.2 +
                expectedBeforeFailureOuterCharge exception outer parameter root otsTable ftsTable (next result.1.2.1.1)
                  result.1.1 result.1.2.1.2 result.1.2.2 result.2) :=
          add_le_add hhead (ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl
            (ih result.1.2.1.1 result.1.1 result.1.2.1.2 result.1.2.2 result.2))
        _ = _ := by
          simp only [mul_add, ENNReal.tsum_add]
          ac_rfl

theorem beforeFailureStructural_le_hash_add_nonSecret
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureCharge exception (signingStructuralCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedBeforeFailureCharge exception (fun _ _ => 1) parameter root otsTable ftsTable computation frame cache hit failed +
        expectedBeforeFailureOuterCharge exception (fun _ input => if NonSecretHashInput parameter input then 1 else 0)
          parameter root otsTable ftsTable computation frame cache hit failed :=
  expectedBeforeFailureCharge_le_add_outer exception parameter root otsTable ftsTable _ _ _
    (parentStoppedEncoding_add_ftsParent_le_one_add_nonSecret (secretKey parameter root otsTable ftsTable))
    (expectedPreExceptionCharge_sign_le_preHashQueries exception (secretKey parameter root otsTable ftsTable))
    computation frame cache hit failed

theorem initializedBeforeFailureHashCharge_le_queryBound
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    (∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
      expectedBeforeFailureCharge (parentException parameter otsTable ftsTable) (fun _ _ => 1)
        parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q)
          initial.1 initial.2.2 false initial.1.isNone) ≤ q := by
  let otsSecret := OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)
  let ftsSecret := fun index tree leaf => ftsTable (index, tree, leaf)
  let restCost := fun initial : Digest × QueryCache HashSpec =>
    expectedQueryCharge (fun _ _ => 1)
      (simulateQ (expandedAdversaryImpl (secretKey parameter initial.1 otsTable ftsTable))
        (OtsProbeSimulation.retainedGameRestComputation adversary ⟨initial.1, parameter⟩)) initial.2
  have hm := tsum_probOutput_map_mul (initializeRoot parameter otsTable ftsTable q fuel) Prod.snd restCost
  rw [initializeRoot_original] at hm
  calc
    _ ≤ ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] * restCost initial.2 := by
      apply ENNReal.tsum_le_tsum
      intro initial
      apply mul_le_mul' le_rfl
      apply (expectedBeforeFailureCharge_le_preExceptionCharge _ _ _ _ _ _ _ _ _ _ _).trans
      rw [preCharge_retainedComputation_eq_uncapped _ _ adversary q hq parameter hparameter otsTable ftsTable hfts]
      exact expectedPreExceptionCharge_le_queryCharge _ _ _ _ _
    _ = ∑' initial, Pr[= initial | originalRoot parameter otsTable] * restCost initial := hm.symm
    _ ≤ expectedQueryCharge (fun _ _ => 1) (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ := by
      rw [gameAfterSecrets, expectedQueryCharge_bind]
      apply le_trans _ (le_add_left le_rfl)
      apply ENNReal.tsum_le_tsum
      intro initial
      apply mul_le_mul' le_rfl
      exact (OtsProbeSimulation.expectedQueryCharge_retained_eq_gameRest _ _ _ _ _).le
    _ ≤ q := by
      simpa only [one_mul] using expectedQueryCharge_le_queryBound (fun _ _ => 1) 1 (fun _ _ => le_rfl)
        (gameAfterSecrets adversary parameter otsSecret ftsSecret) q
        (isQueryBoundP_gameAfterSecrets adversary q hq hparameter
          (OtsProbeSimulation.mem_support_sampleOtsSecrets_all otsSecret) hfts) ∅

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
