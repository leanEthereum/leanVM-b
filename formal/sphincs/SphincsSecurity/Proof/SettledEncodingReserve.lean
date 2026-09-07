import SphincsSecurity.Proof.BeforeFailureStructuralReserve
import SphincsSecurity.Proof.EncodingMessageConservation

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def settledEncodingQueryReserve (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if ∃ position : EncodingPosition, AtEncodingPosition key.parameter input position ∧
      EncodingMessageSettledAt cache key position then 1 else 0

attribute [local irreducible] settledEncodingQueryReserve

theorem encodingMessageIncrement_add_settledEncodingReserve
    (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) (position : EncodingPosition)
    (hat : AtEncodingPosition key.parameter input position) :
    (encodingMessageIncrement cache key position : ENNReal) + settledEncodingQueryReserve key cache input = 1 := by
  by_cases hs : EncodingMessageSettledAt cache key position
  · have he : ∃ candidate : EncodingPosition, AtEncodingPosition key.parameter input candidate ∧
        EncodingMessageSettledAt cache key candidate := ⟨position, hat, hs⟩
    simp only [encodingMessageIncrement, if_pos hs, Nat.cast_zero, settledEncodingQueryReserve, if_pos he, zero_add]
  · have he : ¬∃ candidate : EncodingPosition, AtEncodingPosition key.parameter input candidate ∧
        EncodingMessageSettledAt cache key candidate := by
      rintro ⟨candidate, hc, hsettled⟩
      exact hs ((atEncodingPosition_unique hc hat) ▸ hsettled)
    simp only [encodingMessageIncrement, if_neg hs, Nat.cast_one, settledEncodingQueryReserve, if_neg he, add_zero]

theorem encodingMessageReserve_add_settledEncodingReserve_conserved
    {cache : QueryCache HashSpec} (hfinite : Finite cache) (key : SecretKey)
    {input : HashInput} {answer : HashOutput} (position : EncodingPosition)
    (hfresh : cache input = none) (hat : AtEncodingPosition key.parameter input position) :
    (encodingMessageReserve (cache.cacheQuery input answer) key : ENNReal) + settledEncodingQueryReserve key cache input =
      (encodingMessageReserve cache key : ENNReal) + 1 := by
  rw [encodingMessageReserve_cacheQuery_eq_increment hfinite hfresh hat, Nat.cast_add, add_assoc,
    encodingMessageIncrement_add_settledEncodingReserve key cache input position hat]

theorem signingStructuralCharge_add_settledEncoding_le
    (key : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    signingStructuralCharge key cache input + settledEncodingQueryReserve key cache input ≤
      nonMessageHashCharge key.parameter cache input +
        if NonMessageNonSecretHashInput key.parameter input then 1 else 0 := by
  unfold settledEncodingQueryReserve
  by_cases hsettled : ∃ position : EncodingPosition, AtEncodingPosition key.parameter input position ∧
      EncodingMessageSettledAt cache key position
  · rw [if_pos hsettled]
    obtain ⟨position, hat, hs⟩ := hsettled
    have hm : ¬ MessageHashInput key.parameter input := fun h => h.not_atEncoding position hat
    have hn : NonMessageNonSecretHashInput key.parameter input := ⟨NonSecretHashInput.of_atEncoding hat, hm⟩
    simpa only [nonMessageHashCharge, if_neg hm, if_pos hn] using
      add_le_add (signingStructuralCharge_le_one_of_encoding_settled key cache input position hat hs) (le_refl (1 : ENNReal))
  · rw [if_neg hsettled, add_zero]
    exact signingStructuralCharge_le_nonMessage_add_nonMessageNonSecret key cache input

namespace JointOriginal

attribute [local irreducible] signingStructuralCharge nonMessageNonEncodingHashCharge
attribute [local irreducible] nonMessageHashCharge expectedBeforeFailureCharge expectedBeforeFailureSigningCharge expectedBeforeFailureOuterCharge

theorem beforeFailureCharge_add_signingNonEncoding_add_outerReserve_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (charge extra : QueryCache HashSpec → HashInput → ENNReal)
    (hsign : ∀ message cache hit,
      expectedPreExceptionCharge exception charge (sign (secretKey parameter root otsTable ftsTable) message) cache hit +
        expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge parameter)
          (sign (secretKey parameter root otsTable ftsTable) message) cache hit ≤
        expectedPreExceptionCharge exception (nonMessageHashCharge parameter)
          (sign (secretKey parameter root otsTable ftsTable) message) cache hit)
    (hhash : ∀ cache input,
      charge cache input + extra cache input ≤
        nonMessageHashCharge parameter cache input + if NonMessageNonSecretHashInput parameter input then 1 else 0)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureCharge exception charge
        parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter)
        parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureOuterCharge exception extra
        parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedBeforeFailureCharge exception (nonMessageHashCharge parameter)
        parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureOuterCharge exception (fun _ input => if NonMessageNonSecretHashInput parameter input then 1 else 0)
        parameter root otsTable ftsTable computation frame cache hit failed := by
  let key := secretKey parameter root otsTable ftsTable
  let outer := fun (_ : QueryCache HashSpec) input => if NonMessageNonSecretHashInput parameter input then (1 : ENNReal) else 0
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedBeforeFailureCharge_query_bind, expectedBeforeFailureSigningCharge_query_bind,
        expectedBeforeFailureOuterCharge_query_bind, expectedBeforeFailureCharge_query_bind, expectedBeforeFailureOuterCharge_query_bind]
      have hhead : ((if failed then 0 else expectedPreExceptionCharge exception charge (expandedAdversaryImpl key input) cache hit) +
          beforeFailureSigningStepCharge exception (nonMessageNonEncodingHashCharge parameter) key cache hit failed input) +
          (if hit || failed then 0 else outerHashQueryCharge extra input cache) ≤
          (if failed then 0 else expectedPreExceptionCharge exception (nonMessageHashCharge parameter) (expandedAdversaryImpl key input) cache hit) +
            if hit || failed then 0 else outerHashQueryCharge outer input cache := by
        cases input with
        | inl query =>
            simp only [beforeFailureSigningStepCharge, add_zero, expandedAdversaryImpl, outerHashQueryCharge]
            rw [expectedPreExceptionCharge_query, expectedPreExceptionCharge_query]
            cases hit <;> cases failed <;> simp only [Bool.or_false, Bool.or_true, Bool.false_eq_true, if_false, if_true, add_zero, zero_le]
            cases query with
            | inl sample => simp [hashQueryCharge]
            | inr input => exact hhash cache input
        | inr message =>
            simp only [beforeFailureSigningStepCharge, outerHashQueryCharge, ite_self, add_zero, expandedAdversaryImpl, scheme]
            cases failed with
            | true => simp
            | false => exact hsign message cache hit
      have htail : (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          expectedBeforeFailureCharge exception charge parameter root otsTable ftsTable (next result.1.2.1.1)
            result.1.1 result.1.2.1.2 result.1.2.2 result.2) +
          (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter) parameter root otsTable ftsTable (next result.1.2.1.1)
            result.1.1 result.1.2.1.2 result.1.2.2 result.2) +
          (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          expectedBeforeFailureOuterCharge exception extra parameter root otsTable ftsTable (next result.1.2.1.1)
            result.1.1 result.1.2.1.2 result.1.2.2 result.2) ≤
          (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          expectedBeforeFailureCharge exception (nonMessageHashCharge parameter) parameter root otsTable ftsTable (next result.1.2.1.1)
            result.1.1 result.1.2.1.2 result.1.2.2 result.2) +
          (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          expectedBeforeFailureOuterCharge exception outer parameter root otsTable ftsTable (next result.1.2.1.1)
            result.1.1 result.1.2.1.2 result.1.2.2 result.2) := by
        rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
        apply ENNReal.tsum_le_tsum
        intro result
        rw [← mul_add, ← mul_add, ← mul_add]
        exact mul_le_mul' le_rfl (ih result.1.2.1.1 result.1.1 result.1.2.1.2 result.1.2.2 result.2)
      convert add_le_add hhead htail using 1 <;> ac_rfl

theorem beforeFailureStructural_add_signingNonEncoding_add_outerReserve_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (extra : QueryCache HashSpec → HashInput → ENNReal)
    (hhash : ∀ cache input,
      signingStructuralCharge (secretKey parameter root otsTable ftsTable) cache input + extra cache input ≤
        nonMessageHashCharge parameter cache input + if NonMessageNonSecretHashInput parameter input then 1 else 0)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureCharge exception (signingStructuralCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter)
        parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureOuterCharge exception extra
        parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedBeforeFailureCharge exception (nonMessageHashCharge parameter)
        parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureOuterCharge exception (fun _ input => if NonMessageNonSecretHashInput parameter input then 1 else 0)
        parameter root otsTable ftsTable computation frame cache hit failed :=
  beforeFailureCharge_add_signingNonEncoding_add_outerReserve_le exception parameter root otsTable ftsTable
    (signingStructuralCharge (secretKey parameter root otsTable ftsTable)) extra
    (expectedPreExceptionCharge_sign_add_nonEncoding_le_nonMessage exception (secretKey parameter root otsTable ftsTable))
    hhash computation frame cache hit failed

theorem beforeFailureStructural_add_signingNonEncoding_add_settledEncoding_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureCharge exception (signingStructuralCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter)
        parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureOuterCharge exception (settledEncodingQueryReserve (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedBeforeFailureCharge exception (nonMessageHashCharge parameter)
        parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureOuterCharge exception (fun _ input => if NonMessageNonSecretHashInput parameter input then 1 else 0)
        parameter root otsTable ftsTable computation frame cache hit failed :=
  beforeFailureStructural_add_signingNonEncoding_add_outerReserve_le exception parameter root otsTable ftsTable
    (settledEncodingQueryReserve (secretKey parameter root otsTable ftsTable))
    (signingStructuralCharge_add_settledEncoding_le (secretKey parameter root otsTable ftsTable))
    computation frame cache hit failed

end JointOriginal
end SphincsSecurity.Concrete.FtsProbeSimulation
