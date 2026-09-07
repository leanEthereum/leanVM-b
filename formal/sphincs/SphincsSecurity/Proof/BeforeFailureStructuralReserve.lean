import SphincsSecurity.Proof.SigningEncodingReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem beforeFailureStructural_add_signingNonEncoding_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureCharge exception (signingStructuralCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter)
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
        expectedBeforeFailureCharge_query_bind, expectedBeforeFailureOuterCharge_query_bind]
      have hhead : (if failed then 0 else expectedPreExceptionCharge exception (signingStructuralCharge key) (expandedAdversaryImpl key input) cache hit) +
          beforeFailureSigningStepCharge exception (nonMessageNonEncodingHashCharge parameter) key cache hit failed input ≤
          (if failed then 0 else expectedPreExceptionCharge exception (nonMessageHashCharge parameter) (expandedAdversaryImpl key input) cache hit) +
            if hit || failed then 0 else outerHashQueryCharge outer input cache := by
        cases input with
        | inl query =>
            simp only [beforeFailureSigningStepCharge, add_zero, expandedAdversaryImpl, outerHashQueryCharge]
            rw [expectedPreExceptionCharge_query, expectedPreExceptionCharge_query]
            cases hit <;> cases failed <;> simp only [Bool.or_false, Bool.or_true, Bool.false_eq_true, if_false, if_true, add_zero, zero_le]
            cases query with
            | inl sample => simp [hashQueryCharge]
            | inr input => exact signingStructuralCharge_le_nonMessage_add_nonMessageNonSecret key cache input
        | inr message =>
            simp only [beforeFailureSigningStepCharge, outerHashQueryCharge, ite_self, add_zero, expandedAdversaryImpl, scheme]
            cases failed with
            | true => simp
            | false => exact expectedPreExceptionCharge_sign_add_nonEncoding_le_nonMessage exception key message cache hit
      have htail : (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          expectedBeforeFailureCharge exception (signingStructuralCharge key) parameter root otsTable ftsTable (next result.1.2.1.1)
            result.1.1 result.1.2.1.2 result.1.2.2 result.2) +
          (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter) parameter root otsTable ftsTable (next result.1.2.1.1)
            result.1.1 result.1.2.1.2 result.1.2.2 result.2) ≤
          (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          expectedBeforeFailureCharge exception (nonMessageHashCharge parameter) parameter root otsTable ftsTable (next result.1.2.1.1)
            result.1.1 result.1.2.1.2 result.1.2.2 result.2) +
          (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          expectedBeforeFailureOuterCharge exception outer parameter root otsTable ftsTable (next result.1.2.1.1)
            result.1.1 result.1.2.1.2 result.1.2.2 result.2) := by
        rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
        apply ENNReal.tsum_le_tsum
        intro result
        rw [← mul_add, ← mul_add]
        exact mul_le_mul' le_rfl (ih result.1.2.1.1 result.1.1 result.1.2.1.2 result.1.2.2 result.2)
      convert add_le_add hhead htail using 1 <;> ac_rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
