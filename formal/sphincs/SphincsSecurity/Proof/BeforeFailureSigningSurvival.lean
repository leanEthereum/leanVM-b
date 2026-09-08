import SphincsSecurity.Proof.SigningSurvivalAfterEncoding

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def beforeFailureSigningSurvivalCredit
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (cache : QueryCache HashSpec) (hit failed : Bool) : (OracleWorld + SigningSpec).Domain → ENNReal
  | .inl _ => 0
  | .inr message => if failed then 0 else signingSurvivalCredit exception key message cache hit

noncomputable def expectedBeforeFailureSigningSurvivalCredit
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Option Frame → QueryCache HashSpec → Bool → Bool → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ => 0)
    (fun input _ next frame cache hit failed =>
      beforeFailureSigningSurvivalCredit exception (secretKey parameter root otsTable ftsTable) cache hit failed input +
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          next result.1.2.1.1 result.1.1 result.1.2.1.2 result.1.2.2 result.2) computation

@[simp] theorem expectedBeforeFailureSigningSurvivalCredit_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (value : α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureSigningSurvivalCredit exception parameter root otsTable ftsTable (pure value) frame cache hit failed = 0 := rfl

theorem expectedBeforeFailureSigningSurvivalCredit_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureSigningSurvivalCredit exception parameter root otsTable ftsTable (OracleSpec.query input >>= next) frame cache hit failed =
      beforeFailureSigningSurvivalCredit exception (secretKey parameter root otsTable ftsTable) cache hit failed input +
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          expectedBeforeFailureSigningSurvivalCredit exception parameter root otsTable ftsTable (next result.1.2.1.1)
            result.1.1 result.1.2.1.2 result.1.2.2 result.2 := rfl

private theorem beforeFailureEncodingPairs_add_survival_le_reserved
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (cap : Nat) (hcapMax : cap ≤ 2 ^ 127)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit failed : Bool)
    (hcap : ∀ result ∈ support ((simulateQ romImpl (expandedAdversaryImpl key input)).run cache), QueryCache.enncard result.2 ≤ cap) :
    beforeFailureSigningStepCharge exception (encodingPairIncrementCharge key) key cache hit failed input +
        beforeFailureSigningSurvivalCredit exception key cache hit failed input ≤
      beforeFailureSigningStepCharge exception (nonMessageNonEncodingHashCharge key.parameter) key cache hit failed input := by
  cases input with
  | inl query => simp only [beforeFailureSigningStepCharge, beforeFailureSigningSurvivalCredit, zero_add, le_refl]
  | inr message =>
      simp only [beforeFailureSigningStepCharge, beforeFailureSigningSurvivalCredit]
      cases failed with
      | true => simp
      | false =>
          simp only [Bool.false_eq_true, if_false]
          apply expected_encodingPairs_add_survival_sign_le_reserved exception key message cap hcapMax cache hfinite hit
          simpa only [OracleSpec.Range, OracleSpec.add_apply_inr, expandedAdversaryImpl, scheme] using hcap

theorem expected_beforeFailureEncodingPairs_add_survival_le_reserved
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (hcapMax : cap ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit failed : Bool)
    (hcap : ∀ result ∈ support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed),
      QueryCache.enncard result.1.2.1.2 ≤ cap) :
    expectedBeforeFailureSigningCharge exception (encodingPairIncrementCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureSigningSurvivalCredit exception parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter)
        parameter root otsTable ftsTable computation frame cache hit failed := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedBeforeFailureSigningCharge_query_bind, expectedBeforeFailureSigningSurvivalCredit_query_bind,
        expectedBeforeFailureSigningCharge_query_bind, add_add_add_comm, ← ENNReal.tsum_add]
      simp_rw [← mul_add]
      apply add_le_add
      · exact beforeFailureEncodingPairs_add_survival_le_reserved exception (secretKey parameter root otsTable ftsTable)
          cap hcapMax input cache hfinite hit failed
          (runWithFailure_expanded_head_cache_cap exception parameter root otsTable ftsTable input next frame cache hit failed cap hcap)
      · apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed)
        · have hm := stepWithFailure_original_support exception parameter root otsTable ftsTable input frame cache hit failed result hr
          have hf := finite_cache_of_mem_support _ cache result.1.2.1.1 result.1.2.1.2
            (runExceptionMonitor_support_project exception _ cache hit hm) hfinite
          exact mul_le_mul' le_rfl (ih result.1.2.1.1 result.1.1 result.1.2.1.2 hf result.1.2.2 result.2
            (runWithFailure_tail_cache_cap exception parameter root otsTable ftsTable input next frame cache hit failed cap hcap result hr))
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
