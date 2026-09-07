import SphincsSecurity.Proof.OccupancyDerivative
import SphincsSecurity.Proof.LinearReserveMessageCount

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem cachedIndexBinomialMoments_cacheQuery (key : SecretKey) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (input : HashInput) (output : HashOutput) (degree : Nat) (hfresh : before input = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    cachedIndexBinomialMoments key (before.cacheQuery input output, log) degree = cachedIndexBinomialMoments key (before, log) degree +
      (if MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
        ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log)
          (hashOutputFewTimeView output).1).card.choose degree : ENNReal) else 0) := by
  simp only [cachedIndexBinomialMoments, observedOptionalSigningViews_cache_stable key.parameter key.root before _ log
    (QueryCache.le_cacheQuery before hfresh) hsigned, cacheMessageWeight_cacheQuery key.parameter _ before input output hfresh]

theorem expected_message_cachedIndexBinomialMoments (key : SecretKey) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (input : HashInput) (degree : Nat) (hfresh : before input = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (hmessage : MessageHashInput key.parameter input) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      cachedIndexBinomialMoments key (before.cacheQuery input output, log) degree) =
      cachedIndexBinomialMoments key (before, log) degree + observedLogBinomialOccupancy key degree (before, log) *
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 := tsum_probOutput_eq_one' (by simp)
  simp only [cachedIndexBinomialMoments_cacheQuery key before log input _ degree hfresh hsigned, hmessage, true_and,
    mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
  rw [expected_uniformHashOutput_admissible_weight (fun source : FewTimeView =>
    ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1).card.choose degree : ENNReal)),
    uniform_view_choose_expectation]
  unfold observedLogBinomialOccupancy
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem expected_message_cachedOccupancyDerivative (order remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (hfresh : before input = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (hmessage : MessageHashInput key.parameter input) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      occupancyDerivativePolynomial order (cachedIndexBinomialMoments key (before.cacheQuery input output, log)) remaining) =
      occupancyDerivativePolynomial order (cachedIndexBinomialMoments key (before, log)) remaining +
        occupancyDerivativePolynomial order (fun degree => observedLogBinomialOccupancy key degree (before, log)) remaining *
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) := by
  rw [expected_occupancyDerivativePolynomial]
  simp only [expected_message_cachedIndexBinomialMoments key before log input _ hfresh hsigned hmessage,
    occupancyDerivativePolynomial_add, occupancyDerivativePolynomial_mul_right]

theorem expected_randomOracle_cachedOccupancyDerivative (order remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (randomOracle input).run before] *
      occupancyDerivativePolynomial order (cachedIndexBinomialMoments key (result.2, log)) remaining) =
      occupancyDerivativePolynomial order (cachedIndexBinomialMoments key (before, log)) remaining +
        freshMessageQueryCharge key.parameter before input *
          (occupancyDerivativePolynomial order (fun degree => observedLogBinomialOccupancy key degree (before, log)) remaining *
            (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal))) := by
  by_cases hfresh : before input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    change (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      occupancyDerivativePolynomial order (cachedIndexBinomialMoments key (before.cacheQuery input output, log)) remaining) = _
    by_cases hmessage : MessageHashInput key.parameter input
    · simp only [freshMessageQueryCharge, hfresh, hmessage, and_self, if_true, one_mul]
      exact expected_message_cachedOccupancyDerivative order remaining key before log input hfresh hsigned hmessage
    · have hstable (output : HashOutput) : cachedIndexBinomialMoments key (before.cacheQuery input output, log) =
          cachedIndexBinomialMoments key (before, log) := by
        funext degree
        simp only [cachedIndexBinomialMoments_cacheQuery key before log input output degree hfresh hsigned, hmessage, false_and, if_false, add_zero]
      have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 := tsum_probOutput_eq_one' (by simp)
      simp only [hstable, ENNReal.tsum_mul_right, hmass, one_mul, freshMessageQueryCharge, hmessage, and_false, if_false, zero_mul, add_zero]
  · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ houtput, tsum_probOutput_pure_mul]
    simp only [freshMessageQueryCharge, hfresh, false_and, if_false, zero_mul, add_zero]

end SphincsSecurity.Concrete
