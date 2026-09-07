import SphincsSecurity.Proof.AdaptiveMixedEnvelope

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def initialMixedDerivativeVector (power order : Nat) : ENNReal :=
  if power = 0 ∧ order < 15 then
    (coverageFactorialCoefficient order * order.factorial : Nat) * (Fintype.card Index : ENNReal) else 0

theorem mixedIndexBinomialMoments_empty_no_message (key : SecretKey) (cache : QueryCache HashSpec)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none) (power degree : Nat) :
    mixedIndexBinomialMoments key cache power (cache, []) degree =
      if power = 0 ∧ degree = 0 then (Fintype.card Index : ENNReal) else 0 := by
  cases power with
  | zero =>
      rw [mixedIndexBinomialMoments_zero]
      cases degree with
      | zero => simp only [observedLogBinomialOccupancy, binomialOccupancyMoment_zero, and_self, if_true]
      | succ degree => simp only [observedLogBinomialOccupancy, binomialOccupancyMoment_empty, Nat.cast_zero,
          Nat.succ_ne_zero, and_false, if_false]
  | succ power =>
      have hcounts (index : Index) : cachedIndexMultiplicity key.parameter cache index = 0 :=
        cacheMessageWeight_of_no_message key.parameter _ cache hnone
      simp only [mixedIndexBinomialMoments, observedWeightedBinomialMoments, weightedBinomialOccupancyMoment,
        hcounts, zero_pow (Nat.succ_ne_zero power), zero_mul, Finset.sum_const_zero, Nat.succ_ne_zero, false_and, if_false]

theorem observedMixedDerivativeVector_empty_no_message (key : SecretKey) (cache : QueryCache HashSpec)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none) :
    observedMixedDerivativeVector key 0 (cache, []) = initialMixedDerivativeVector := by
  funext power order
  by_cases horder : order < 15
  · unfold observedMixedDerivativeVector occupancyDerivativePolynomial
    simp only [binomialCompletion_zero, mixedIndexBinomialMoments_empty_no_message key cache hnone]
    by_cases hpower : power = 0
    · simp only [hpower, true_and, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range,
        show 0 < 15 - order by omega, if_true, Nat.zero_add, initialMixedDerivativeVector, and_self, horder]
    · simp only [hpower, false_and, if_false, mul_zero, Finset.sum_const_zero, initialMixedDerivativeVector]
  · simp only [observedMixedDerivativeVector, occupancyDerivativePolynomial_of_ge order (by omega),
      initialMixedDerivativeVector, horder, and_false, if_false]

theorem mixedCacheEnvelope_empty_no_message_le (key : SecretKey) (q signatures : Nat) (cache : QueryCache HashSpec)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none) :
    mixedCacheEnvelope key q 0 signatures (cache, []) ≤
      mixedRemainingEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) q signatures initialMixedDerivativeVector := by
  unfold mixedCacheEnvelope
  rw [observedMixedDerivativeVector_empty_no_message key cache hnone]
  exact mixedRemainingEnvelope_queries_mono _ _ _ signatures _ (Nat.sub_le _ _)

theorem expected_adaptive_validOccupancy_le_initialMixedEnvelope {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      (if SigningTranscript.Valid result.2.2 then observedLogOccupancy key result.2 else 0)) ≤
      mixedRemainingEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) q signatureLimit initialMixedDerivativeVector 0 0 :=
  (expected_adaptive_validOccupancy_le_mixedEnvelope key q hq computation cache hbudget).trans
    (mixedCacheEnvelope_empty_no_message_le key q signatureLimit cache hnone 0 0)

end SphincsSecurity.Concrete
