import SphincsSecurity.Proof.CacheIndexMultiplicity

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
set_option backward.isDefEq.respectTransparency false

noncomputable def mixedIndexBinomialMoments (key : SecretKey) (sourceCache : QueryCache HashSpec)
    (power : Nat) (state : CoverLogState) (degree : Nat) : ENNReal :=
  observedWeightedBinomialMoments (fun index => cachedIndexMultiplicity key.parameter sourceCache index ^ power) key state degree

theorem mixedIndexBinomialMoments_zero (key : SecretKey) (sourceCache : QueryCache HashSpec) (state : CoverLogState) (degree : Nat) :
    mixedIndexBinomialMoments key sourceCache 0 state degree = observedLogBinomialOccupancy key degree state := by
  simp only [mixedIndexBinomialMoments, pow_zero, observedWeightedBinomialMoments, weightedBinomialOccupancyMoment_one,
    observedLogBinomialOccupancy]

theorem mixedIndexBinomialMoments_one (key : SecretKey) (state : CoverLogState) (degree : Nat) :
    mixedIndexBinomialMoments key state.1 1 state degree = cachedIndexBinomialMoments key state degree := by
  rw [cachedIndexBinomialMoments, cacheMessageWeight_eq_index_sum key.parameter state.1 (fun index =>
    ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter state.1) key.root state.2) index).card.choose degree : ENNReal))]
  simp only [mixedIndexBinomialMoments, observedWeightedBinomialMoments, weightedBinomialOccupancyMoment, pow_one]

theorem weightedCachedBinomialMoments_pow (key : SecretKey) (power : Nat) (state : CoverLogState) (degree : Nat) :
    weightedCachedBinomialMoments (fun index => cachedIndexMultiplicity key.parameter state.1 index ^ power) key state degree =
      mixedIndexBinomialMoments key state.1 (power + 1) state degree := by
  rw [weightedCachedBinomialMoments_eq_index_sum]
  unfold mixedIndexBinomialMoments observedWeightedBinomialMoments weightedBinomialOccupancyMoment
  apply Finset.sum_congr rfl
  intro index _
  dsimp only
  rw [pow_succ]
  ring

theorem expected_logTraced_sign_frozenMixedDerivative_le (power order remaining : Nat) (key : SecretKey)
    (q : Nat) (hq : q ≤ 2 ^ 127) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      occupancyDerivativePolynomial order (mixedIndexBinomialMoments key state.1 power result.2) remaining) ≤
      occupancyDerivativePolynomial order (mixedIndexBinomialMoments key state.1 power state) (remaining + 1) +
        occupancyDerivativePolynomial (order + 1) (mixedIndexBinomialMoments key state.1 (power + 1) state) remaining * digestReuseWeight q := by
  have hweights : weightedCachedBinomialMoments (fun index => cachedIndexMultiplicity key.parameter state.1 index ^ power) key state =
      mixedIndexBinomialMoments key state.1 (power + 1) state := by
    funext degree
    exact weightedCachedBinomialMoments_pow key power state degree
  have hbound := expected_logTraced_sign_weightedDerivative_le
    (fun index => cachedIndexMultiplicity key.parameter state.1 index ^ power) order remaining key q hq state hsigned hcache message
  rw [hweights] at hbound
  exact hbound

end SphincsSecurity.Concrete
