import SphincsSecurity.Proof.WeightedPowerSigning
import SphincsSecurity.Proof.FreshTargetShapeAverage
import SphincsSecurity.Proof.TargetIndexEnvelope

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
set_option backward.isDefEq.respectTransparency false

theorem targetIndexMoments_eq_weightedPower (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (power degree : Nat) :
    targetIndexMoments key cache log power degree =
      observedWeightedPowerMoments (fun index => cachedIndexMultiplicity key.parameter cache index ^ power) key (cache, log) degree := rfl

theorem targetIndexTreeLower_eq_weighted (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (power degree : Nat) :
    targetIndexTreeLower (targetIndexMoments key cache log) power degree =
      ∑ index : Index, cachedIndexMultiplicity key.parameter cache index ^ power * cachePowerArrival degree
        ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter cache) key.root log) index).card : ENNReal) := by
  simp only [targetIndexTreeLower, targetIndexMoments, cachePowerArrival, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro lower _
  ring

theorem targetIndexReuseStep_eq_cached (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (power degree : Nat) :
    targetIndexReuseStep (targetIndexMoments key cache log) power degree =
      cacheMessageWeight key.parameter (fun _ source => cachedIndexMultiplicity key.parameter cache source.1 ^ power *
        cachePowerArrival degree ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter cache) key.root log) source.1).card : ENNReal)) cache := by
  rw [cacheMessageWeight_eq_index_sum key.parameter cache (fun index => cachedIndexMultiplicity key.parameter cache index ^ power *
    cachePowerArrival degree ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter cache) key.root log) index).card : ENNReal))]
  unfold targetIndexReuseStep
  rw [targetIndexTreeLower_eq_weighted]
  apply Finset.sum_congr rfl
  intro index _
  rw [pow_succ]
  ring

theorem targetIndexMoments_raised (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (power degree : Nat) :
    (∑ index : Index, cachedIndexMultiplicity key.parameter cache index ^ power *
      (((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter cache) key.root log) index).card + 1 : Nat) : ENNReal) ^ degree) =
      targetIndexMoments key cache log power degree + targetIndexTreeLower (targetIndexMoments key cache log) power degree := by
  simp only [Nat.cast_add, Nat.cast_one, add_one_pow_eq_cachePowerArrival, mul_add, Finset.sum_add_distrib,
    targetIndexTreeLower_eq_weighted, targetIndexMoments]

theorem expected_signWithView_frozenRawIndex_le (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (power degree : Nat) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      observedWeightedPowerMoments (fun index => cachedIndexMultiplicity key.parameter before index ^ power) key
        (result.2, log ++ [⟨message, result.1.1⟩]) degree) ≤
      targetIndexMoments key before log power degree +
        (Fintype.card Index : ENNReal)⁻¹ * targetIndexTreeLower (targetIndexMoments key before log) power degree +
          digestReuseWeight q * targetIndexReuseStep (targetIndexMoments key before log) power degree := by
  apply (expected_signWithView_weightedPower_le (fun index => cachedIndexMultiplicity key.parameter before index ^ power)
    key message before log degree hsigned q hq hcache).trans_eq
  rw [← targetIndexTreeLower_eq_weighted, ← targetIndexReuseStep_eq_cached]
  simp only [targetIndexMoments_eq_weightedPower, div_eq_mul_inv]
  ring

end SphincsSecurity.Concrete
