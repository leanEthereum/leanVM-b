import SphincsSecurity.Proof.MixedOccupancySigning

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def mixedSigningGrowthMoments (key : SecretKey) (before : QueryCache HashSpec)
    (power : Nat) (after : CoverLogState) : Nat → ENNReal :=
  observedWeightedBinomialMoments (fun index => cachedIndexMultiplicity key.parameter after.1 index ^ power -
    cachedIndexMultiplicity key.parameter before index ^ power) key after

theorem mixedIndexBinomialMoments_eq_frozen_add_growth (key : SecretKey) (before : QueryCache HashSpec)
    (power : Nat) (after : CoverLogState) (hcache : before ≤ after.1) (degree : Nat) :
    mixedIndexBinomialMoments key after.1 power after degree =
      mixedIndexBinomialMoments key before power after degree + mixedSigningGrowthMoments key before power after degree := by
  have hweights (index : Index) : cachedIndexMultiplicity key.parameter after.1 index ^ power =
      cachedIndexMultiplicity key.parameter before index ^ power +
        (cachedIndexMultiplicity key.parameter after.1 index ^ power - cachedIndexMultiplicity key.parameter before index ^ power) :=
    (add_tsub_cancel_of_le (pow_le_pow_left' (cachedIndexMultiplicity_mono key.parameter before after.1 hcache index) power)).symm
  unfold mixedIndexBinomialMoments mixedSigningGrowthMoments observedWeightedBinomialMoments weightedBinomialOccupancyMoment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  dsimp only
  conv_lhs => rw [hweights]
  rw [add_mul]

theorem expected_logTraced_sign_mixedDerivative_le_growth (power order remaining : Nat) (key : SecretKey)
    (q : Nat) (hq : q ≤ 2 ^ 127) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      occupancyDerivativePolynomial order (mixedIndexBinomialMoments key result.2.1 power result.2) remaining) ≤
      occupancyDerivativePolynomial order (mixedIndexBinomialMoments key state.1 power state) (remaining + 1) +
        occupancyDerivativePolynomial (order + 1) (mixedIndexBinomialMoments key state.1 (power + 1) state) remaining * digestReuseWeight q +
          ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
            occupancyDerivativePolynomial order (mixedSigningGrowthMoments key state.1 power result.2) remaining := by
  have hdecompose : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      occupancyDerivativePolynomial order (mixedIndexBinomialMoments key result.2.1 power result.2) remaining) =
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
        (occupancyDerivativePolynomial order (mixedIndexBinomialMoments key state.1 power result.2) remaining +
          occupancyDerivativePolynomial order (mixedSigningGrowthMoments key state.1 power result.2) remaining) := by
    apply tsum_congr
    intro result
    by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
    · have hmoment : mixedIndexBinomialMoments key result.2.1 power result.2 =
          (fun degree => mixedIndexBinomialMoments key state.1 power result.2 degree + mixedSigningGrowthMoments key state.1 power result.2 degree) := by
        funext degree
        exact mixedIndexBinomialMoments_eq_frozen_add_growth key state.1 power result.2
          (logTracedMappedAdversaryImpl_cache_le key (.inr message) state result hresult) degree
      rw [hmoment, occupancyDerivativePolynomial_add]
    · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
  rw [hdecompose]
  simp only [mul_add, ENNReal.tsum_add]
  exact add_le_add (expected_logTraced_sign_frozenMixedDerivative_le power order remaining key q hq state hsigned hcache message) le_rfl

end SphincsSecurity.Concrete
