import SphincsSecurity.Proof.SignerMixedGrowthBound
import SphincsSecurity.Proof.MixedDerivativeQuery

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_signWithView_mixedGrowth_le_uniform (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (power degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      mixedSigningGrowthMoments key before power (result.2, log ++ [⟨message, result.1.1⟩]) degree) ≤
      ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * newMixedMomentWeight key before log power source degree := by
  apply le_trans ?_ (expected_newAdmissibleSignerView_weight_le key message before (fun source => newMixedMomentWeight key before log power source degree))
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        ∑' source, if NewAdmissibleSignerView before key (· = source) result then newMixedMomentWeight key before log power source degree else 0 := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
      · exact mul_le_mul' le_rfl (signWithView_mixedGrowth_le_newEvents key message before log power degree hsigned result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ = _ := by
      simp only [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro source
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro result
      split_ifs <;> simp

theorem raised_mixedIndexBinomialMoments (key : SecretKey) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (power degree : Nat) :
    (∑ index : Index, cachedIndexMultiplicity key.parameter before index ^ power *
      (((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) index).card + 1).choose degree : ENNReal)) =
      mixedIndexBinomialMoments key before power (before, log) degree +
        shiftBinomialMoments (mixedIndexBinomialMoments key before power (before, log)) degree := by
  cases degree with
  | zero =>
      simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, shiftBinomialMoments, add_zero,
        mixedIndexBinomialMoments, observedWeightedBinomialMoments, weightedBinomialOccupancyMoment_zero]
  | succ degree =>
      simp only [Nat.choose_succ_succ, Nat.cast_add, mul_add, Finset.sum_add_distrib, shiftBinomialMoments,
        mixedIndexBinomialMoments, observedWeightedBinomialMoments, weightedBinomialOccupancyMoment]
      exact add_comm _ _

theorem expected_newMixedMomentWeight (key : SecretKey) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (power degree : Nat) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * newMixedMomentWeight key before log power source degree) =
      (∑ lower ∈ Finset.range power, (power.choose lower : ENNReal) *
        (mixedIndexBinomialMoments key before lower (before, log) degree +
          shiftBinomialMoments (mixedIndexBinomialMoments key before lower (before, log)) degree)) / (Fintype.card Index : ENNReal) := by
  unfold newMixedMomentWeight
  rw [uniform_view_index_weight_expectation (fun index => cachePowerArrival power (cachedIndexMultiplicity key.parameter before index) *
    (((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) index).card + 1).choose degree : ENNReal)),
    weighted_cachePowerArrival_sum]
  simp only [raised_mixedIndexBinomialMoments]

theorem occupancyDerivativePolynomial_mono (order remaining : Nat) {first second : Nat → ENNReal}
    (hmoments : ∀ degree, first degree ≤ second degree) :
    occupancyDerivativePolynomial order first remaining ≤ occupancyDerivativePolynomial order second remaining := by
  apply Finset.sum_le_sum
  intro degree _
  exact mul_le_mul' le_rfl (binomialCompletion_mono hmoments remaining degree)

theorem expected_signWithView_mixedGrowthDerivative_le (power order remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      occupancyDerivativePolynomial order (mixedSigningGrowthMoments key before power (result.2, log ++ [⟨message, result.1.1⟩])) remaining) ≤
      (∑ lower ∈ Finset.range power, (power.choose lower : ENNReal) *
        (occupancyDerivativePolynomial order (mixedIndexBinomialMoments key before lower (before, log)) remaining +
          occupancyDerivativePolynomial (order + 1) (mixedIndexBinomialMoments key before lower (before, log)) remaining)) /
        (Fintype.card Index : ENNReal) := by
  rw [expected_occupancyDerivativePolynomial]
  apply (occupancyDerivativePolynomial_mono order remaining
    (fun degree => expected_signWithView_mixedGrowth_le_uniform key message before log power degree hsigned)).trans_eq
  simp only [expected_newMixedMomentWeight, div_eq_mul_inv, occupancyDerivativePolynomial_mul_right, occupancyDerivativePolynomial_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro lower _
  simp_rw [mul_comm ((power.choose lower : Nat) : ENNReal)]
  rw [occupancyDerivativePolynomial_mul_right, occupancyDerivativePolynomial_add, occupancyDerivativePolynomial_shift]

end SphincsSecurity.Concrete
