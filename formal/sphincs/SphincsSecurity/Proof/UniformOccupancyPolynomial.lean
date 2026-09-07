import SphincsSecurity.Proof.UniformReuseIncrement

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
set_option backward.isDefEq.respectTransparency false

noncomputable def occupancyUniformIncrementPolynomial (moments : Nat → ENNReal) (remaining : Nat) : ENNReal :=
  ∑ degree ∈ Finset.range 14, (coverageFactorialCoefficient (degree + 1) * (degree + 1).factorial : Nat) *
    (binomialCompletion moments remaining degree / (Fintype.card Index : ENNReal))

theorem expected_coverageOccupancyIncrement_eq_polynomial {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * coverageOccupancyCompletionIncrement views remaining source) =
      occupancyUniformIncrementPolynomial (fun degree => (binomialOccupancyMoment views degree : ENNReal)) remaining := by
  have hstep : coverageOccupancyCompletion views (remaining + 1) = coverageOccupancyCompletion views remaining +
      occupancyUniformIncrementPolynomial (fun degree => (binomialOccupancyMoment views degree : ENNReal)) remaining := by
    simp only [coverageOccupancyCompletion, occupancyUniformIncrementPolynomial, binomialCompletion_succ, mul_add, Finset.sum_add_distrib]
  have h := expected_coverageOccupancyCompletionIncrement views remaining
  rw [hstep] at h
  exact (ENNReal.add_right_inj (coverageOccupancyCompletion_ne_top views remaining)).mp h

theorem uniformOccupancyIncrement_eq_polynomial (remaining : Nat) (key : SecretKey)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) :
    uniformOccupancyIncrement remaining key cache log =
      occupancyUniformIncrementPolynomial (fun degree => observedLogBinomialOccupancy key degree (cache, log)) remaining :=
  expected_coverageOccupancyIncrement_eq_polynomial _ remaining

theorem occupancyUniformIncrementPolynomial_mono {first second : Nat → ENNReal}
    (hmoments : ∀ degree, first degree ≤ second degree) (remaining : Nat) :
    occupancyUniformIncrementPolynomial first remaining ≤ occupancyUniformIncrementPolynomial second remaining := by
  apply Finset.sum_le_sum
  intro degree _
  exact mul_le_mul' le_rfl (mul_le_mul' (binomialCompletion_mono hmoments remaining degree) le_rfl)

theorem uniformOccupancyIncrement_mono (remaining : Nat) (key : SecretKey) (before after : CoverLogState)
    (hcache : before.1 ≤ after.1) (hprefix : before.2.IsPrefix after.2)
    (hsigned : SigningDigestsCached key.parameter before.1 key.root before.2) :
    uniformOccupancyIncrement remaining key before.1 before.2 ≤ uniformOccupancyIncrement remaining key after.1 after.2 := by
  rw [uniformOccupancyIncrement_eq_polynomial, uniformOccupancyIncrement_eq_polynomial]
  apply occupancyUniformIncrementPolynomial_mono
  intro degree
  unfold observedLogBinomialOccupancy
  rw [← observedOptionalSigningViews_cache_stable key.parameter key.root before.1 after.1 before.2 hcache hsigned]
  exact Nat.cast_le.mpr (observed_binomialOccupancy_prefix_mono _ _ _ _ hprefix degree)

theorem expected_logTraced_sign_uniformOccupancyIncrement_le (remaining : Nat) (key : SecretKey) (q : Nat)
    (hq : q ≤ 2 ^ 127) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      uniformOccupancyIncrement remaining key result.2.1 result.2.2) ≤
      uniformOccupancyIncrement (remaining + 1) key state.1 state.2 +
        occupancyUniformIncrementPolynomial (binomialReuseMoments key q state message) remaining := by
  simp only [uniformOccupancyIncrement_eq_polynomial, occupancyUniformIncrementPolynomial, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro degree _
  simp_rw [mul_left_comm (Pr[= _ | _])]
  rw [ENNReal.tsum_mul_left, ← mul_add, ← ENNReal.add_div]
  simp only [div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right]
  exact mul_le_mul' (mul_le_mul' le_rfl
    (expected_logTraced_sign_completion_le key q remaining degree hq state hsigned hcache message)) le_rfl

end SphincsSecurity.Concrete
