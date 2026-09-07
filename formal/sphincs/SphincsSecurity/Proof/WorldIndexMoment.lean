import SphincsSecurity.Proof.CachedIndexMomentArrival

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_romImpl_cachedOccupancyDerivative (order remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : OracleWorld.Domain)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (romImpl input).run before] *
      occupancyDerivativePolynomial order (cachedIndexBinomialMoments key (result.2, log)) remaining) =
      occupancyDerivativePolynomial order (cachedIndexBinomialMoments key (before, log)) remaining +
        hashQueryCharge (freshMessageQueryCharge key.parameter) before input *
          (occupancyDerivativePolynomial order (fun degree => observedLogBinomialOccupancy key degree (before, log)) remaining *
            (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal))) := by
  cases input with
  | inl input =>
      have hrun : (unifFwdImpl HashSpec input).run before =
          (fun sample => (sample, before)) <$> (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) := by
        simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
          (hashSpec := HashSpec) (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) before)
      change (∑' result, Pr[= result | (unifFwdImpl HashSpec input).run before] *
        occupancyDerivativePolynomial order (cachedIndexBinomialMoments key (result.2, log)) remaining) = _
      rw [hrun, tsum_probOutput_map_mul]
      dsimp only [hashQueryCharge, Sum.elim_inl]
      rw [zero_mul, add_zero, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
  | inr input => exact expected_randomOracle_cachedOccupancyDerivative order remaining key before log input hsigned

theorem expected_fixedLog_cachedOccupancyDerivative {α : Type} (order remaining : Nat) (key : SecretKey)
    (computation : OracleComp OracleWorld α) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run before] *
      occupancyDerivativePolynomial order (cachedIndexBinomialMoments key (result.2, log)) remaining) =
      occupancyDerivativePolynomial order (cachedIndexBinomialMoments key (before, log)) remaining +
        expectedQueryCharge (freshMessageQueryCharge key.parameter) computation before *
          (occupancyDerivativePolynomial order (fun degree => observedLogBinomialOccupancy key degree (before, log)) remaining *
            (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal))) := by
  induction computation using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, expectedQueryCharge_pure, zero_mul, add_zero]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul, expectedQueryCharge_query_bind]
      calc
        _ = ∑' middle, Pr[= middle | (romImpl input).run before] *
            (occupancyDerivativePolynomial order (cachedIndexBinomialMoments key (middle.2, log)) remaining +
              expectedQueryCharge (freshMessageQueryCharge key.parameter) (next middle.1) middle.2 *
                (occupancyDerivativePolynomial order (fun degree => observedLogBinomialOccupancy key degree (before, log)) remaining *
                  (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)))) := by
          apply tsum_congr
          intro middle
          by_cases hmiddle : middle ∈ support ((romImpl input).run before)
          · have hcache := simulateQ_romImpl_cache_le (OracleSpec.query input) before middle
              (by simpa only [simulateQ_spec_query] using hmiddle)
            rw [ih middle.1 middle.2 (hsigned.mono hcache)]
            simp only [observedLogBinomialOccupancy, observedOptionalSigningViews_cache_stable key.parameter key.root before middle.2 log hcache hsigned]
          · rw [probOutput_eq_zero_of_not_mem_support hmiddle, zero_mul, zero_mul]
        _ = _ := by
          simp only [mul_add, ENNReal.tsum_add]
          rw [expected_romImpl_cachedOccupancyDerivative order remaining key before log input hsigned]
          simp only [← mul_assoc, ENNReal.tsum_mul_right]
          ring

theorem cachedIndexBinomialMoments_of_no_message (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) (degree : Nat) :
    cachedIndexBinomialMoments key (cache, log) degree = 0 :=
  cacheMessageWeight_of_no_message key.parameter _ cache hnone

theorem occupancyDerivativePolynomial_zero (order remaining : Nat) :
    occupancyDerivativePolynomial order (fun _ => 0) remaining = 0 := by
  have hcompletion (degree : Nat) : binomialCompletion (fun _ => 0) remaining degree = 0 := by
    have h := binomialCompletion_mul_right (fun _ => (0 : ENNReal)) 0 remaining degree
    simpa only [mul_zero] using h
  simp only [occupancyDerivativePolynomial, hcompletion, mul_zero, Finset.sum_const_zero]

theorem expected_fixedLog_cachedOccupancyDerivative_of_no_message {α : Type} (order remaining : Nat) (key : SecretKey)
    (computation : OracleComp OracleWorld α) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → before input = none) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run before] *
      occupancyDerivativePolynomial order (cachedIndexBinomialMoments key (result.2, log)) remaining) =
      expectedQueryCharge (freshMessageQueryCharge key.parameter) computation before *
        (occupancyDerivativePolynomial order (fun degree => observedLogBinomialOccupancy key degree (before, log)) remaining *
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal))) := by
  rw [expected_fixedLog_cachedOccupancyDerivative order remaining key computation before log hsigned]
  have hzero : cachedIndexBinomialMoments key (before, log) = fun _ => 0 := by
    funext degree
    exact cachedIndexBinomialMoments_of_no_message key before log hnone degree
  rw [hzero, occupancyDerivativePolynomial_zero, zero_add]

end SphincsSecurity.Concrete
