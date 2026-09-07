import SphincsSecurity.Proof.WeightedBinomialOccupancy
import SphincsSecurity.Proof.OccupancyDerivative

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
set_option backward.isDefEq.respectTransparency false

noncomputable def observedWeightedBinomialMoments (weights : Index → ENNReal) (key : SecretKey)
    (state : CoverLogState) (degree : Nat) : ENNReal :=
  weightedBinomialOccupancyMoment weights (observedOptionalSigningViews (messageAnswers key.parameter state.1) key.root state.2) degree

noncomputable def weightedCachedBinomialMoments (weights : Index → ENNReal) (key : SecretKey)
    (state : CoverLogState) (degree : Nat) : ENNReal :=
  cacheMessageWeight key.parameter (fun _ source => weights source.1 *
    ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter state.1) key.root state.2)
      source.1).card.choose degree : ENNReal)) state.1

theorem signWithView_weightedBinomial_eq (weights : Index → ENNReal) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    observedWeightedBinomialMoments weights key (result.2, log ++ [⟨message, result.1.1⟩]) (degree + 1) =
      observedWeightedBinomialMoments weights key (before, log) (degree + 1) + successfulSignerViewWeight (fun source =>
        weights source.1 * ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log)
          source.1).card.choose degree : ENNReal)) result := by
  have hstable := observedOptionalSigningViews_cache_stable key.parameter key.root before result.2 log
    (simulateQ_romImpl_cache_le (signWithView key message) before result hresult) hsigned
  unfold observedWeightedBinomialMoments
  cases hresponse : result.1.1 with
  | none =>
      rw [observed_weightedBinomial_append_none _ _ _ _ _ _ (by simp [observedSigningView?]), hstable]
      simp only [successfulSignerViewWeight, hresponse, add_zero]
  | some signature =>
      have hresult' : ((some signature, result.1.2), result.2) ∈ support
          ((simulateQ romImpl (signWithView key message)).run before) := by
        have heq : result = ((some signature, result.1.2), result.2) := Prod.ext (Prod.ext hresponse rfl) rfl
        rwa [heq] at hresult
      obtain ⟨output, houtput, _, hview⟩ := signWithView_successful_cached_output key message before result.2 signature result.1.2 hresult'
      have hsource : observedSigningView? (messageAnswers key.parameter result.2) key.root ⟨message, some signature⟩ = some (hashOutputFewTimeView output) := by
        simp [observedSigningView?, messageAnswers, houtput]
      rw [observed_weightedBinomial_append_some _ _ _ _ _ _ _ hsource, hstable]
      simp only [successfulSignerViewWeight, hresponse, hview]

theorem expected_signWithView_weightedBinomial_le (weights : Index → ENNReal) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      observedWeightedBinomialMoments weights key (result.2, log ++ [⟨message, result.1.1⟩]) (degree + 1)) ≤
      observedWeightedBinomialMoments weights key (before, log) (degree + 1) +
        observedWeightedBinomialMoments weights key (before, log) degree / (Fintype.card Index : ENNReal) +
        weightedCachedBinomialMoments weights key (before, log) degree * digestReuseWeight q := by
  let weight := fun source : FewTimeView => weights source.1 *
    ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1).card.choose degree : ENNReal)
  have heq : (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      observedWeightedBinomialMoments weights key (result.2, log ++ [⟨message, result.1.1⟩]) (degree + 1)) =
      ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        (observedWeightedBinomialMoments weights key (before, log) (degree + 1) + successfulSignerViewWeight weight result) := by
    apply tsum_congr
    intro result
    by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
    · rw [signWithView_weightedBinomial_eq weights key message before log degree hsigned result hresult]
    · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
  rw [heq]
  simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
  have hsigner := expected_successfulSignerInputWeight_le_allMessage key message before
    (fun _ source => weight source) weight (fun _ _ => le_rfl) q hq hcache
  simp only [successfulSignerInputWeight_const] at hsigner
  have huniform : (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight source) =
      observedWeightedBinomialMoments weights key (before, log) degree / (Fintype.card Index : ENNReal) :=
    uniform_view_index_weight_expectation (fun index => weights index *
      ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) index).card.choose degree : ENNReal))
  rw [huniform] at hsigner
  exact (add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) hsigner).trans_eq (add_assoc _ _ _).symm

theorem expected_logTraced_sign_weightedCompletion_le (weights : Index → ENNReal) (key : SecretKey)
    (q remaining degree : Nat) (hq : q ≤ 2 ^ 127) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      binomialCompletion (observedWeightedBinomialMoments weights key result.2) remaining degree) ≤
      binomialCompletion (observedWeightedBinomialMoments weights key state) (remaining + 1) degree +
        binomialCompletion (shiftBinomialMoments (fun degree => weightedCachedBinomialMoments weights key state degree * digestReuseWeight q)) remaining degree := by
  apply expected_binomialCompletion_le
  intro d
  cases d with
  | zero =>
      simp only [observedWeightedBinomialMoments, weightedBinomialOccupancyMoment_zero, binomialStep,
        shiftBinomialMoments, add_zero, ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
  | succ d =>
      rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
      have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
          (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
        (simulateQ_signWithView_fst_run key message state.1).symm
      rw [hrun, tsum_probOutput_map_mul]
      simpa only [binomialStep, signingLogFragment, shiftBinomialMoments, add_assoc] using
        expected_signWithView_weightedBinomial_le weights key message state.1 state.2 d hsigned q hq hcache

theorem expected_logTraced_sign_weightedDerivative_le (weights : Index → ENNReal) (order remaining : Nat)
    (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      occupancyDerivativePolynomial order (observedWeightedBinomialMoments weights key result.2) remaining) ≤
      occupancyDerivativePolynomial order (observedWeightedBinomialMoments weights key state) (remaining + 1) +
        occupancyDerivativePolynomial (order + 1) (weightedCachedBinomialMoments weights key state) remaining * digestReuseWeight q := by
  rw [← occupancyDerivativePolynomial_mul_right, ← occupancyDerivativePolynomial_shift]
  simp only [occupancyDerivativePolynomial, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro degree _
  simp_rw [mul_left_comm (Pr[= _ | _])]
  rw [ENNReal.tsum_mul_left, ← mul_add]
  exact mul_le_mul' le_rfl (expected_logTraced_sign_weightedCompletion_le weights key q remaining degree hq state hsigned hcache message)

end SphincsSecurity.Concrete
