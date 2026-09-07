import SphincsSecurity.Proof.CacheMessageSignerWeight
import SphincsSecurity.Proof.UniformOccupancyPolynomial

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
set_option backward.isDefEq.respectTransparency false

noncomputable def cachedIndexBinomialMoments (key : SecretKey) (state : CoverLogState) (degree : Nat) : ENNReal :=
  cacheMessageWeight key.parameter (fun _ source =>
    ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter state.1) key.root state.2)
      source.1).card.choose degree : ENNReal)) state.1

noncomputable def allMessageBinomialReuseMoments (key : SecretKey) (q : Nat) (state : CoverLogState) : Nat → ENNReal
  | 0 => 0
  | degree + 1 => cachedIndexBinomialMoments key state degree * digestReuseWeight q

theorem expected_signWithView_binomialOccupancy_le_allMessage (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      (binomialOccupancyMoment (observedOptionalSigningViews (messageAnswers key.parameter result.2) key.root
        (log ++ [⟨message, result.1.1⟩])) (degree + 1) : ENNReal)) ≤
      observedLogBinomialOccupancy key (degree + 1) (before, log) +
        observedLogBinomialOccupancy key degree (before, log) / (Fintype.card Index : ENNReal) +
        allMessageBinomialReuseMoments key q (before, log) (degree + 1) := by
  let views := observedOptionalSigningViews (messageAnswers key.parameter before) key.root log
  let weight := fun source : FewTimeView => ((signingSlotsAtIndex views source.1).card.choose degree : ENNReal)
  have heq : (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      (binomialOccupancyMoment (observedOptionalSigningViews (messageAnswers key.parameter result.2) key.root
        (log ++ [⟨message, result.1.1⟩])) (degree + 1) : ENNReal)) =
      ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        ((binomialOccupancyMoment views (degree + 1) : ENNReal) + successfulSignerViewWeight weight result) := by
    apply tsum_congr
    intro result
    by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
    · rw [signWithView_binomialOccupancy_eq key message before log degree hsigned result hresult]
    · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
  rw [heq]
  simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
  have hsigner := expected_successfulSignerInputWeight_le_allMessage key message before
    (fun _ source => weight source) weight (fun _ _ => le_rfl) q hq hcache
  simp only [successfulSignerInputWeight_const] at hsigner
  have huniform : (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight source) =
      (binomialOccupancyMoment views degree : ENNReal) / (Fintype.card Index : ENNReal) :=
    uniform_view_choose_expectation views degree
  rw [huniform] at hsigner
  exact (add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) hsigner).trans_eq (add_assoc _ _ _).symm

theorem expected_logTraced_sign_completion_le_allMessage (key : SecretKey) (q remaining degree : Nat)
    (hq : q ≤ 2 ^ 127) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      binomialCompletion (fun degree => observedLogBinomialOccupancy key degree result.2) remaining degree) ≤
      binomialCompletion (fun degree => observedLogBinomialOccupancy key degree state) (remaining + 1) degree +
        binomialCompletion (allMessageBinomialReuseMoments key q state) remaining degree := by
  apply expected_binomialCompletion_le
  intro d
  cases d with
  | zero =>
      simp only [observedLogBinomialOccupancy, binomialOccupancyMoment_zero, binomialStep,
        allMessageBinomialReuseMoments, add_zero, ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
  | succ d =>
      rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
      have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
          (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
        (simulateQ_signWithView_fst_run key message state.1).symm
      rw [hrun, tsum_probOutput_map_mul]
      simpa only [observedLogBinomialOccupancy, binomialStep, signingLogFragment, add_assoc] using
        expected_signWithView_binomialOccupancy_le_allMessage key message state.1 state.2 d hsigned q hq hcache

theorem expected_logTraced_sign_uniformOccupancyIncrement_le_allMessage (remaining : Nat) (key : SecretKey) (q : Nat)
    (hq : q ≤ 2 ^ 127) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      uniformOccupancyIncrement remaining key result.2.1 result.2.2) ≤
      uniformOccupancyIncrement (remaining + 1) key state.1 state.2 +
        occupancyUniformIncrementPolynomial (allMessageBinomialReuseMoments key q state) remaining := by
  simp only [uniformOccupancyIncrement_eq_polynomial, occupancyUniformIncrementPolynomial, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro degree _
  simp_rw [mul_left_comm (Pr[= _ | _])]
  rw [ENNReal.tsum_mul_left, ← mul_add, ← ENNReal.add_div]
  simp only [div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right]
  exact mul_le_mul' (mul_le_mul' le_rfl
    (expected_logTraced_sign_completion_le_allMessage key q remaining degree hq state hsigned hcache message)) le_rfl

end SphincsSecurity.Concrete
