import SphincsSecurity.Proof.CachedMultiplicityPower

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def weightedPowerMoment (weights : Index → ENNReal) (views : Fin n → Option FewTimeView) (degree : Nat) : ENNReal :=
  ∑ index : Index, weights index * ((signingSlotsAtIndex views index).card : ENNReal) ^ degree

noncomputable def observedWeightedPowerMoments (weights : Index → ENNReal) (key : SecretKey) (state : CoverLogState) (degree : Nat) : ENNReal :=
  weightedPowerMoment weights (observedOptionalSigningViews (messageAnswers key.parameter state.1) key.root state.2) degree

theorem weightedPowerMoment_insert (weights : Index → ENNReal) (views : Fin n → Option FewTimeView) (source : FewTimeView) (degree : Nat) :
    weightedPowerMoment weights (insertFewTimeView views source) degree = weightedPowerMoment weights views degree +
      weights source.1 * cachePowerArrival degree ((signingSlotsAtIndex views source.1).card : ENNReal) := by
  have hpoint (index : Index) :
      (((signingSlotsAtIndex views index).card + if source.1 = index then 1 else 0 : Nat) : ENNReal) ^ degree =
        ((signingSlotsAtIndex views index).card : ENNReal) ^ degree +
          if source.1 = index then cachePowerArrival degree ((signingSlotsAtIndex views source.1).card : ENNReal) else 0 := by
    by_cases heq : source.1 = index
    · subst index
      simp only [if_true, Nat.cast_add, Nat.cast_one, add_one_pow_eq_cachePowerArrival]
    · simp only [heq, if_false, add_zero]
  simp only [weightedPowerMoment, signingSlotsAtIndex_insert_card, hpoint, mul_add, Finset.sum_add_distrib,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem observed_weightedPower_append_none (weights : Index → ENNReal) (answers : HashInput → Option HashOutput)
    (root : Digest) (log : QueryLog SigningSpec) (entry : SigningEntry) (degree : Nat)
    (hnone : observedSigningView? answers root entry = none) :
    weightedPowerMoment weights (observedOptionalSigningViews answers root (log ++ [entry])) degree =
      weightedPowerMoment weights (observedOptionalSigningViews answers root log) degree := by
  unfold weightedPowerMoment observedOptionalSigningViews
  simp only [signingSlotsAtIndex_log_append_card, hnone, reduceCtorEq, false_and, exists_false, if_false, add_zero]

theorem observed_weightedPower_append_some (weights : Index → ENNReal) (answers : HashInput → Option HashOutput)
    (root : Digest) (log : QueryLog SigningSpec) (entry : SigningEntry) (source : FewTimeView) (degree : Nat)
    (hsome : observedSigningView? answers root entry = some source) :
    weightedPowerMoment weights (observedOptionalSigningViews answers root (log ++ [entry])) degree =
      weightedPowerMoment weights (observedOptionalSigningViews answers root log) degree +
        weights source.1 * cachePowerArrival degree ((signingSlotsAtIndex (observedOptionalSigningViews answers root log) source.1).card : ENNReal) := by
  rw [← weightedPowerMoment_insert]
  unfold weightedPowerMoment observedOptionalSigningViews
  simp only [signingSlotsAtIndex_log_append_card, signingSlotsAtIndex_insert_card, hsome, Option.some.injEq, exists_eq_left']

theorem signWithView_weightedPower_eq (weights : Index → ENNReal) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    observedWeightedPowerMoments weights key (result.2, log ++ [⟨message, result.1.1⟩]) degree =
      observedWeightedPowerMoments weights key (before, log) degree + successfulSignerViewWeight (fun source =>
        weights source.1 * cachePowerArrival degree ((signingSlotsAtIndex
          (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1).card : ENNReal)) result := by
  have hstable := observedOptionalSigningViews_cache_stable key.parameter key.root before result.2 log
    (simulateQ_romImpl_cache_le (signWithView key message) before result hresult) hsigned
  unfold observedWeightedPowerMoments
  cases hresponse : result.1.1 with
  | none =>
      rw [observed_weightedPower_append_none _ _ _ _ _ _ (by simp [observedSigningView?]), hstable]
      simp only [successfulSignerViewWeight, hresponse, add_zero]
  | some signature =>
      have hresult' : ((some signature, result.1.2), result.2) ∈ support
          ((simulateQ romImpl (signWithView key message)).run before) := by
        have heq : result = ((some signature, result.1.2), result.2) := Prod.ext (Prod.ext hresponse rfl) rfl
        rwa [heq] at hresult
      obtain ⟨output, houtput, _, hview⟩ := signWithView_successful_cached_output key message before result.2 signature result.1.2 hresult'
      have hsource : observedSigningView? (messageAnswers key.parameter result.2) key.root ⟨message, some signature⟩ = some (hashOutputFewTimeView output) := by
        simp [observedSigningView?, messageAnswers, houtput]
      rw [observed_weightedPower_append_some _ _ _ _ _ _ _ hsource, hstable]
      simp only [successfulSignerViewWeight, hresponse, hview]

theorem expected_signWithView_weightedPower_le_of_reuseWeight (weights : Index → ENNReal) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuseWeight : ENNReal)
    (hreuse : ∀ input, Pr[PrehitSuccessfulSignerView (onlyInputCache before input) key message (fun _ => True) |
      (simulateQ romImpl (signWithView key message)).run before] ≤ reuseWeight) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      observedWeightedPowerMoments weights key (result.2, log ++ [⟨message, result.1.1⟩]) degree) ≤
      observedWeightedPowerMoments weights key (before, log) degree +
        freshDigestSelectionProbability key message before *
          ((∑ index : Index, weights index * cachePowerArrival degree ((signingSlotsAtIndex
            (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) index).card : ENNReal)) / (Fintype.card Index : ENNReal)) +
        cacheMessageWeight key.parameter (fun _ source => weights source.1 * cachePowerArrival degree ((signingSlotsAtIndex
          (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1).card : ENNReal)) before * reuseWeight := by
  let weight := fun source : FewTimeView => weights source.1 * cachePowerArrival degree ((signingSlotsAtIndex
    (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1).card : ENNReal)
  have heq : (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      observedWeightedPowerMoments weights key (result.2, log ++ [⟨message, result.1.1⟩]) degree) =
      ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        (observedWeightedPowerMoments weights key (before, log) degree + successfulSignerViewWeight weight result) := by
    apply tsum_congr
    intro result
    by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
    · rw [signWithView_weightedPower_eq weights key message before log degree hsigned result hresult]
    · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
  rw [heq]
  simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
  have hsigner := expected_successfulSignerInputWeight_le_allMessage_of_reuseWeight key message before
    (fun _ source => weight source) weight (fun _ _ => le_rfl) reuseWeight hreuse
  simp only [successfulSignerInputWeight_const] at hsigner
  dsimp only [weight] at hsigner
  rw [uniform_view_index_weight_expectation (fun index => weights index * cachePowerArrival degree ((signingSlotsAtIndex
    (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) index).card : ENNReal))] at hsigner
  exact (add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) hsigner).trans_eq (add_assoc _ _ _).symm

theorem expected_signWithView_weightedPower_le_mass_mul (weights : Index → ENNReal) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      observedWeightedPowerMoments weights key (result.2, log ++ [⟨message, result.1.1⟩]) degree) ≤
      observedWeightedPowerMoments weights key (before, log) degree +
        freshDigestSelectionProbability key message before *
          ((∑ index : Index, weights index * cachePowerArrival degree ((signingSlotsAtIndex
            (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) index).card : ENNReal)) / (Fintype.card Index : ENNReal)) +
        cacheMessageWeight key.parameter (fun _ source => weights source.1 * cachePowerArrival degree ((signingSlotsAtIndex
          (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1).card : ENNReal)) before * digestReuseWeight q :=
  expected_signWithView_weightedPower_le_of_reuseWeight weights key message before log degree hsigned
    (digestReuseWeight q) (fun input =>
      probEvent_signWithView_fixedPrehit_le_digestReuseWeight key message before input (fun _ => True) q hq hcache)

theorem expected_signWithView_weightedPower_le (weights : Index → ENNReal) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      observedWeightedPowerMoments weights key (result.2, log ++ [⟨message, result.1.1⟩]) degree) ≤
      observedWeightedPowerMoments weights key (before, log) degree +
        (∑ index : Index, weights index * cachePowerArrival degree ((signingSlotsAtIndex
          (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) index).card : ENNReal)) / (Fintype.card Index : ENNReal) +
        cacheMessageWeight key.parameter (fun _ source => weights source.1 * cachePowerArrival degree ((signingSlotsAtIndex
          (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1).card : ENNReal)) before * digestReuseWeight q :=
  (expected_signWithView_weightedPower_le_mass_mul weights key message before log degree hsigned q hq hcache).trans
    (add_le_add (add_le_add le_rfl
      (mul_le_of_le_one_left' (freshDigestSelectionProbability_le_one key message before))) le_rfl)

end SphincsSecurity.Concrete
