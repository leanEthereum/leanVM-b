import SphincsSecurity.Proof.FewTimeBinomialOccupancy

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem observed_binomialOccupancy_append_none (answers : HashInput → Option HashOutput) (root : Digest)
    (log : QueryLog SigningSpec) (entry : SigningEntry) (degree : Nat)
    (hnone : observedSigningView? answers root entry = none) :
    binomialOccupancyMoment (observedOptionalSigningViews answers root (log ++ [entry])) degree =
      binomialOccupancyMoment (observedOptionalSigningViews answers root log) degree := by
  unfold binomialOccupancyMoment observedOptionalSigningViews
  simp only [signingSlotsAtIndex_log_append_card, hnone, reduceCtorEq, false_and, exists_false, if_false, add_zero]

theorem observed_binomialOccupancy_append_some (answers : HashInput → Option HashOutput) (root : Digest)
    (log : QueryLog SigningSpec) (entry : SigningEntry) (source : FewTimeView) (degree : Nat)
    (hsome : observedSigningView? answers root entry = some source) :
    binomialOccupancyMoment (observedOptionalSigningViews answers root (log ++ [entry])) (degree + 1) =
      binomialOccupancyMoment (observedOptionalSigningViews answers root log) (degree + 1) +
        (signingSlotsAtIndex (observedOptionalSigningViews answers root log) source.1).card.choose degree := by
  rw [← binomialOccupancyMoment_insert]
  unfold binomialOccupancyMoment observedOptionalSigningViews
  simp only [signingSlotsAtIndex_log_append_card, signingSlotsAtIndex_insert_card, hsome, Option.some.injEq, exists_eq_left']

theorem signWithView_binomialOccupancy_eq (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    (binomialOccupancyMoment (observedOptionalSigningViews (messageAnswers key.parameter result.2) key.root
      (log ++ [⟨message, result.1.1⟩])) (degree + 1) : ENNReal) =
        (binomialOccupancyMoment (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) (degree + 1) : ENNReal) +
          successfulSignerViewWeight (fun source =>
            ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1).card.choose degree : ENNReal)) result := by
  have hcache := simulateQ_romImpl_cache_le (signWithView key message) before result hresult
  have hstable := observedOptionalSigningViews_cache_stable key.parameter key.root before result.2 log hcache hsigned
  cases hresponse : result.1.1 with
  | none =>
      rw [observed_binomialOccupancy_append_none _ _ _ _ _ (by simp [observedSigningView?]), hstable]
      simp only [successfulSignerViewWeight, hresponse, add_zero]
  | some signature =>
      have hresult' : ((some signature, result.1.2), result.2) ∈ support
          ((simulateQ romImpl (signWithView key message)).run before) := by
        have heq : result = ((some signature, result.1.2), result.2) := Prod.ext (Prod.ext hresponse rfl) rfl
        rwa [heq] at hresult
      obtain ⟨output, houtput, _, hview⟩ := signWithView_successful_cached_output key message before result.2 signature result.1.2 hresult'
      have hsource : observedSigningView? (messageAnswers key.parameter result.2) key.root ⟨message, some signature⟩ = some (hashOutputFewTimeView output) := by
        simp [observedSigningView?, messageAnswers, houtput]
      rw [observed_binomialOccupancy_append_some _ _ _ _ _ _ hsource, hstable, Nat.cast_add]
      simp only [successfulSignerViewWeight, hresponse, hview]

theorem expected_signWithView_binomialOccupancy_le (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      (binomialOccupancyMoment (observedOptionalSigningViews (messageAnswers key.parameter result.2) key.root
        (log ++ [⟨message, result.1.1⟩])) (degree + 1) : ENNReal)) ≤
      (binomialOccupancyMoment (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) (degree + 1) : ENNReal) +
        (binomialOccupancyMoment (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) degree : ENNReal) /
          (Fintype.card Index : ENNReal) +
        (∑' source, cachedMessageEntryCountWhere before key.parameter key.root message (· = source) *
          ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1).card.choose degree : ENNReal)) * digestReuseWeight q := by
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
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, expected_successfulSignerViewWeight_eq]
  apply (add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl).trans
  exact (add_le_add le_rfl (expected_successfulSigner_choose_le views degree key message before q hq hcache)).trans_eq (add_assoc _ _ _).symm

noncomputable def observedLogBinomialOccupancy (key : SecretKey) (degree : Nat) (state : CoverLogState) : ENNReal :=
  binomialOccupancyMoment (observedOptionalSigningViews (messageAnswers key.parameter state.1) key.root state.2) degree

noncomputable def binomialOccupancyStepCharge (key : SecretKey) (q degree : Nat) (state : CoverLogState) :
    (OracleWorld + SigningSpec).Domain → ENNReal
  | .inl _ => 0
  | .inr message =>
      let views := observedOptionalSigningViews (messageAnswers key.parameter state.1) key.root state.2
      (binomialOccupancyMoment views degree : ENNReal) / (Fintype.card Index : ENNReal) +
        (∑' source, cachedMessageEntryCountWhere state.1 key.parameter key.root message (· = source) *
          ((signingSlotsAtIndex views source.1).card.choose degree : ENNReal)) * digestReuseWeight q

theorem expected_logTraced_binomialOccupancy_le (key : SecretKey) (degree q : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (input : (OracleWorld + SigningSpec).Domain) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * observedLogBinomialOccupancy key (degree + 1) result.2) ≤
      observedLogBinomialOccupancy key (degree + 1) state + binomialOccupancyStepCharge key q degree state input := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  cases input with
  | inl world =>
      simp only [signingLogFragment, List.append_nil, binomialOccupancyStepCharge, add_zero]
      have heq : (∑' result, Pr[= result | (unloggedMappedAdversaryImpl key (.inl world)).run state.1] *
          observedLogBinomialOccupancy key (degree + 1) (result.2, state.2)) =
          ∑' result, Pr[= result | (unloggedMappedAdversaryImpl key (.inl world)).run state.1] * observedLogBinomialOccupancy key (degree + 1) state := by
        apply tsum_congr
        intro result
        by_cases hresult : result ∈ support ((unloggedMappedAdversaryImpl key (.inl world)).run state.1)
        · have hstable := observedOptionalSigningViews_cache_stable key.parameter key.root state.1 result.2 state.2
            (unloggedMappedAdversaryImpl_cache_le key (.inl world) state.1 result hresult) hsigned
          simp only [observedLogBinomialOccupancy, hstable]
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
      rw [heq, ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
  | inr message =>
      have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
          (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
        (simulateQ_signWithView_fst_run key message state.1).symm
      rw [hrun, tsum_probOutput_map_mul]
      simpa only [observedLogBinomialOccupancy, binomialOccupancyStepCharge, signingLogFragment, add_assoc] using
        expected_signWithView_binomialOccupancy_le key message state.1 state.2 degree hsigned q hq hcache

end SphincsSecurity.Concrete
