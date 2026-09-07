import SphincsSecurity.Proof.AllMessageReuse

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

private theorem observed_occupancyCompletion_append_none (answers : HashInput → Option HashOutput) (root : Digest)
    (log : QueryLog SigningSpec) (entry : SigningEntry) (remaining : Nat)
    (hnone : observedSigningView? answers root entry = none) :
    coverageOccupancyCompletion (observedOptionalSigningViews answers root (log ++ [entry])) remaining =
      coverageOccupancyCompletion (observedOptionalSigningViews answers root log) remaining := by
  have hmoments : (fun degree => (binomialOccupancyMoment (observedOptionalSigningViews answers root (log ++ [entry])) degree : ENNReal)) =
      (fun degree => (binomialOccupancyMoment (observedOptionalSigningViews answers root log) degree : ENNReal)) := by
    funext degree
    exact congrArg (fun value : Nat => (value : ENNReal)) (observed_binomialOccupancy_append_none answers root log entry degree hnone)
  simp only [coverageOccupancyCompletion, hmoments]

private theorem observed_occupancyCompletion_append_some (answers : HashInput → Option HashOutput) (root : Digest)
    (log : QueryLog SigningSpec) (entry : SigningEntry) (remaining : Nat) (source : FewTimeView)
    (hsome : observedSigningView? answers root entry = some source) :
    coverageOccupancyCompletion (observedOptionalSigningViews answers root (log ++ [entry])) remaining =
      coverageOccupancyCompletion (insertFewTimeView (observedOptionalSigningViews answers root log) source) remaining := by
  have hmoments : (fun degree => (binomialOccupancyMoment (observedOptionalSigningViews answers root (log ++ [entry])) degree : ENNReal)) =
      (fun degree => (binomialOccupancyMoment (insertFewTimeView (observedOptionalSigningViews answers root log) source) degree : ENNReal)) := by
    funext degree
    apply congrArg (fun value : Nat => (value : ENNReal))
    cases degree with
    | zero => simp only [binomialOccupancyMoment_zero]
    | succ degree => rw [observed_binomialOccupancy_append_some answers root log entry source degree hsome, binomialOccupancyMoment_insert]
  simp only [coverageOccupancyCompletion, hmoments]

theorem signWithView_occupancyCompletion_eq (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    coverageOccupancyCompletion (observedOptionalSigningViews (messageAnswers key.parameter result.2) key.root
      (log ++ [⟨message, result.1.1⟩])) remaining =
      coverageOccupancyCompletion (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) remaining +
        successfulSignerInputWeight key message (fun _ source => coverageOccupancyCompletionIncrement
          (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) remaining source) result := by
  have hstable := observedOptionalSigningViews_cache_stable key.parameter key.root before result.2 log
    (simulateQ_romImpl_cache_le (signWithView key message) before result hresult) hsigned
  cases hresponse : result.1.1 with
  | none =>
      rw [observed_occupancyCompletion_append_none _ _ _ _ _ (by simp [observedSigningView?]), hstable]
      simp only [successfulSignerInputWeight, hresponse, add_zero]
  | some signature =>
      have hresult' : ((some signature, result.1.2), result.2) ∈ support
          ((simulateQ romImpl (signWithView key message)).run before) := by
        have heq : result = ((some signature, result.1.2), result.2) := Prod.ext (Prod.ext hresponse rfl) rfl
        rwa [heq] at hresult
      obtain ⟨output, houtput, _, hview⟩ := signWithView_successful_cached_output key message before result.2 signature result.1.2 hresult'
      have hsource : observedSigningView? (messageAnswers key.parameter result.2) key.root ⟨message, some signature⟩ = some (hashOutputFewTimeView output) := by
        simp [observedSigningView?, messageAnswers, houtput]
      rw [observed_occupancyCompletion_append_some _ _ _ _ _ _ hsource, hstable, ← coverageOccupancyCompletion_add_increment]
      simp only [successfulSignerInputWeight, hresponse, hview]

theorem expected_signWithView_occupancyCompletion_le_allMessage (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      coverageOccupancyCompletion (observedOptionalSigningViews (messageAnswers key.parameter result.2) key.root
        (log ++ [⟨message, result.1.1⟩])) remaining) ≤
      coverageOccupancyCompletion (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) (remaining + 1) +
        allMessageOccupancyReuseCharge remaining key before log q := by
  let views := observedOptionalSigningViews (messageAnswers key.parameter before) key.root log
  let weight := fun (_ : HashInput) source => coverageOccupancyCompletionIncrement views remaining source
  calc
    _ = ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        (coverageOccupancyCompletion views remaining + successfulSignerInputWeight key message weight result) := by
      apply tsum_congr
      intro result
      by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
      · rw [signWithView_occupancyCompletion_eq remaining key message before log hsigned result hresult]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ ≤ coverageOccupancyCompletion views remaining +
        (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] * successfulSignerInputWeight key message weight result) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl
    _ ≤ coverageOccupancyCompletion views remaining +
        ((∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * coverageOccupancyCompletionIncrement views remaining source) +
          allMessageOccupancyReuseCharge remaining key before log q) :=
      add_le_add le_rfl (expected_successfulSignerInputWeight_le_allMessage key message before weight _ (fun _ _ => le_rfl) q hq hcache)
    _ = _ := by rw [← add_assoc, expected_coverageOccupancyCompletionIncrement]

theorem expected_logTraced_sign_occupancyCompletion_le_allMessage (remaining : Nat) (key : SecretKey) (q : Nat)
    (hq : q ≤ 2 ^ 127) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      observedLogOccupancyCompletion remaining key result.2) ≤
      observedLogOccupancyCompletion (remaining + 1) key state + allMessageOccupancyReuseCharge remaining key state.1 state.2 q := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
      (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
    (simulateQ_signWithView_fst_run key message state.1).symm
  rw [hrun, tsum_probOutput_map_mul]
  exact expected_signWithView_occupancyCompletion_le_allMessage remaining key message state.1 state.2 hsigned q hq hcache

end SphincsSecurity.Concrete
