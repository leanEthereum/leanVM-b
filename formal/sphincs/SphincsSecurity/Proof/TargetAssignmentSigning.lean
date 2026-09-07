import SphincsSecurity.Proof.TargetAssignmentReuse

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem futureTargetAssignmentCount_congr {n m : Nat} (before : Fin n → Option FewTimeView)
    (after : Fin m → Option FewTimeView) (remaining : Nat) (target : FewTimeView)
    (hcounts : ∀ tree, targetTreeMatchCount before target tree = targetTreeMatchCount after target tree) :
    futureTargetAssignmentCount before remaining target = futureTargetAssignmentCount after remaining target :=
  le_antisymm (futureTargetAssignmentCount_mono remaining before after target (fun tree => (hcounts tree).le))
    (futureTargetAssignmentCount_mono remaining after before target (fun tree => (hcounts tree).ge))

theorem assignment_eligibleSigningViews_append_none (answers : HashInput → Option HashOutput) (root : Digest)
    (payload : HashInput) (log : QueryLog SigningSpec) (entry : SigningEntry) (target : FewTimeView)
    (hnone : eligibleSigningView? answers root payload entry = none) (remaining : Nat) :
    futureTargetAssignmentCount (eligibleSigningViews answers root payload (log ++ [entry])) remaining target =
      futureTargetAssignmentCount (eligibleSigningViews answers root payload log) remaining target := by
  apply futureTargetAssignmentCount_congr
  intro tree
  change targetTreeMatchCount (fun slot => eligibleSigningView? answers root payload ((log ++ [entry]).get slot)) target tree =
    targetTreeMatchCount (fun slot => eligibleSigningView? answers root payload (log.get slot)) target tree
  simp only [targetTreeMatchCount_log, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hnone, reduceCtorEq,
    false_and, exists_false, if_false, add_zero]

theorem assignment_eligibleSigningViews_append_some (answers : HashInput → Option HashOutput) (root : Digest)
    (payload : HashInput) (log : QueryLog SigningSpec) (entry : SigningEntry) (target source : FewTimeView)
    (hsome : eligibleSigningView? answers root payload entry = some source) (remaining : Nat) :
    futureTargetAssignmentCount (eligibleSigningViews answers root payload (log ++ [entry])) remaining target =
      futureTargetAssignmentCount (insertFewTimeView (eligibleSigningViews answers root payload log) source) remaining target := by
  apply futureTargetAssignmentCount_congr
  intro tree
  rw [targetTreeMatchCount_insert]
  change targetTreeMatchCount (fun slot => eligibleSigningView? answers root payload ((log ++ [entry]).get slot)) target tree =
    targetTreeMatchCount (fun slot => eligibleSigningView? answers root payload (log.get slot)) target tree + sourceTreeMatch target source tree
  simp only [targetTreeMatchCount_log, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hsome, Option.some.injEq,
    exists_eq_left', sourceTreeMatch, add_zero]

noncomputable def observedTargetAssignmentCount (remaining : Nat) (parameter : PublicParameter)
    (root : Digest) (payload : HashInput) (target : FewTimeView)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) : ENNReal :=
  futureTargetAssignmentCount (eligibleSigningViews (messageAnswers parameter cache) root payload log) remaining target

theorem observedTargetAssignmentCount_cache_stable (remaining : Nat) (parameter : PublicParameter)
    (root : Digest) (payload : HashInput) (target : FewTimeView)
    (before after : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached parameter before root log) :
    observedTargetAssignmentCount remaining parameter root payload target after log =
      observedTargetAssignmentCount remaining parameter root payload target before log := by
  have hstable : eligibleSigningViews (messageAnswers parameter after) root payload log =
      eligibleSigningViews (messageAnswers parameter before) root payload log := by
    funext slot
    exact eligibleSigningView?_cache_stable parameter root before after hcache payload (log.get slot)
      (hsigned _ (List.get_mem _ _))
  simp only [observedTargetAssignmentCount, hstable]

theorem signWithView_observedTargetAssignmentCount_le (remaining : Nat) (key : SecretKey)
    (message : Message) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    observedTargetAssignmentCount remaining key.parameter key.root payload target result.2
      (log ++ [⟨message, result.1.1⟩]) ≤
      observedTargetAssignmentCount remaining key.parameter key.root payload target before log +
        successfulSignerViewWeight
          (futureTargetAssignmentIncrement
            (eligibleSigningViews (messageAnswers key.parameter before) key.root payload log) remaining target) result := by
  have hcache := simulateQ_romImpl_cache_le (signWithView key message) before result hresult
  have hstable : eligibleSigningViews (messageAnswers key.parameter result.2) key.root payload log =
      eligibleSigningViews (messageAnswers key.parameter before) key.root payload log := by
    funext slot
    exact eligibleSigningView?_cache_stable key.parameter key.root before result.2 hcache payload (log.get slot)
      (hsigned _ (List.get_mem _ _))
  unfold observedTargetAssignmentCount
  cases hresponse : result.1.1 with
  | none =>
      rw [assignment_eligibleSigningViews_append_none _ _ _ _ _ _ (by simp [eligibleSigningView?]) remaining, hstable]
      simp only [successfulSignerViewWeight, hresponse, add_zero, le_refl]
  | some signature =>
      have hresult' : ((some signature, result.1.2), result.2) ∈ support
          ((simulateQ romImpl (signWithView key message)).run before) := by
        have heq : result = ((some signature, result.1.2), result.2) := Prod.ext (Prod.ext hresponse rfl) rfl
        rwa [heq] at hresult
      obtain ⟨output, houtput, _, hview⟩ := signWithView_successful_cached_output key message before result.2 signature result.1.2 hresult'
      simp only [successfulSignerViewWeight, hresponse, hview]
      by_cases hsame : messageDigestPayload key.root message signature.randomness = payload
      · rw [assignment_eligibleSigningViews_append_none _ _ _ _ _ _ (by simp [eligibleSigningView?, hsame]) remaining, hstable]
        exact le_self_add
      · have hsome : eligibleSigningView? (messageAnswers key.parameter result.2) key.root payload ⟨message, some signature⟩ =
            some (hashOutputFewTimeView output) := by
          simp [eligibleSigningView?, observedSigningView?, messageAnswers, hsame, houtput]
        rw [assignment_eligibleSigningViews_append_some _ _ _ _ _ _ _ hsome remaining, hstable,
          ← futureTargetAssignmentCount_add_increment]

theorem signWithView_observedTargetAssignmentCount_le_input (remaining : Nat) (key : SecretKey)
    (message : Message) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    observedTargetAssignmentCount remaining key.parameter key.root payload target result.2
      (log ++ [⟨message, result.1.1⟩]) ≤
      observedTargetAssignmentCount remaining key.parameter key.root payload target before log +
        successfulSignerInputWeight key message (targetAssignmentInputIncrement remaining key before log payload target) result := by
  have hcoarse := signWithView_observedTargetAssignmentCount_le remaining key message before log payload target hsigned result hresult
  cases hresponse : result.1.1 with
  | none => simpa only [successfulSignerInputWeight, successfulSignerViewWeight, hresponse] using hcoarse
  | some signature =>
      by_cases hsame : messageDigestPayload key.root message signature.randomness = payload
      · have heq : observedTargetAssignmentCount remaining key.parameter key.root payload target result.2
            (log ++ [⟨message, some signature⟩]) =
            observedTargetAssignmentCount remaining key.parameter key.root payload target before log := by
          unfold observedTargetAssignmentCount
          rw [assignment_eligibleSigningViews_append_none _ _ _ _ _ _ (by simp [eligibleSigningView?, hsame]) remaining]
          exact observedTargetAssignmentCount_cache_stable remaining key.parameter key.root payload target before result.2 log
            (simulateQ_romImpl_cache_le (signWithView key message) before result hresult) hsigned
        rw [heq]
        exact le_self_add
      · have hinput : tweakableHashInput key.parameter .message (messageDigestPayload key.root message signature.randomness) ≠
            tweakableHashInput key.parameter .message payload := by
          intro heq
          exact hsame (tweakableHashInput_injective key.parameter (by trivial) (by trivial) heq).2
        cases hview : result.1.2 <;>
          simpa only [successfulSignerInputWeight, successfulSignerViewWeight, hresponse, hview,
            targetAssignmentInputIncrement, if_neg hinput] using hcoarse

noncomputable def targetAssignmentInputReuseCharge (remaining : Nat) (key : SecretKey)
    (message : Message) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView) (q : Nat) : ENNReal :=
  (∑' input, cachedSignerInputWeight key message before (targetAssignmentInputIncrement remaining key before log payload target) input) *
    digestReuseWeight q

theorem cachedSignerInputWeight_assignment_target_self (remaining : Nat) (key : SecretKey)
    (message : Message) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView) :
    cachedSignerInputWeight key message before (targetAssignmentInputIncrement remaining key before log payload target)
      (tweakableHashInput key.parameter .message payload) = 0 := by
  unfold cachedSignerInputWeight
  cases before (tweakableHashInput key.parameter .message payload) <;>
    simp only [targetAssignmentInputIncrement_self, ite_self]

theorem expected_signWithView_observedTargetAssignmentCount_le_inputReuse (remaining : Nat) (key : SecretKey)
    (message : Message) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      observedTargetAssignmentCount remaining key.parameter key.root payload target result.2
        (log ++ [⟨message, result.1.1⟩])) ≤
      observedTargetAssignmentCount (remaining + 1) key.parameter key.root payload target before log +
        targetAssignmentInputReuseCharge remaining key message before log payload target q := by
  let views := eligibleSigningViews (messageAnswers key.parameter before) key.root payload log
  let weight := targetAssignmentInputIncrement remaining key before log payload target
  have hweight (input : HashInput) (source : FewTimeView) : weight input source ≤ futureTargetAssignmentIncrement views remaining target source := by
    unfold weight targetAssignmentInputIncrement
    split_ifs
    · exact bot_le
    · exact le_rfl
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        (futureTargetAssignmentCount views remaining target + successfulSignerInputWeight key message weight result) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
      · exact mul_le_mul' le_rfl (signWithView_observedTargetAssignmentCount_le_input remaining key message before log payload target hsigned result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ ≤ futureTargetAssignmentCount views remaining target +
        (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
          successfulSignerInputWeight key message weight result) := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl
    _ ≤ futureTargetAssignmentCount views remaining target +
        ((∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
          futureTargetAssignmentIncrement views remaining target source) +
          targetAssignmentInputReuseCharge remaining key message before log payload target q) :=
      add_le_add le_rfl (expected_successfulSignerInputWeight_le key message before weight _ hweight q hq hcache)
    _ = _ := by
      rw [← add_assoc, expected_source_futureTargetAssignmentIncrement]
      rfl

end SphincsSecurity.Concrete
