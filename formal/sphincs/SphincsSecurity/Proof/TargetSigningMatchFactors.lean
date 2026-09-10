import SphincsSecurity.Proof.NormalizedTargetCacheQuery
import SphincsSecurity.Proof.SingleMessageCacheGrowth

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def normalizedTargetLogMatch (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (tree : FtsTree) : ENNReal :=
  (Fintype.card FtsLeaf : ENNReal) *
    (targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter cache) key.root payload log) target tree : ENNReal)

noncomputable def normalizedTargetLogProduct (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset FtsTree) : ENNReal :=
  ∏ tree ∈ required, normalizedTargetLogMatch key cache log payload target tree

theorem targetTreeMatchCount_log_append_singleton (log : List α) (entry : α) (view : α → Option FewTimeView)
    (target : FewTimeView) (tree : FtsTree) :
    targetTreeMatchCount (fun slot => view ((log ++ [entry]).get slot)) target tree =
      targetTreeMatchCount (fun slot => view (log.get slot)) target tree +
        if ∃ source, view entry = some source ∧ source.1 = target.1 ∧ source.2 tree = target.2 tree then 1 else 0 := by
  simp only [targetTreeMatchCount_log_append, targetTreeMatchCount_log, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

theorem normalizedSourceSubsetMatch_singleton (target source : FewTimeView) (tree : FtsTree) :
    normalizedSourceSubsetMatch target source {tree} = (Fintype.card FtsLeaf : ENNReal) * (sourceTreeMatch target source tree : ENNReal) := by
  simp only [normalizedSourceSubsetMatch, Finset.card_singleton, pow_one, sourceSubsetMatch, Finset.prod_singleton]

theorem eligibleSigningViews_cache_stable (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (hcache : before ≤ after)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    eligibleSigningViews (messageAnswers key.parameter after) key.root payload log =
      eligibleSigningViews (messageAnswers key.parameter before) key.root payload log := by
  funext slot
  exact eligibleSigningView?_cache_stable key.parameter key.root before after hcache payload (log.get slot)
    (hsigned _ (List.get_mem _ _))

theorem signWithView_eligibleView_of_view (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (payload : HashInput) (source : FewTimeView) (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) (hview : result.1.2 = some source) :
    eligibleSigningView? (messageAnswers key.parameter result.2) key.root payload ⟨message, result.1.1⟩ = none ∨
      eligibleSigningView? (messageAnswers key.parameter result.2) key.root payload ⟨message, result.1.1⟩ = some source := by
  cases hresponse : result.1.1 with
  | none => exact Or.inl (by simp [eligibleSigningView?])
  | some signature =>
      have hresult' : ((some signature, result.1.2), result.2) ∈ support
          ((simulateQ romImpl (signWithView key message)).run before) := by
        have heq : result = ((some signature, result.1.2), result.2) := Prod.ext (Prod.ext hresponse rfl) rfl
        rwa [heq] at hresult
      obtain ⟨output, houtput, _, houtview⟩ := signWithView_successful_cached_output key message before result.2 signature result.1.2 hresult'
      have heq : hashOutputFewTimeView output = source := Option.some.inj (houtview.symm.trans hview)
      by_cases hsame : messageDigestPayload key.root message signature.randomness = payload
      · exact Or.inl (by simp [eligibleSigningView?, hsame])
      · exact Or.inr (by simp [eligibleSigningView?, observedSigningView?, messageAnswers, hsame, houtput, heq])

theorem normalizedTargetLogMatch_le_of_eligibleView (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (entry : SigningEntry) (payload : HashInput) (target source : FewTimeView) (tree : FtsTree)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hentry : eligibleSigningView? (messageAnswers key.parameter after) key.root payload entry = none ∨
      eligibleSigningView? (messageAnswers key.parameter after) key.root payload entry = some source) :
    normalizedTargetLogMatch key after (log ++ [entry]) payload target tree ≤
      normalizedTargetLogMatch key before log payload target tree + normalizedSourceSubsetMatch target source {tree} := by
  have hstable := eligibleSigningViews_cache_stable key before after log payload hcache hsigned
  have hstep := targetTreeMatchCount_log_append_singleton log entry
    (eligibleSigningView? (messageAnswers key.parameter after) key.root payload) target tree
  change targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter after) key.root payload (log ++ [entry])) target tree =
    targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter after) key.root payload log) target tree + _ at hstep
  rw [hstable] at hstep
  rw [normalizedTargetLogMatch, hstep, Nat.cast_add, mul_add, normalizedSourceSubsetMatch_singleton]
  apply add_le_add le_rfl
  apply mul_le_mul' le_rfl
  apply Nat.cast_le.mpr
  rcases hentry with hnone | hsome
  · simp only [hnone, reduceCtorEq, false_and, exists_false, if_false, Nat.zero_le]
  · simp only [hsome, Option.some.injEq, exists_eq_left', sourceTreeMatch, le_refl]

theorem signWithView_normalizedTargetLogMatch_le (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target source : FewTimeView) (tree : FtsTree)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) (hview : result.1.2 = some source) :
    normalizedTargetLogMatch key result.2 (log ++ [⟨message, result.1.1⟩]) payload target tree ≤
      normalizedTargetLogMatch key before log payload target tree + normalizedSourceSubsetMatch target source {tree} := by
  exact normalizedTargetLogMatch_le_of_eligibleView key before result.2 log ⟨message, result.1.1⟩ payload target source tree
    (simulateQ_romImpl_cache_le (signWithView key message) before result hresult) hsigned
    (signWithView_eligibleView_of_view key message before payload source result hresult hview)

theorem signWithView_normalizedCachedTargetSubsetMatch_of_new (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (signature : Option Signature) (view : Option FewTimeView)
    (hresult : ((signature, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before))
    (targetInput payload : HashInput) (target : FewTimeView) (required : Finset FtsTree) (output : HashOutput)
    (hfresh : before (tweakableHashInput key.parameter .message payload) = none)
    (hafter : after (tweakableHashInput key.parameter .message payload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) :
    normalizedCachedTargetSubsetMatch key.parameter after targetInput target required =
      normalizedCachedTargetSubsetMatch key.parameter before targetInput target required +
        if tweakableHashInput key.parameter .message payload = targetInput then 0 else normalizedSourceSubsetMatch target (hashOutputFewTimeView output) required := by
  simp only [normalizedCachedTargetSubsetMatch_eq_weight]
  exact signWithView_cacheMessageWeight_of_new key message before after signature view hresult _ payload output hfresh hafter hadmissible

theorem normalizedCachedTargetSubsetMatch_mono (parameter : PublicParameter) (before after : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset FtsTree) (hcache : before ≤ after) :
    normalizedCachedTargetSubsetMatch parameter before targetInput target required ≤
      normalizedCachedTargetSubsetMatch parameter after targetInput target required := by
  simp only [normalizedCachedTargetSubsetMatch_eq_weight]
  rw [cacheMessageWeight_of_le parameter _ before after hcache]
  exact le_self_add

end SphincsSecurity.Concrete
