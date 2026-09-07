import SphincsSecurity.Proof.CachedSigningViews

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def SignerCacheCover (key : SecretKey) (message : Message) (log : QueryLog SigningSpec)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : Prop :=
  SigningCacheCovered key.parameter key.root result.2 (log ++ [⟨message, result.1.1⟩])

theorem signerCacheCover_queries_or_completion (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter cache key.root log)
    (hclean : ¬ SigningCacheCovered key.parameter key.root cache log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run cache))
    (hevent : SignerCacheCover key message log result) :
    CoveredMessageCache key.parameter (fixedSigningViews key.parameter cache key.root log) result.2 ∨
      SuccessfulSignerViewSatisfies (CompletesSomeFewTimeTarget (cachedAdmissibleMessageInputs key.parameter cache hfinite)
        (fixedSigningViews key.parameter cache key.root log) (cachedFewTimeView cache)) result := by
  obtain ⟨input, targetOutput, ⟨payload, rfl⟩, htarget, hadmissible, hcover⟩ := hevent
  rw [fixedSigningViews, payloadOf_tweakableHashInput] at hcover
  have hcache := simulateQ_romImpl_cache_le (signWithView key message) cache result hresult
  have hstable : eligibleSigningViews (messageAnswers key.parameter result.2) key.root payload log =
      eligibleSigningViews (messageAnswers key.parameter cache) key.root payload log := by
    simpa only [fixedSigningViews, payloadOf_tweakableHashInput] using congrFun
      (fixedSigningViews_cache_stable key.parameter key.root cache result.2 log hcache hsigned)
      (tweakableHashInput key.parameter .message payload)
  have hold (h : CoveredFewTimeView (eligibleSigningViews (messageAnswers key.parameter result.2) key.root payload log)
      (hashOutputFewTimeView targetOutput)) :
      CoveredMessageCache key.parameter (fixedSigningViews key.parameter cache key.root log) result.2 := by
    rw [hstable] at h
    refine ⟨tweakableHashInput key.parameter .message payload, targetOutput, ⟨_, rfl⟩, htarget, hadmissible, ?_⟩
    simpa only [fixedSigningViews, payloadOf_tweakableHashInput] using h
  cases hsignature : result.1.1 with
  | none =>
      rw [hsignature] at hcover
      exact Or.inl (hold (covered_eligibleSigningViews_append_none _ _ _ _ _ _
        (by simp [eligibleSigningView?]) hcover))
  | some signature =>
      rw [hsignature] at hcover
      have hresult' : ((some signature, result.1.2), result.2) ∈ support
          ((simulateQ romImpl (signWithView key message)).run cache) := by
        have heq : result = ((some signature, result.1.2), result.2) := Prod.ext (Prod.ext hsignature rfl) rfl
        rwa [heq] at hresult
      obtain ⟨sourceOutput, hsource, _, hview⟩ := signWithView_successful_cached_output key message cache result.2 signature result.1.2 hresult'
      by_cases hsame : messageDigestPayload key.root message signature.randomness = payload
      · exact Or.inl (hold (covered_eligibleSigningViews_append_none _ _ _ _ _ _
          (by simp [eligibleSigningView?, hsame]) hcover))
      · have hsome : eligibleSigningView? (messageAnswers key.parameter result.2) key.root payload ⟨message, some signature⟩ =
            some (hashOutputFewTimeView sourceOutput) := by
          simp [eligibleSigningView?, observedSigningView?, messageAnswers, hsame, hsource]
        have hcovered := covered_eligibleSigningViews_append_some _ _ _ _ _ _ _ hsome hcover
        rw [hstable] at hcovered
        have hprior := signWithView_admissible_message_cached_before key message cache result.2 signature result.1.2 hresult'
          payload targetOutput (Ne.symm hsame) htarget hadmissible
        let targetInput := tweakableHashInput key.parameter .message payload
        have htargetView : cachedFewTimeView cache targetInput = hashOutputFewTimeView targetOutput := by
          simp only [cachedFewTimeView, targetInput, hprior, Option.getD_some]
        have hmember : targetInput ∈ cachedAdmissibleMessageInputs key.parameter cache hfinite := by
          refine Finset.mem_filter.mpr ⟨hfinite.mem_toFinset.mpr ?_, ⟨_, rfl⟩, targetOutput, hprior, hadmissible⟩
          exact Option.ne_none_iff_exists'.mpr ⟨targetOutput, hprior⟩
        refine Or.inr ⟨signature, hashOutputFewTimeView sourceOutput, Prod.ext hsignature hview, targetInput, hmember, ?_, ?_⟩
        · rw [htargetView]
          intro hcovered
          exact hclean ⟨targetInput, targetOutput, ⟨_, rfl⟩, hprior, hadmissible, hcovered⟩
        · rw [htargetView]
          simpa only [fixedSigningViews, targetInput, payloadOf_tweakableHashInput] using hcovered

theorem probEvent_signerCacheCover_le_charge (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter cache key.root log)
    (hclean : ¬ SigningCacheCovered key.parameter key.root cache log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    Pr[SignerCacheCover key message log | (simulateQ romImpl (signWithView key message)).run cache] ≤
      observedSignerCoverCharge key message cache hfinite log q := by
  have hqueries := probEvent_adaptive_coveredMessageCache_le_charge key.parameter
    (fixedSigningViews key.parameter cache key.root log) (signWithView key message) cache hfinite
  change ¬ CoveredMessageCache key.parameter (fixedSigningViews key.parameter cache key.root log) cache at hclean
  rw [if_neg hclean, zero_add] at hqueries
  have hcompletion := probEvent_signer_completesSomeFewTimeTarget_le (cachedAdmissibleMessageInputs key.parameter cache hfinite)
    (fixedSigningViews key.parameter cache key.root log) (cachedFewTimeView cache) key message cache q hq hcache
  have hbound := (probEvent_mono (fun result hresult hevent =>
    signerCacheCover_queries_or_completion key message cache hfinite log hsigned hclean result hresult hevent)).trans
      ((probEvent_or_le _ _ _).trans (add_le_add hqueries hcompletion))
  simpa only [observedSignerCoverCharge, add_assoc] using hbound

end SphincsSecurity.Concrete
