import SphincsSecurity.Proof.ObservedSignerCompletion

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem observedFewTimeCover_append_ineligible (answers : HashInput → Option HashOutput)
    (root : Digest) (log : QueryLog SigningSpec) (entry : SigningEntry) (forgery : Forgery)
    (hineligible : ∀ signature, entry.2 = some signature →
      messageDigestPayload root entry.1 signature.randomness = messageDigestPayload root forgery.message forgery.signature.randomness)
    (hcover : ObservedFewTimeCover answers root (log ++ [entry]) forgery) :
    ObservedFewTimeCover answers root log forgery := by
  obtain ⟨digest, htarget, hadmissible, hcover⟩ := hcover
  refine ⟨digest, htarget, hadmissible, ?_⟩
  intro tree
  obtain ⟨selected, signature, signedDigest, hselected, hresponse, hsignedAdmissible, hsignedDigest, hne, hindex, hleaf⟩ := hcover tree
  rcases List.mem_append.mp hselected with hold | hnew
  · exact ⟨selected, signature, signedDigest, hold, hresponse, hsignedAdmissible, hsignedDigest, hne, hindex, hleaf⟩
  · obtain rfl := List.mem_singleton.mp hnew
    exact (hne (hineligible signature hresponse)).elim

def ObservedSignerCover (key : SecretKey) (message : Message) (log : QueryLog SigningSpec)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : Prop :=
  ∃ forgery, ObservedFewTimeCover (messageAnswers key.parameter result.2) key.root
    (log ++ [⟨message, result.1.1⟩]) forgery

theorem observedSignerCover_queries_or_completion (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter cache key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run cache))
    (hevent : ObservedSignerCover key message log result) :
    CoveredMessageCache key.parameter (fixedSigningViews key.parameter cache key.root log) result.2 ∨
      SignerCompletesObservedTarget key message log result := by
  obtain ⟨forgery, hcover⟩ := hevent
  have hcache := simulateQ_romImpl_cache_le (signWithView key message) cache result hresult
  cases hsignature : result.1.1 with
  | none =>
      rw [hsignature] at hcover
      have hold := observedFewTimeCover_append_ineligible (messageAnswers key.parameter result.2) key.root log
        ⟨message, none⟩ forgery (fun signature h => by simp only [reduceCtorEq] at h) hcover
      exact Or.inl (observedFewTimeCover_coveredMessageCache key.parameter cache result.2 key.root log hcache hsigned forgery hold)
  | some signature =>
      rw [hsignature] at hcover
      have hresult' : ((some signature, result.1.2), result.2) ∈ support
          ((simulateQ romImpl (signWithView key message)).run cache) := by
        have heq : result = ((some signature, result.1.2), result.2) := Prod.ext (Prod.ext hsignature rfl) rfl
        rwa [heq] at hresult
      obtain ⟨output, _, _, hview⟩ := signWithView_successful_cached_output key message cache result.2 signature result.1.2 hresult'
      by_cases hne : messageDigestPayload key.root forgery.message forgery.signature.randomness ≠
          messageDigestPayload key.root message signature.randomness
      · exact Or.inr ⟨signature, hashOutputFewTimeView output, forgery, Prod.ext hsignature hview, hne, hcover⟩
      · have hpayload : messageDigestPayload key.root message signature.randomness =
            messageDigestPayload key.root forgery.message forgery.signature.randomness := (not_ne_iff.mp hne).symm
        have hold := observedFewTimeCover_append_ineligible (messageAnswers key.parameter result.2) key.root log
          ⟨message, some signature⟩ forgery (fun selected hresponse => by
            have heq : signature = selected := Option.some.inj hresponse
            simpa only [← heq] using hpayload) hcover
        exact Or.inl (observedFewTimeCover_coveredMessageCache key.parameter cache result.2 key.root log hcache hsigned forgery hold)

noncomputable def observedSignerCoverCharge (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (log : QueryLog SigningSpec) (q : Nat) : ENNReal :=
  expectedQueryCharge (freshCoverageCharge key.parameter (fixedSigningViews key.parameter cache key.root log))
      (signWithView key message) cache * ((2 ^ 176 : Nat) : ENNReal)⁻¹ +
    (∑ target ∈ cachedAdmissibleMessageInputs key.parameter cache hfinite,
      completionProbability (fixedSigningViews key.parameter cache key.root log target) (cachedFewTimeView cache target)) +
    cachedMessageEntryCountWhere cache key.parameter key.root message
      (CompletesSomeFewTimeTarget (cachedAdmissibleMessageInputs key.parameter cache hfinite)
        (fixedSigningViews key.parameter cache key.root log) (cachedFewTimeView cache)) * digestReuseWeight q

theorem probEvent_observedSignerCover_le_charge (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter cache key.root log)
    (hclean : ¬ CoveredMessageCache key.parameter (fixedSigningViews key.parameter cache key.root log) cache)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    Pr[ObservedSignerCover key message log | (simulateQ romImpl (signWithView key message)).run cache] ≤
      observedSignerCoverCharge key message cache hfinite log q := by
  have hqueries := probEvent_adaptive_coveredMessageCache_le_charge key.parameter
    (fixedSigningViews key.parameter cache key.root log) (signWithView key message) cache hfinite
  rw [if_neg hclean, zero_add] at hqueries
  have hcompletion := probEvent_signerCompletesObservedTarget_le key message cache hfinite log hsigned hclean q hq hcache
  have hbound := (probEvent_mono (fun result hresult hevent =>
    observedSignerCover_queries_or_completion key message cache log hsigned result hresult hevent)).trans
      ((probEvent_or_le _ _ _).trans (add_le_add hqueries hcompletion))
  simpa only [observedSignerCoverCharge, add_assoc] using hbound

end SphincsSecurity.Concrete
