import SphincsSecurity.Proof.ObservedAdaptiveCoverBound
import SphincsSecurity.Proof.FewTimeConditionalSignerCompletion
import SphincsSecurity.Proof.SignerAdmissibleMessage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cachedAdmissibleMessageInputs (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) : Finset HashInput :=
  hfinite.toFinset.filter (fun input => MessageHashInput parameter input ∧
    ∃ output, cache input = some output ∧ Admissible (truncateMessageDigest output))

def cachedFewTimeView (cache : QueryCache HashSpec) (input : HashInput) : FewTimeView :=
  hashOutputFewTimeView ((cache input).getD default)

theorem observedFewTimeCover_append_insertedView (parameter : PublicParameter)
    (before after : QueryCache HashSpec) (root : Digest) (log : QueryLog SigningSpec)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached parameter before root log)
    (message : Message) (signature : Signature) (sourceOutput : HashOutput)
    (hsource : after (tweakableHashInput parameter .message (messageDigestPayload root message signature.randomness)) = some sourceOutput)
    (forgery : Forgery)
    (hcover : ObservedFewTimeCover (messageAnswers parameter after) root (log ++ [⟨message, some signature⟩]) forgery) :
    ∃ targetOutput, after (tweakableHashInput parameter .message
        (messageDigestPayload root forgery.message forgery.signature.randomness)) = some targetOutput ∧
      Admissible (truncateMessageDigest targetOutput) ∧
      CoveredFewTimeView (insertFewTimeView (fixedSigningViews parameter before root log
        (tweakableHashInput parameter .message (messageDigestPayload root forgery.message forgery.signature.randomness)))
        (hashOutputFewTimeView sourceOutput)) (hashOutputFewTimeView targetOutput) := by
  obtain ⟨digest, ⟨answer, hanswer, hdigest⟩, hadmissible, hcover⟩ := hcover
  have hdigest' : digest = truncateMessageDigest answer := hdigest.symm
  rw [hdigest'] at hadmissible hcover
  refine ⟨answer, hanswer, hadmissible, ?_⟩
  rw [fixedSigningViews, payloadOf_tweakableHashInput]
  intro tree
  obtain ⟨entry, signedSignature, signedDigest, hentry, hresponse, _, hsignedDigest, hne, hindex, hleaf⟩ := hcover tree
  obtain ⟨signedAnswer, hsignedAnswer, htruncate⟩ := hsignedDigest
  rcases List.mem_append.mp hentry with hold | hnew
  · obtain ⟨priorAnswer, hprior⟩ := Option.ne_none_iff_exists'.mp (hsigned entry hold signedSignature hresponse)
    have hafter : messageAnswers parameter after (messageDigestPayload root entry.1 signedSignature.randomness) = some priorAnswer := hcache hprior
    have heq : priorAnswer = signedAnswer := Option.some.inj (hafter.symm.trans hsignedAnswer)
    have hpriorDigest : ObservedMessageDigest (messageAnswers parameter before) root entry.1 signedSignature.randomness signedDigest :=
      ⟨priorAnswer, hprior, heq ▸ htruncate⟩
    have hview := eligibleSigningView?_eq_some hresponse hpriorDigest hne
    obtain ⟨slot, hslot⟩ := List.mem_iff_get.mp hold
    refine ⟨slot.succ, fewTimeTargetView (digestIndex signedDigest) (digestLeaves signedDigest), ?_, hindex, hleaf⟩
    simpa only [insertFewTimeView, Fin.cons_succ, eligibleSigningViews, hslot] using hview
  · obtain rfl := List.mem_singleton.mp hnew
    have hsignature : signature = signedSignature := Option.some.inj hresponse
    have hsource' : after (tweakableHashInput parameter .message
        (messageDigestPayload root message signedSignature.randomness)) = some sourceOutput := by
      rwa [← hsignature]
    have houtput : sourceOutput = signedAnswer := Option.some.inj (hsource'.symm.trans hsignedAnswer)
    refine ⟨0, hashOutputFewTimeView sourceOutput, rfl, ?_, ?_⟩
    · change digestIndex (truncateMessageDigest sourceOutput) = digestIndex (truncateMessageDigest answer)
      rw [houtput, htruncate]
      exact hindex
    · change digestLeaves (truncateMessageDigest sourceOutput) (ftsIndexOf tree) = digestLeaves (truncateMessageDigest answer) (ftsIndexOf tree)
      rw [houtput, htruncate]
      exact hleaf

def SignerCompletesObservedTarget (key : SecretKey) (message : Message) (log : QueryLog SigningSpec)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : Prop :=
  ∃ signature view forgery, result.1 = (some signature, some view) ∧
    messageDigestPayload key.root forgery.message forgery.signature.randomness ≠
      messageDigestPayload key.root message signature.randomness ∧
    ObservedFewTimeCover (messageAnswers key.parameter result.2) key.root (log ++ [⟨message, some signature⟩]) forgery

theorem signerCompletesObservedTarget_implies_completion (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter cache key.root log)
    (hclean : ¬ CoveredMessageCache key.parameter (fixedSigningViews key.parameter cache key.root log) cache)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run cache))
    (hevent : SignerCompletesObservedTarget key message log result) :
    SuccessfulSignerViewSatisfies (CompletesSomeFewTimeTarget (cachedAdmissibleMessageInputs key.parameter cache hfinite)
      (fixedSigningViews key.parameter cache key.root log) (cachedFewTimeView cache)) result := by
  obtain ⟨signature, view, forgery, hshape, hne, hcover⟩ := hevent
  have hresult' : ((some signature, some view), result.2) ∈ support
      ((simulateQ romImpl (signWithView key message)).run cache) := by
    have heq : result = ((some signature, some view), result.2) := Prod.ext hshape rfl
    rwa [heq] at hresult
  obtain ⟨sourceOutput, hsource, _, hview⟩ := signWithView_successful_cached_output key message cache result.2 signature (some view) hresult'
  have hview' : view = hashOutputFewTimeView sourceOutput := Option.some.inj hview
  have hcache := simulateQ_romImpl_cache_le (signWithView key message) cache result hresult
  obtain ⟨targetOutput, htarget, hadmissible, hcovered⟩ := observedFewTimeCover_append_insertedView key.parameter cache result.2 key.root log
    hcache hsigned message signature sourceOutput hsource forgery hcover
  have hprior := signWithView_admissible_message_cached_before key message cache result.2 signature (some view) hresult'
    (messageDigestPayload key.root forgery.message forgery.signature.randomness) targetOutput hne htarget hadmissible
  let targetInput := tweakableHashInput key.parameter .message (messageDigestPayload key.root forgery.message forgery.signature.randomness)
  have htargetView : cachedFewTimeView cache targetInput = hashOutputFewTimeView targetOutput := by
    simp only [cachedFewTimeView, targetInput, hprior, Option.getD_some]
  have hmember : targetInput ∈ cachedAdmissibleMessageInputs key.parameter cache hfinite := by
    refine Finset.mem_filter.mpr ⟨hfinite.mem_toFinset.mpr ?_, ⟨_, rfl⟩, targetOutput, hprior, hadmissible⟩
    exact Option.ne_none_iff_exists'.mpr ⟨targetOutput, hprior⟩
  refine ⟨signature, view, hshape, targetInput, hmember, ?_, ?_⟩
  · rw [htargetView]
    intro hcovered
    exact hclean ⟨targetInput, targetOutput, ⟨_, rfl⟩, hprior, hadmissible, hcovered⟩
  · rw [htargetView, hview']
    exact hcovered

theorem probEvent_signerCompletesObservedTarget_le (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter cache key.root log)
    (hclean : ¬ CoveredMessageCache key.parameter (fixedSigningViews key.parameter cache key.root log) cache)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    Pr[SignerCompletesObservedTarget key message log | (simulateQ romImpl (signWithView key message)).run cache] ≤
      (∑ target ∈ cachedAdmissibleMessageInputs key.parameter cache hfinite,
        completionProbability (fixedSigningViews key.parameter cache key.root log target) (cachedFewTimeView cache target)) +
      cachedMessageEntryCountWhere cache key.parameter key.root message
        (CompletesSomeFewTimeTarget (cachedAdmissibleMessageInputs key.parameter cache hfinite)
          (fixedSigningViews key.parameter cache key.root log) (cachedFewTimeView cache)) * digestReuseWeight q := by
  apply (probEvent_mono (fun result hresult hevent =>
    signerCompletesObservedTarget_implies_completion key message cache hfinite log hsigned hclean result hresult hevent)).trans
  exact probEvent_signer_completesSomeFewTimeTarget_le _ _ _ key message cache q hq hcache

end SphincsSecurity.Concrete
