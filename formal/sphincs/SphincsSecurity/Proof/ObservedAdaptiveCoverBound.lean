import SphincsSecurity.Proof.ObservedFreshCoverBound
import SphincsSecurity.Proof.FewTimeAdaptiveCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def fixedSigningViews (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (root : Digest) (log : QueryLog SigningSpec) (input : HashInput) : Fin log.length → Option FewTimeView :=
  eligibleSigningViews (messageAnswers parameter cache) root (payloadOf input) log

def SigningDigestsCached (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (root : Digest) (log : QueryLog SigningSpec) : Prop :=
  ∀ entry ∈ log, ∀ signature, entry.2 = some signature →
    messageAnswers parameter cache (messageDigestPayload root entry.1 signature.randomness) ≠ none

theorem signingDigestsCached_of_validTrace (key : SecretKey) (cache : QueryCache HashSpec)
    (trace : SigningCacheTrace) (hvalid : trace.ValidRuns key) (hcaches : trace.CachesLe cache) :
    SigningDigestsCached key.parameter cache key.root trace.toSigningLog := by
  intro entry hentry signature hresponse
  obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp hentry
  have hrun := record.successfulSignRun (hvalid record hrecord) hresponse (hcaches record hrecord).2
    (agreesWithFn_fromCache cache)
  obtain ⟨_, _, _, hdigest, _, _, _, _, _, _, _⟩ := hrun.indexed
  obtain ⟨_, _, _, _, _, _, hcached⟩ := hdigest.extract
  exact CachedRun.messageDigest_cached hcached

theorem observedFewTimeCover_coveredMessageCache (parameter : PublicParameter)
    (before after : QueryCache HashSpec) (root : Digest) (log : QueryLog SigningSpec)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached parameter before root log)
    (forgery : Forgery) (hcover : ObservedFewTimeCover (messageAnswers parameter after) root log forgery) :
    CoveredMessageCache parameter (fixedSigningViews parameter before root log) after := by
  obtain ⟨digest, ⟨answer, hanswer, hdigest⟩, hadmissible, hcover⟩ := hcover
  have hdigest' : digest = truncateMessageDigest answer := hdigest.symm
  rw [hdigest'] at hadmissible hcover
  refine ⟨tweakableHashInput parameter .message (messageDigestPayload root forgery.message forgery.signature.randomness),
    answer, ⟨_, rfl⟩, hanswer, hadmissible, ?_⟩
  rw [fixedSigningViews, payloadOf_tweakableHashInput]
  intro tree
  obtain ⟨entry, signature, signedDigest, hentry, hresponse, _, hsignedDigest, hne, hindex, hleaf⟩ := hcover tree
  obtain ⟨signedAnswer, hsignedAnswer, htruncate⟩ := hsignedDigest
  obtain ⟨priorAnswer, hprior⟩ := Option.ne_none_iff_exists'.mp (hsigned entry hentry signature hresponse)
  have hafter : messageAnswers parameter after (messageDigestPayload root entry.1 signature.randomness) = some priorAnswer := hcache hprior
  have heq : priorAnswer = signedAnswer := Option.some.inj (hafter.symm.trans hsignedAnswer)
  have hpriorDigest : ObservedMessageDigest (messageAnswers parameter before) root entry.1 signature.randomness signedDigest :=
    ⟨priorAnswer, hprior, heq ▸ htruncate⟩
  have hview := eligibleSigningView?_eq_some hresponse hpriorDigest hne
  obtain ⟨slot, hslot⟩ := List.mem_iff_get.mp hentry
  refine ⟨slot, fewTimeTargetView (digestIndex signedDigest) (digestLeaves signedDigest), ?_, hindex, hleaf⟩
  simpa only [eligibleSigningViews, hslot] using hview

theorem probEvent_adaptive_observedFewTimeCover_le_charge
    (parameter : PublicParameter) (cache : QueryCache HashSpec) (root : Digest) (log : QueryLog SigningSpec)
    (computation : OracleComp OracleWorld Forgery) (hfinite : Finite cache)
    (hsigned : SigningDigestsCached parameter cache root log) :
    Pr[fun result : Forgery × QueryCache HashSpec => ObservedFewTimeCover (messageAnswers parameter result.2) root log result.1 |
      (simulateQ romImpl computation).run cache] ≤
      (if CoveredMessageCache parameter (fixedSigningViews parameter cache root log) cache then 1 else 0) +
        expectedQueryCharge (freshCoverageCharge parameter (fixedSigningViews parameter cache root log)) computation cache *
          ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_mono (fun result hresult hcover => observedFewTimeCover_coveredMessageCache parameter cache result.2 root log
    (simulateQ_romImpl_cache_le computation cache result hresult) hsigned result.1 hcover)).trans
  exact probEvent_adaptive_coveredMessageCache_le_charge parameter (fixedSigningViews parameter cache root log) computation cache hfinite

end SphincsSecurity.Concrete
