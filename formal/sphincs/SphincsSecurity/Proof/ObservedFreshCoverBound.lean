import SphincsSecurity.Proof.ObservedCoverPattern
import SphincsSecurity.Proof.FewTimeConditionalCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def eligibleSigningView? (answers : HashInput → Option HashOutput) (root : Digest)
    (targetPayload : HashInput) (entry : SigningEntry) : Option FewTimeView := do
  let signature ← entry.2
  if messageDigestPayload root entry.1 signature.randomness = targetPayload then none
  else observedSigningView? answers root entry

noncomputable def eligibleSigningViews (answers : HashInput → Option HashOutput) (root : Digest)
    (targetPayload : HashInput) (log : QueryLog SigningSpec) : Fin log.length → Option FewTimeView :=
  fun slot => eligibleSigningView? answers root targetPayload (log.get slot)

theorem eligibleSigningView?_eq_some {answers : HashInput → Option HashOutput} {root : Digest}
    {targetPayload : HashInput} {entry : SigningEntry} {signature : Signature} {digest : MessageDigest}
    (hresponse : entry.2 = some signature) (hdigest : ObservedMessageDigest answers root entry.1 signature.randomness digest)
    (hne : messageDigestPayload root entry.1 signature.randomness ≠ targetPayload) :
    eligibleSigningView? answers root targetPayload entry = some (fewTimeTargetView (digestIndex digest) (digestLeaves digest)) := by
  simp [eligibleSigningView?, hresponse, hne, observedSigningView?_eq_some hresponse hdigest]

theorem messageAnswers_cacheQuery_of_ne (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetPayload payload : HashInput) (output : HashOutput) (hne : payload ≠ targetPayload) :
    messageAnswers parameter (cache.cacheQuery (tweakableHashInput parameter .message targetPayload) output) payload =
      messageAnswers parameter cache payload := by
  have hinput : tweakableHashInput parameter .message payload ≠ tweakableHashInput parameter .message targetPayload := by
    intro heq
    exact hne (tweakableHashInput_injective parameter (by trivial) (by trivial) heq).2
  exact QueryCache.cacheQuery_of_ne cache output hinput

theorem observedFewTimeCover_after_query_covered (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (root : Digest) (log : QueryLog SigningSpec) (forgery : Forgery) (output : HashOutput)
    (hcover : ObservedFewTimeCover
      (messageAnswers parameter (cache.cacheQuery (tweakableHashInput parameter .message
        (messageDigestPayload root forgery.message forgery.signature.randomness)) output)) root log forgery) :
    Admissible (truncateMessageDigest output) ∧
      CoveredFewTimeView (eligibleSigningViews (messageAnswers parameter cache) root
        (messageDigestPayload root forgery.message forgery.signature.randomness) log) (hashOutputFewTimeView output) := by
  obtain ⟨digest, ⟨answer, hanswer, hdigest⟩, hadmissible, hcover⟩ := hcover
  have hanswer' : output = answer := by simpa only [messageAnswers, QueryCache.cacheQuery_self, Option.some.injEq] using hanswer
  have hdigest' : digest = truncateMessageDigest output := by rw [hanswer', hdigest]
  rw [hdigest'] at hadmissible hcover
  refine ⟨hadmissible, ?_⟩
  intro tree
  obtain ⟨entry, signature, signedDigest, hentry, hresponse, _, hsigned, hne, hindex, hleaf⟩ := hcover tree
  obtain ⟨signedAnswer, hsignedAnswer, htruncate⟩ := hsigned
  rw [messageAnswers_cacheQuery_of_ne parameter cache _ _ output hne] at hsignedAnswer
  have hview := eligibleSigningView?_eq_some hresponse ⟨signedAnswer, hsignedAnswer, htruncate⟩ hne
  obtain ⟨slot, hslot⟩ := List.mem_iff_get.mp hentry
  refine ⟨slot, fewTimeTargetView (digestIndex signedDigest) (digestLeaves signedDigest), ?_, hindex, hleaf⟩
  simpa only [eligibleSigningViews, hslot] using hview

theorem probEvent_uniform_observedFewTimeCover_le_occupancy
    (parameter : PublicParameter) (cache : QueryCache HashSpec) (root : Digest) (log : QueryLog SigningSpec) (forgery : Forgery) :
    Pr[fun output => ObservedFewTimeCover
      (messageAnswers parameter (cache.cacheQuery (tweakableHashInput parameter .message
        (messageDigestPayload root forgery.message forgery.signature.randomness)) output)) root log forgery |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (coverageOccupancyMoment (eligibleSigningViews (messageAnswers parameter cache) root
        (messageDigestPayload root forgery.message forgery.signature.randomness) log) : ENNReal) * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_mono (fun output _ hcover => observedFewTimeCover_after_query_covered parameter cache root log forgery output hcover)).trans
  exact probEvent_uniformHashOutput_covered_le_occupancy _

theorem probEvent_fresh_observedFewTimeCover_le_occupancy
    (parameter : PublicParameter) (cache : QueryCache HashSpec) (root : Digest) (log : QueryLog SigningSpec) (forgery : Forgery)
    (hfresh : cache (tweakableHashInput parameter .message (messageDigestPayload root forgery.message forgery.signature.randomness)) = none) :
    Pr[fun result : HashOutput × QueryCache HashSpec => ObservedFewTimeCover (messageAnswers parameter result.2) root log forgery |
      (randomOracle (tweakableHashInput parameter .message (messageDigestPayload root forgery.message forgery.signature.randomness))).run cache] ≤
      (coverageOccupancyMoment (eligibleSigningViews (messageAnswers parameter cache) root
        (messageDigestPayload root forgery.message forgery.signature.randomness) log) : ENNReal) * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hfresh, probEvent_map]
  exact probEvent_uniform_observedFewTimeCover_le_occupancy parameter cache root log forgery

def ObservedCoverAtPayload (answers : HashInput → Option HashOutput) (root : Digest)
    (log : QueryLog SigningSpec) (payload : HashInput) : Prop :=
  ∃ forgery, messageDigestPayload root forgery.message forgery.signature.randomness = payload ∧
    ObservedFewTimeCover answers root log forgery

theorem probEvent_uniform_observedCoverAtPayload_le_occupancy
    (parameter : PublicParameter) (cache : QueryCache HashSpec) (root : Digest)
    (log : QueryLog SigningSpec) (payload : HashInput) :
    Pr[fun output => ObservedCoverAtPayload
      (messageAnswers parameter (cache.cacheQuery (tweakableHashInput parameter .message payload) output)) root log payload |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (coverageOccupancyMoment (eligibleSigningViews (messageAnswers parameter cache) root payload log) : ENNReal) *
        ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_mono (q := fun output => Admissible (truncateMessageDigest output) ∧
    CoveredFewTimeView (eligibleSigningViews (messageAnswers parameter cache) root payload log)
      (hashOutputFewTimeView output)) ?_).trans (probEvent_uniformHashOutput_covered_le_occupancy _)
  intro output _ hcover
  obtain ⟨forgery, rfl, hcover⟩ := hcover
  exact observedFewTimeCover_after_query_covered parameter cache root log forgery output hcover

theorem probEvent_fresh_observedCoverAtPayload_le_occupancy
    (parameter : PublicParameter) (cache : QueryCache HashSpec) (root : Digest)
    (log : QueryLog SigningSpec) (payload : HashInput)
    (hfresh : cache (tweakableHashInput parameter .message payload) = none) :
    Pr[fun result : HashOutput × QueryCache HashSpec =>
      ObservedCoverAtPayload (messageAnswers parameter result.2) root log payload |
      (randomOracle (tweakableHashInput parameter .message payload)).run cache] ≤
      (coverageOccupancyMoment (eligibleSigningViews (messageAnswers parameter cache) root payload log) : ENNReal) *
        ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hfresh, probEvent_map]
  exact probEvent_uniform_observedCoverAtPayload_le_occupancy parameter cache root log payload

end SphincsSecurity.Concrete
