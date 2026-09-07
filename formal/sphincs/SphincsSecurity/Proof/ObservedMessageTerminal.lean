import SphincsSecurity.Proof.ObservedMessagePatterns
import SphincsSecurity.Proof.RetainedJointSecretProjection

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
open FtsProbeSimulation (messageAnswers RetainedGameResult)
set_option backward.isDefEq.respectTransparency false

theorem gameAfterSecretsWithViewTrace_target_cached
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.cache.AgreesWithFn f) :
    CachedRun result.2.cache f
      (messageDigest parameter result.1.1 result.1.2.1.message result.1.2.1.signature.randomness) := by
  rw [gameAfterSecretsWithViewTrace, mem_support_bind_iff] at hresult
  obtain ⟨⟨root, rootCache⟩, _, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨restResult, hrest, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  rw [gameRestWithViewTrace, mem_support_bind_iff] at hrest
  obtain ⟨⟨forgery, state⟩, _, hfinish⟩ := hrest
  rw [mem_support_bind_iff] at hfinish
  obtain ⟨⟨⟨verified, targetView⟩, finalCache⟩, hverifyView, hpure⟩ := hfinish
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst restResult
  have hverify : (verified, finalCache) ∈ support
      ((simulateQ romImpl (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run state.cache) := by
    rw [← simulateQ_verifyWithView_fst_run ⟨root, parameter⟩ forgery.message forgery.signature state.cache, support_map]
    exact ⟨((verified, targetView), finalCache), hverifyView, rfl⟩
  have hc : CachedRun finalCache f (verify ⟨root, parameter⟩ forgery.message forgery.signature) :=
    (replay_of_mem_support _ state.cache verified finalCache
      (by simpa only [scheme, simulateQ_romImpl_liftM] using hverify) f hf).2.2
  rw [verify] at hc
  exact CachedRun.bind_left hc

theorem messageOrForestEvent_observedCover
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (hevent : messageOrForestEvent parameter otsSecret ftsSecret result) :
    ObservedFewTimeCover (messageAnswers parameter result.2.cache) result.1.1 result.2.trace.signing.toSigningLog result.1.2.1 := by
  rcases hevent with hmessage | hforest
  · obtain ⟨_, f, digest, hf, _, _, _, _, hcollision, _⟩ := hmessage
    have hobserved : ObservedMessageCollision (messageAnswers parameter result.2.cache)
        result.1.1 result.2.trace.signing.toSigningLog result.1.2.1 :=
      messageDigestCollision_observed (key := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩) hf hcollision
    exact observedMessageCollision_implies_cover hobserved
  · obtain ⟨f, digest, hf, _, _, heval, hadmissible, hproper, _⟩ := hforest
    exact properFewTimeLeak_observed (key := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩) hf
      (gameAfterSecretsWithViewTrace_target_cached adversary parameter otsSecret ftsSecret result hresult f hf) heval hadmissible hproper

def ObservedRetainedCover (value : RetainedGameResult) (answers : HashInput → Option HashOutput) : Prop :=
  OtsProbeSimulation.retainedRestVerdict value.2 = true ∧
    ObservedFewTimeCover answers value.1 value.2.1.2 value.2.1.1

theorem retainedNonSecretResidual_observed_of_log
    (adversary : Adversary) (secrets : SampledSecrets)
    (left : (RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord)
    (right : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hlog : OtsProbeSimulation.retainedGameLogProjection left.1 = OtsProbeSimulation.viewedGameLogProjection right)
    (hright : right ∈ support (gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret secrets.ftsSecret))
    (hleft : retainedNonSecretResidual (secrets, left)) :
    ObservedRetainedCover left.1.1 (messageAnswers secrets.parameter left.1.2) := by
  have hcover := messageOrForestEvent_observedCover adversary secrets.parameter secrets.otsSecret secrets.ftsSecret right hright
    (messageOrForestEvent_of_retained_log adversary secrets left right hlog hright hleft)
  have hroot := congrArg (fun result : OtsProbeSimulation.RetainedGameLogResult => result.1.1) hlog
  have hforgery := congrArg (fun result : OtsProbeSimulation.RetainedGameLogResult => result.1.2.1) hlog
  have hcache := congrArg (fun result : OtsProbeSimulation.RetainedGameLogResult => result.2.1) hlog
  have hsigning := congrArg (fun result : OtsProbeSimulation.RetainedGameLogResult => result.2.2) hlog
  change left.1.1.1 = right.1.1 at hroot
  change left.1.1.2.1.1 = right.1.2.1 at hforgery
  change left.1.2 = right.2.cache at hcache
  change left.1.1.2.1.2 = right.2.trace.signing.toSigningLog at hsigning
  refine ⟨hleft.1.1.1, ?_⟩
  simpa only [hroot, hforgery, hcache, hsigning] using hcover

end SphincsSecurity.Concrete
