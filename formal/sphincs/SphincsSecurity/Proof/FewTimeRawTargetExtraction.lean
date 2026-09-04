import SphincsSecurity.Proof.FewTimeRawTargetCompletion

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem OriginConfiguration.raw_target_monitored_complete_of_projection
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.cache.AgreesWithFn f)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest parameter result.1.1 result.1.2.1.message
        result.1.2.1.signature.randomness) = digest)
    (hproper : ProperFewTimeLeak f result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.trace.signing.toSigningLog (digestIndex digest) (digestLeaves digest))
    {limit sources : Nat} (hle : result.2.trace.signing.toSigningLog.length ≤ limit)
    (configuration : OriginConfiguration (hproper.1.cover.pattern.pad hle) sources)
    (hrealized : configuration.PaddedRealizedBy hproper.1.cover hle result.2.trace rfl)
    (source : Fin result.2.trace.intervals.length)
    (output : HashOutput) (before after : QueryCache HashSpec)
    (hentry : result.2.trace.intervals.get source =
      ⟨.inl (.inr (tweakableHashInput parameter .message
        (messageDigestPayload result.1.1 result.1.2.1.message
          result.1.2.1.signature.randomness))), output, before, after⟩)
    (hfresh : before (tweakableHashInput parameter .message
      (messageDigestPayload result.1.1 result.1.2.1.message
        result.1.2.1.signature.randomness)) = none)
    (hattempt : signAttemptResultOfOutput output = some (digestIndex digest, digestLeaves digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (initialCache : QueryCache HashSpec)
    (monitored : α × OriginTargetMonitorState configuration)
    (hmonitored : monitored ∈ support
      ((simulateQ (rawTargetMonitoredAdversaryImpl configuration
        ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
        (rawTargetCandidateViews (result.2.trace.intervals.take source.val)).length)
        computation).run (OriginTargetMonitorState.initial configuration initialCache)))
    (htrace : result.2.trace = monitored.2.origin.viewed.trace) :
    monitored.2.Complete ∧
      ∀ target, monitored.2.targetView = some target →
        FixedFewTimePatternHit (hproper.1.cover.pattern.pad hle).assignment
          (monitored.2.origin.observation.views, target) := by
  let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
  have hbase : (result.1, result.2.base) ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
    rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
      support_map]
    exact ⟨result, hresult, rfl⟩
  have hinvariants := gameAfterSecretsWithFullTrace_support_invariants adversary
    parameter otsSecret ftsSecret (result.1, result.2.base) hbase
  have hintervals := gameAfterSecretsWithFullTrace_support_interval_invariants adversary
    parameter otsSecret ftsSecret (result.1, result.2.base) hbase
  have hvalid := gameAfterSecretsWithFullTrace_support_validIntervals adversary
    parameter otsSecret ftsSecret (result.1, result.2.base) hbase
  have hsource := hproper.direct_target_not_configured_source result.1.2.1 digest hdigest rfl
    hle configuration result.2.trace rfl hrealized hvalid source output before after hentry
  have hview : hashOutputFewTimeView output =
      fewTimeTargetView (digestIndex digest) (digestLeaves digest) :=
    (signAttemptResultOfOutput_view output _ _ hattempt).symm
  have hsplit := trace_take_get_drop result.2.trace.intervals source
  rw [hentry] at hsplit
  have htraceSplit := (congrArg FullAdversaryTrace.intervals htrace).symm.trans hsplit
  obtain ⟨hlogMonitored, hrealizedMonitored⟩ :=
    configuration.paddedRealized_transport result.2.trace monitored.2.origin.viewed.trace
      htrace rfl hrealized
  apply configuration.raw_target_complete_and_hit computation initialCache
    (result.2.trace.intervals.take source.val) (result.2.trace.intervals.drop (source.val + 1))
    _ output before after hfresh hsource (by rw [hattempt]; simp) hview
    monitored hmonitored htraceSplit hlogMonitored hrealizedMonitored
  · rw [← htrace]
    exact hvalid
  · rw [← htrace]
    exact hintervals.2.2
  · rw [← htrace]
    exact hinvariants.2.1
  · exact hf

end SphincsSecurity.Concrete
