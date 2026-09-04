import SphincsSecurity.Proof.FewTimeRawTargetAllowed
import SphincsSecurity.Proof.FewTimeHonestLeakTerminal

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem rawTargetMonitoredAdversaryImpl_origin_replayConsistent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec)
    (result : α × OriginTargetMonitorState configuration)
    (hmem : result ∈ support
      ((simulateQ (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run (OriginTargetMonitorState.initial configuration initialCache))) :
    result.2.origin.ReplayConsistent secretKey := by
  have horigin : (result.1, result.2.origin) ∈ support
      ((simulateQ (originMonitoredAdversaryImpl configuration secretKey)
        computation).run (OriginMonitorState.initial configuration initialCache)) := by
    change (result.1, result.2.origin) ∈ support
      ((simulateQ (originMonitoredAdversaryImpl configuration secretKey) computation).run
        (OriginTargetMonitorState.initial configuration initialCache).origin)
    rw [← rawTargetMonitoredAdversaryImpl_projection configuration secretKey targetOrdinal
      computation (OriginTargetMonitorState.initial configuration initialCache), support_map]
    exact ⟨result, hmem, rfl⟩
  exact originMonitoredAdversaryImpl_replayConsistent configuration secretKey computation
    (OriginMonitorState.initial configuration initialCache) (result.1, result.2.origin)
    (OriginMonitorState.replayConsistent_initial configuration secretKey initialCache) horigin

theorem OriginConfiguration.raw_target_complete_and_hit
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index} {targetLeaves : DigestTree → FtsLeaf}
    {cover : FewTimeCover f cache secretKey signingLog index targetLeaves}
    {sources limit : Nat} {hle : signingLog.length ≤ limit}
    (configuration : OriginConfiguration (cover.pattern.pad hle) sources)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (beforeEntries suffix : List AdversaryCacheEntry)
    (input : HashInput) (output : HashOutput) (before after : QueryCache HashSpec)
    (hfresh : before input = none)
    (hsource : configuration.sourceAt? (directIntervalCount beforeEntries) = none)
    (hadmissible : signAttemptResultOfOutput output ≠ none)
    (hview : hashOutputFewTimeView output = fewTimeTargetView index targetLeaves)
    (result : α × OriginTargetMonitorState configuration)
    (hmem : result ∈ support
      ((simulateQ (rawTargetMonitoredAdversaryImpl configuration secretKey
        (rawTargetCandidateViews beforeEntries).length) computation).run
          (OriginTargetMonitorState.initial configuration initialCache)))
    (htrace : result.2.origin.viewed.trace.intervals =
      beforeEntries ++ ⟨.inl (.inr input), output, before, after⟩ :: suffix)
    (hlog : result.2.origin.viewed.trace.signing.toSigningLog = signingLog)
    (hrealized : configuration.PaddedRealizedBy cover hle result.2.origin.viewed.trace hlog)
    (hvalidIntervals : result.2.origin.viewed.trace.ValidIntervals secretKey)
    (hchronological : FullAdversaryTrace.Chronological result.2.origin.viewed.trace.intervals)
    (hcaches : result.2.origin.viewed.trace.signing.CachesLe cache)
    (hf : cache.AgreesWithFn f) :
    result.2.Complete ∧
      ∀ target, result.2.targetView = some target →
        FixedFewTimePatternHit (cover.pattern.pad hle).assignment
          (result.2.origin.observation.views, target) := by
  have hreplay := rawTargetMonitoredAdversaryImpl_origin_replayConsistent configuration secretKey
    _ computation initialCache result hmem
  obtain ⟨horigin, hhit⟩ := configuration.paddedRealized_complete_and_hit hlog hrealized
    hreplay hvalidIntervals hchronological hcaches hf
  obtain ⟨hvalid, htarget⟩ := rawTargetMonitoredAdversaryImpl_selected_direct configuration secretKey
    computation initialCache beforeEntries suffix input output before after hfresh hsource
    hadmissible result hmem htrace
  rw [hview] at htarget
  constructor
  · exact ⟨hvalid, horigin, _, htarget⟩
  · intro target htarget'
    have heq := Option.some.inj (htarget'.symm.trans htarget)
    simpa only [heq] using hhit

theorem trace_take_get_drop (intervals : List AdversaryCacheEntry)
    (source : Fin intervals.length) :
    intervals = intervals.take source.val ++ intervals.get source :: intervals.drop (source.val + 1) := by
  conv_lhs => rw [← List.take_append_drop source.val intervals]
  rw [List.drop_eq_getElem_cons source.isLt]
  rfl

end SphincsSecurity.Concrete
