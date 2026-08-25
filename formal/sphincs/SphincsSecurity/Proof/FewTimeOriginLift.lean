import SphincsSecurity.Proof.FewTimeOriginTerminal

/-!
# Probability lift for a realized padded origin

For a fixed cover and target, the deterministic replay theorem turns every realized viewed trace
into the terminal event bounded by the origin monitor's supermartingale.  The monitor projection
then transfers that bound back to the viewed adversary execution.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

def PaddedOriginTerminal {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    {q limit : Nat} (hle : signingLog.length ≤ limit)
    (configuration : OriginConfiguration (cover.pattern.pad hle) q)
    (state : ViewedFullTraceState) : Prop :=
  ∃ hlog : state.trace.signing.toSigningLog = signingLog,
    configuration.PaddedRealizedBy cover hle state.trace hlog
      ∧ state.trace.ValidIntervals secretKey
      ∧ FullAdversaryTrace.Chronological state.trace.intervals
      ∧ state.trace.signing.CachesLe cache

noncomputable instance {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    {q limit : Nat} (hle : signingLog.length ≤ limit)
    (configuration : OriginConfiguration (cover.pattern.pad hle) q) :
    DecidablePred (PaddedOriginTerminal cover hle configuration) :=
  fun state => Classical.propDecidable (PaddedOriginTerminal cover hle configuration state)

theorem probEvent_paddedOriginTerminal_le_ideal {f : QueryImpl HashSpec Id}
    {cache initialCache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    {sources limit : Nat} (hle : signingLog.length ≤ limit)
    (configuration : OriginConfiguration (cover.pattern.pad hle) sources)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hf : cache.AgreesWithFn f) (q : Nat) (hq : q ≤ 2 ^ 120)
    (hinitialCache : QueryCache.enncard initialCache ≤ q) :
    Pr[fun result : α × ViewedFullTraceState =>
        PaddedOriginTerminal cover hle configuration result.2
          ∧ QueryCache.enncard result.2.cache ≤ q |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ configuration.prehit.card *
        Pr[fun views => FixedFewTimePatternHit (cover.pattern.pad hle).assignment
            (views, fewTimeTargetView index targetLeaves) |
          ($ᵗ ((cover.pattern.pad hle).selected → FewTimeView) :
            ProbComp ((cover.pattern.pad hle).selected → FewTimeView))] := by
  let initialState := OriginMonitorState.initial configuration initialCache
  let event := fun views =>
    FixedFewTimePatternHit (cover.pattern.pad hle).assignment
      (views, fewTimeTargetView index targetLeaves)
  let monitoredEvent := fun result : α × OriginMonitorState configuration =>
    result.2.Complete ∧ event result.2.observation.views
      ∧ QueryCache.enncard result.2.viewed.cache ≤ q
  calc
    _ ≤ Pr[monitoredEvent |
        (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
          computation).run initialState] := by
      apply probEvent_viewed_le_originMonitoredAdversaryImpl configuration secretKey
        computation initialState _ monitoredEvent
      intro result hresult hterminal
      obtain ⟨⟨hlog, hrealized, hvalidIntervals, hchronological, hcaches⟩,
        hcache⟩ := hterminal
      have hreplay := originMonitoredAdversaryImpl_replayConsistent
        configuration secretKey computation initialState result
        (OriginMonitorState.replayConsistent_initial configuration secretKey initialCache)
        hresult
      have hcomplete := configuration.paddedRealized_complete_and_hit hlog hrealized
        hreplay hvalidIntervals hchronological hcaches hf
      exact ⟨hcomplete.1, hcomplete.2, hcache⟩
    _ ≤ _ := by
      simpa only [initialState, event, monitoredEvent] using
        (probEvent_originMonitored_complete_le_ideal configuration secretKey computation
          initialCache event q hq hinitialCache)

end Concrete

end SphincsSecurity
