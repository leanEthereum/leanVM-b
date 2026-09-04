import SphincsSecurity.Proof.FewTimeRawTargetNonfresh

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem OriginConfiguration.raw_verifierTarget_fixedTerminal
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.cache.AgreesWithFn f)
    (digest : MessageDigest)
    (hproper : ProperFewTimeLeak f result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.trace.signing.toSigningLog (digestIndex digest) (digestLeaves digest))
    {limit sources : Nat} (hle : result.2.trace.signing.toSigningLog.length ≤ limit)
    (configuration : OriginConfiguration (hproper.1.cover.pattern.pad hle) sources)
    (hrealized : configuration.PaddedRealizedBy hproper.1.cover hle result.2.trace rfl)
    (rootCache : QueryCache HashSpec) (state : ViewedFullTraceState)
    (hadversary : (result.1.2.1, state) ∈ support
      ((simulateQ (viewedFullTracedMappedAdversaryImpl
        ⟨parameter, result.1.1, otsSecret, ftsSecret⟩)
        (adversary.main ⟨result.1.1, parameter⟩)).run
          ⟨rootCache, ⟨[], [], []⟩, [], none⟩))
    (htrace : result.2.trace = state.trace) (_hviews : result.2.views = state.views)
    (input : HashInput) (output : HashOutput) (digestCache : QueryCache HashSpec)
    (hinput : input = tweakableHashInput parameter .message
      (messageDigestPayload result.1.1 result.1.2.1.message
        result.1.2.1.signature.randomness))
    (hmiss : state.cache input = none)
    (hquery : (output, digestCache) ∈ support ((randomOracle input).run state.cache))
    (_hdigestCache : digestCache ≤ result.2.cache)
    (htargetView : hashOutputFewTimeView output =
      fewTimeTargetView (digestIndex digest) (digestLeaves digest))
    (hadmissible : signAttemptResultOfOutput output ≠ none)
    (q : Nat) (hcache : QueryCache.enncard digestCache ≤ q) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    let publicKey : PublicKey := ⟨result.1.1, parameter⟩
    let appended := appendTargetViewedState (.inl (.inr input)) state.cache output
      digestCache none state
    let targetOrdinal := (rawTargetCandidateViews state.trace.intervals).length
    FixedRawTargetViewedTerminal secretKey
      (adversaryWithTargetQuery adversary publicKey) rootCache q configuration
        targetOrdinal ((result.1.2.1, output), appended) := by
  classical
  let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
  let publicKey : PublicKey := ⟨result.1.1, parameter⟩
  let appended := appendTargetViewedState (.inl (.inr input)) state.cache output
    digestCache none state
  let targetOrdinal := (rawTargetCandidateViews state.trace.intervals).length
  have haugmented : ((result.1.2.1, output), appended) ∈ support
      ((simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        (adversaryWithTargetQuery adversary publicKey)).run
          ⟨rootCache, ⟨[], [], []⟩, [], none⟩) := by
    subst input
    exact adversaryWithTargetQuery_viewed_support adversary publicKey secretKey
      rootCache result.1.2.1 state hadversary output digestCache hquery
  refine ⟨hcache, ?_⟩
  intro monitored hmonitored heq
  have hstateEq : monitored.2.origin.viewed = appended := congrArg Prod.snd heq
  have hstateTraceEq : appended.trace = monitored.2.origin.viewed.trace :=
    congrArg ViewedFullTraceState.trace hstateEq.symm
  have hbase : (result.1, result.2.base) ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
    rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
      support_map]
    exact ⟨result, hresult, rfl⟩
  have hsourceNone : configuration.sourceAt? (directIntervalCount state.trace.intervals) = none := by
    rw [← htrace]
    exact configuration.paddedRealized_sourceAt_directIntervalCount_eq_none hrealized
  obtain ⟨hlogState, hrealizedState⟩ :=
    configuration.paddedRealized_transport result.2.trace state.trace htrace rfl hrealized
  obtain ⟨hlogAppended, hrealizedAppended⟩ :=
    configuration.paddedRealized_append_direct state hlogState hrealizedState input output digestCache
  obtain ⟨hlogMonitored, hrealizedMonitored⟩ :=
    configuration.paddedRealized_transport appended.trace monitored.2.origin.viewed.trace
      hstateTraceEq hlogAppended hrealizedAppended
  have haugmentedIntervals := viewedFullTracedMappedAdversaryImpl_interval_invariants
    secretKey (adversaryWithTargetQuery adversary publicKey) rootCache
      ((result.1.2.1, output), appended) haugmented
  have haugmentedValid := viewedFullTracedMappedAdversaryImpl_validIntervals
    secretKey (adversaryWithTargetQuery adversary publicKey) rootCache
      ((result.1.2.1, output), appended) haugmented
  have hcaches : appended.trace.signing.CachesLe result.2.cache := by
    have hcachesState : state.trace.signing.CachesLe result.2.cache := by
      rw [← htrace]
      exact (gameAfterSecretsWithFullTrace_support_invariants adversary parameter
        otsSecret ftsSecret (result.1, result.2.base) hbase).2.1
    simpa [appended, appendTargetViewedState, fullAdversaryTraceUpdate,
      signingCacheTraceUpdate] using hcachesState
  have htraceSplit : monitored.2.origin.viewed.trace.intervals =
      state.trace.intervals ++ [⟨.inl (.inr input), output, state.cache, digestCache⟩] := by
    simp [hstateEq, appended, appendTargetViewedState, fullAdversaryTraceUpdate]
  apply configuration.raw_target_complete_and_hit (adversaryWithTargetQuery adversary publicKey)
    rootCache state.trace.intervals [] input output state.cache digestCache hmiss hsourceNone
    hadmissible htargetView monitored hmonitored htraceSplit hlogMonitored hrealizedMonitored
  · rw [← hstateTraceEq]
    exact haugmentedValid
  · rw [← hstateTraceEq]
    exact haugmentedIntervals.2.2
  · rw [← hstateTraceEq]
    exact hcaches
  · exact hf

end SphincsSecurity.Concrete
