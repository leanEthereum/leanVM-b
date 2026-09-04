import SphincsSecurity.Proof.FtsProbeSampling
import SphincsSecurity.Proof.OtsProbeRealization

/-!
# Retained one-time probe game

The retained game keeps exactly the root, forgery, signing log, verifier result and final cache.
Its ordinary projection is the existing signing-trace game, so the one-time terminal witnesses can
be transported without retaining the much larger proof-only view trace.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

noncomputable def actualRetainedGameAfterTable (adversary : Adversary)
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : Coordinate → HashOutput) :
    ProbComp (RetainedGameResult × QueryCache HashSpec) := do
  let otsSecret := tableOtsSecret table
  let (root, rootCache) ←
    (simulateQ (randomOracle : QueryImpl HashSpec _)
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅
  let secretKey : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
  let (result, finalCache) ←
    (simulateQ (unloggedMappedAdversaryImpl secretKey)
      (retainedGameRestComputation adversary ⟨root, parameter⟩)).run rootCache
  pure ((root, result), finalCache)

theorem simulateQ_unloggedMapped_signingTraceComputation_run
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (initialCache : QueryCache HashSpec) :
    (simulateQ (unloggedMappedAdversaryImpl secretKey)
        (signingTraceComputation computation)).run initialCache =
      (((simulateQ (mappedAdversaryImpl secretKey) computation).run).run initialCache) := by
  change (simulateQ (unloggedMappedAdversaryImpl secretKey)
      (Concrete.FtsProbeSimulation.signingTraceComputation computation)).run initialCache = _
  exact Concrete.FtsProbeSimulation.simulateQ_unloggedMapped_signingTraceComputation_run
    secretKey computation initialCache

theorem simulateQ_unloggedMapped_liftOracleWorldLeft
    (secretKey : SecretKey) (computation : OracleComp OracleWorld alpha) :
    simulateQ (unloggedMappedAdversaryImpl secretKey)
        (liftOracleWorldLeft computation) =
      simulateQ romImpl computation := by
  change simulateQ (unloggedMappedAdversaryImpl secretKey)
      (Concrete.FtsProbeSimulation.liftOracleWorldLeft computation) = _
  exact Concrete.FtsProbeSimulation.simulateQ_unloggedMapped_liftOracleWorldLeft
    secretKey computation

theorem simulateQ_unloggedMapped_retainedGameRestComputation
    (adversary : Adversary) (secretKey : SecretKey) (publicKey : PublicKey) :
    simulateQ (unloggedMappedAdversaryImpl secretKey)
        (retainedGameRestComputation adversary publicKey) = (do
      let (forgery, log) ←
        simulateQ (unloggedMappedAdversaryImpl secretKey)
          (signingTraceComputation (adversary.main publicKey))
      let verified ← simulateQ romImpl
        (scheme.verify publicKey forgery.message forgery.signature)
      pure ((forgery, log), verified)) := by
  unfold retainedGameRestComputation
  rw [simulateQ_bind]
  apply bind_congr
  intro result
  rcases result with ⟨forgery, log⟩
  rw [simulateQ_bind, simulateQ_unloggedMapped_liftOracleWorldLeft]
  simp

abbrev RetainedLogResult :=
  (Forgery × Bool) × (QueryCache HashSpec × QueryLog SigningSpec)

def retainedRestLogProjection :
    (RetainedRestResult × QueryCache HashSpec) → RetainedLogResult
  | (((forgery, log), verified), cache) =>
      ((forgery, decide (SigningTranscript.Valid log ∧
        ¬SigningTranscript.Contains log forgery) && verified), (cache, log))

def signingRestLogProjection :
    ((Forgery × Bool) × (QueryCache HashSpec × SigningCacheTrace)) → RetainedLogResult
  | ((forgery, verdict), (cache, trace)) =>
      ((forgery, verdict), (cache, trace.toSigningLog))

theorem retainedGameRest_signing_projection
    (adversary : Adversary) (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    retainedRestLogProjection <$>
        (simulateQ (unloggedMappedAdversaryImpl secretKey)
          (retainedGameRestComputation adversary publicKey)).run initialCache =
      signingRestLogProjection <$>
        gameRestWithSigningTrace adversary publicKey secretKey initialCache := by
  let traceRun := (simulateQ (cacheTracedMappedAdversaryImpl secretKey)
    (adversary.main publicKey)).run (initialCache, [])
  let retainedRun := (simulateQ (unloggedMappedAdversaryImpl secretKey)
    (signingTraceComputation (adversary.main publicKey))).run initialCache
  let prefixProjection :
      (Forgery × QueryLog SigningSpec) × QueryCache HashSpec →
        Forgery × (QueryCache HashSpec × QueryLog SigningSpec) :=
    fun result => (result.1.1, (result.2, result.1.2))
  let traceProjection :
      Forgery × (QueryCache HashSpec × SigningCacheTrace) →
        Forgery × (QueryCache HashSpec × QueryLog SigningSpec) :=
    fun result => (result.1, (result.2.1, result.2.2.toSigningLog))
  let finish : Forgery × (QueryCache HashSpec × QueryLog SigningSpec) →
      ProbComp RetainedLogResult := fun result => do
    let (verified, finalCache) ←
      (simulateQ romImpl
        (scheme.verify publicKey result.1.message result.1.signature)).run result.2.1
    pure ((result.1, decide (SigningTranscript.Valid result.2.2 ∧
      ¬SigningTranscript.Contains result.2.2 result.1) && verified),
        (finalCache, result.2.2))
  have hprefix : traceProjection <$> traceRun = prefixProjection <$> retainedRun := by
    rw [show traceProjection = Prod.map id
        (fun state : QueryCache HashSpec × SigningCacheTrace =>
          (state.1, state.2.toSigningLog)) from rfl]
    rw [show prefixProjection = fun result :
        (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
          (result.1.1, (result.2, result.1.2)) from rfl]
    rw [show traceRun = (simulateQ (cacheTracedMappedAdversaryImpl secretKey)
      (adversary.main publicKey)).run (initialCache, []) from rfl]
    rw [cacheTracedMappedAdversaryImpl_log_projection_eq_mapped]
    rw [show retainedRun = (simulateQ (unloggedMappedAdversaryImpl secretKey)
      (signingTraceComputation (adversary.main publicKey))).run initialCache from rfl]
    rw [simulateQ_unloggedMapped_signingTraceComputation_run]
  rw [simulateQ_unloggedMapped_retainedGameRestComputation adversary secretKey publicKey]
  calc
    retainedRestLogProjection <$>
        (do
          let result ← retainedRun
          let (verified, finalCache) ←
            (simulateQ romImpl
              (scheme.verify publicKey result.1.1.message result.1.1.signature)).run result.2
          pure ((result.1, verified), finalCache)) =
      (prefixProjection <$> retainedRun) >>= finish := by
        simp [retainedRestLogProjection, prefixProjection, retainedRun, finish,
          bind_map_left, map_bind]
    _ = (traceProjection <$> traceRun) >>= finish := by rw [hprefix]
    _ = signingRestLogProjection <$>
        gameRestWithSigningTrace adversary publicKey secretKey initialCache := by
      simp [gameRestWithSigningTrace, traceRun, traceProjection, finish,
        signingRestLogProjection, bind_map_left, map_bind]

abbrev RetainedGameLogResult :=
  (Digest × Forgery × Bool) × (QueryCache HashSpec × QueryLog SigningSpec)

def retainedGameLogProjection :
    (RetainedGameResult × QueryCache HashSpec) → RetainedGameLogResult
  | ((root, ((forgery, log), verified)), cache) =>
      ((root, forgery, decide (SigningTranscript.Valid log ∧
        ¬SigningTranscript.Contains log forgery) && verified), (cache, log))

def signingGameLogProjection :
    ((Digest × Forgery × Bool) × (QueryCache HashSpec × SigningCacheTrace)) →
      RetainedGameLogResult
  | ((root, forgery, verdict), (cache, trace)) =>
      ((root, forgery, verdict), (cache, trace.toSigningLog))

def viewedGameLogProjection :
    ((Digest × Forgery × Bool) × ViewedFullTraceState) → RetainedGameLogResult
  | ((root, forgery, verdict), state) =>
      ((root, forgery, verdict), (state.cache, state.trace.signing.toSigningLog))

theorem actualRetainedGameAfterTable_signing_projection
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : Coordinate → HashOutput) :
    retainedGameLogProjection <$>
        actualRetainedGameAfterTable adversary parameter ftsSecret table =
      signingGameLogProjection <$>
        gameAfterSecretsWithSigningTrace adversary parameter (tableOtsSecret table)
          ftsSecret := by
  let rootComputation : OracleComp HashSpec Digest :=
    treeRoot parameter topLayer rootTree (tableOtsSecret table topLayer rootTree)
  have hroot : simulateQ romImpl
      (liftM rootComputation : OracleComp OracleWorld Digest) =
      simulateQ (randomOracle : QueryImpl HashSpec _) rootComputation := by
    change simulateQ (unifFwdImpl HashSpec + randomOracle)
      (liftM rootComputation : OracleComp OracleWorld Digest) = _
    exact QueryImpl.simulateQ_add_liftM_right _ _ _
  unfold actualRetainedGameAfterTable gameAfterSecretsWithSigningTrace
  rw [show treeRoot parameter topLayer rootTree
    (tableOtsSecret table topLayer rootTree) = rootComputation from rfl, hroot]
  simp only [map_bind]
  apply bind_congr
  intro rootResult
  let secretKey : SecretKey :=
    ⟨parameter, rootResult.1, tableOtsSecret table, ftsSecret⟩
  have hrest := congrArg
    (Functor.map fun result : RetainedLogResult =>
      ((rootResult.1, result.1.1, result.1.2), result.2))
    (retainedGameRest_signing_projection adversary
      (⟨rootResult.1, parameter⟩ : PublicKey) secretKey rootResult.2)
  simpa [retainedGameLogProjection, signingGameLogProjection,
    retainedRestLogProjection, signingRestLogProjection, secretKey,
    Functor.map_map, map_bind, bind_map_left] using hrest

theorem gameAfterSecretsWithViewTrace_actualRetained_projection
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : Coordinate → HashOutput) :
    viewedGameLogProjection <$>
        gameAfterSecretsWithViewTrace adversary parameter (tableOtsSecret table) ftsSecret =
      retainedGameLogProjection <$>
        actualRetainedGameAfterTable adversary parameter ftsSecret table := by
  rw [show viewedGameLogProjection =
      Concrete.FtsProbeSimulation.viewedGameLogProjection from rfl]
  rw [Concrete.FtsProbeSimulation.gameAfterSecretsWithViewTrace_log_projection]
  exact (actualRetainedGameAfterTable_signing_projection adversary parameter
    ftsSecret table).symm

def RetainedWitnessFor (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (event : QueryImpl HashSpec Id → QueryCache HashSpec → SecretKey →
      QueryLog SigningSpec → Forgery → Index → (DigestTree → FtsLeaf) → Prop)
    (result : RetainedGameResult × QueryCache HashSpec) : Prop :=
  let root := result.1.1
  let forgery := result.1.2.1.1
  let log := result.1.2.1.2
  ∃ (f : QueryImpl HashSpec Id) (digest : MessageDigest),
    result.2.AgreesWithFn f
      ∧ SigningTranscript.Valid log
      ∧ ¬SigningTranscript.Contains log forgery
      ∧ evalWithAnswerFn f
          (messageDigest parameter root forgery.message forgery.signature.randomness) = digest
      ∧ Admissible digest
      ∧ event f result.2 ⟨parameter, root, tableOtsSecret table, ftsSecret⟩
        log forgery (digestIndex digest) (digestLeaves digest)

def RetainedLogWitnessFor (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (event : QueryImpl HashSpec Id → QueryCache HashSpec → SecretKey →
      QueryLog SigningSpec → Forgery → Index → (DigestTree → FtsLeaf) → Prop)
    (result : RetainedGameLogResult) : Prop :=
  let root := result.1.1
  let forgery := result.1.2.1
  let cache := result.2.1
  let log := result.2.2
  ∃ (f : QueryImpl HashSpec Id) (digest : MessageDigest),
    cache.AgreesWithFn f
      ∧ SigningTranscript.Valid log
      ∧ ¬SigningTranscript.Contains log forgery
      ∧ evalWithAnswerFn f
          (messageDigest parameter root forgery.message forgery.signature.randomness) = digest
      ∧ Admissible digest
      ∧ event f cache ⟨parameter, root, tableOtsSecret table, ftsSecret⟩
        log forgery (digestIndex digest) (digestLeaves digest)

def WinningRetainedWitnessFor (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (event : QueryImpl HashSpec Id → QueryCache HashSpec → SecretKey →
      QueryLog SigningSpec → Forgery → Index → (DigestTree → FtsLeaf) → Prop)
    (result : RetainedGameResult × QueryCache HashSpec) : Prop :=
  let root := result.1.1
  let forgery := result.1.2.1.1
  let log := result.1.2.1.2
  result.1.2.2 = true ∧
    ∃ (f : QueryImpl HashSpec Id) (digest : MessageDigest),
      result.2.AgreesWithFn f
        ∧ SigningTranscript.Valid log
        ∧ ¬SigningTranscript.Contains log forgery
        ∧ evalWithAnswerFn f
            (messageDigest parameter root forgery.message forgery.signature.randomness) = digest
        ∧ Admissible digest
        ∧ evalWithAnswerFn f
            (verify ⟨root, parameter⟩ forgery.message forgery.signature) = true
        ∧ event f result.2 ⟨parameter, root, tableOtsSecret table, ftsSecret⟩
          log forgery (digestIndex digest) (digestLeaves digest)

def WinningRetainedLogWitnessFor (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (event : QueryImpl HashSpec Id → QueryCache HashSpec → SecretKey →
      QueryLog SigningSpec → Forgery → Index → (DigestTree → FtsLeaf) → Prop)
    (result : RetainedGameLogResult) : Prop :=
  let root := result.1.1
  let forgery := result.1.2.1
  let cache := result.2.1
  let log := result.2.2
  result.1.2.2 = true ∧
    ∃ (f : QueryImpl HashSpec Id) (digest : MessageDigest),
      cache.AgreesWithFn f
        ∧ SigningTranscript.Valid log
        ∧ ¬SigningTranscript.Contains log forgery
        ∧ evalWithAnswerFn f
            (messageDigest parameter root forgery.message forgery.signature.randomness) = digest
        ∧ Admissible digest
        ∧ evalWithAnswerFn f
            (verify ⟨root, parameter⟩ forgery.message forgery.signature) = true
        ∧ event f cache ⟨parameter, root, tableOtsSecret table, ftsSecret⟩
          log forgery (digestIndex digest) (digestLeaves digest)

theorem viewedWitness_iff_logProjection
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (event : QueryImpl HashSpec Id → QueryCache HashSpec → SecretKey →
      QueryLog SigningSpec → Forgery → Index → (DigestTree → FtsLeaf) → Prop)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) :
    ViewedTerminalWitnessFor parameter (tableOtsSecret table) ftsSecret event result ↔
      RetainedLogWitnessFor parameter table ftsSecret event
        (viewedGameLogProjection result) := by
  rfl

theorem viewedWinningWitness_iff_logProjection
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (event : QueryImpl HashSpec Id → QueryCache HashSpec → SecretKey →
      QueryLog SigningSpec → Forgery → Index → (DigestTree → FtsLeaf) → Prop)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) :
    (result.1.2.2 = true ∧
      ViewedWinningTerminalWitnessFor parameter (tableOtsSecret table) ftsSecret event result) ↔
      WinningRetainedLogWitnessFor parameter table ftsSecret event
        (viewedGameLogProjection result) := by
  rfl

theorem logProjection_witness_imp_retained
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (event : QueryImpl HashSpec Id → QueryCache HashSpec → SecretKey →
      QueryLog SigningSpec → Forgery → Index → (DigestTree → FtsLeaf) → Prop)
    (result : RetainedGameResult × QueryCache HashSpec)
    (hwitness : RetainedLogWitnessFor parameter table ftsSecret event
      (retainedGameLogProjection result)) :
    RetainedWitnessFor parameter table ftsSecret event result := by
  rcases result with ⟨⟨root, ⟨⟨forgery, log⟩, verified⟩⟩, cache⟩
  exact hwitness

theorem logProjection_winningWitness_imp_retained
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (event : QueryImpl HashSpec Id → QueryCache HashSpec → SecretKey →
      QueryLog SigningSpec → Forgery → Index → (DigestTree → FtsLeaf) → Prop)
    (result : RetainedGameResult × QueryCache HashSpec)
    (hwitness : WinningRetainedLogWitnessFor parameter table ftsSecret event
      (retainedGameLogProjection result)) :
    WinningRetainedWitnessFor parameter table ftsSecret event result := by
  rcases result with ⟨⟨root, ⟨⟨forgery, log⟩, verified⟩⟩, cache⟩
  have hverified : verified = true := by
    cases verified <;>
      simp_all [WinningRetainedLogWitnessFor, retainedGameLogProjection]
  exact ⟨hverified, hwitness.2⟩

theorem probEvent_viewedWitness_le_actualRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (event : QueryImpl HashSpec Id → QueryCache HashSpec → SecretKey →
      QueryLog SigningSpec → Forgery → Index → (DigestTree → FtsLeaf) → Prop) :
    Pr[ViewedTerminalWitnessFor parameter (tableOtsSecret table) ftsSecret event |
      gameAfterSecretsWithViewTrace adversary parameter (tableOtsSecret table) ftsSecret] ≤
      Pr[RetainedWitnessFor parameter table ftsSecret event |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] := by
  calc
    Pr[ViewedTerminalWitnessFor parameter (tableOtsSecret table) ftsSecret event |
      gameAfterSecretsWithViewTrace adversary parameter (tableOtsSecret table) ftsSecret] =
      Pr[RetainedLogWitnessFor parameter table ftsSecret event |
        viewedGameLogProjection <$>
          gameAfterSecretsWithViewTrace adversary parameter (tableOtsSecret table)
            ftsSecret] := by
      rw [probEvent_map]
      apply OracleComp.probEvent_congr'
      · intro result _
        exact viewedWitness_iff_logProjection parameter table ftsSecret event result
      · rfl
    _ = Pr[RetainedLogWitnessFor parameter table ftsSecret event |
        retainedGameLogProjection <$>
          actualRetainedGameAfterTable adversary parameter ftsSecret table] := by
      apply OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      exact congrArg evalDist
        (gameAfterSecretsWithViewTrace_actualRetained_projection adversary parameter
          ftsSecret table)
    _ ≤ Pr[RetainedWitnessFor parameter table ftsSecret event |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] := by
      rw [probEvent_map]
      exact probEvent_mono fun result _ hwitness =>
        logProjection_witness_imp_retained parameter table ftsSecret event result hwitness

theorem probEvent_viewedWinningWitness_le_actualRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (event : QueryImpl HashSpec Id → QueryCache HashSpec → SecretKey →
      QueryLog SigningSpec → Forgery → Index → (DigestTree → FtsLeaf) → Prop) :
    Pr[fun result => result.1.2.2 = true ∧
      ViewedWinningTerminalWitnessFor parameter (tableOtsSecret table) ftsSecret event result |
        gameAfterSecretsWithViewTrace adversary parameter (tableOtsSecret table) ftsSecret] ≤
      Pr[WinningRetainedWitnessFor parameter table ftsSecret event |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] := by
  calc
    _ = Pr[WinningRetainedLogWitnessFor parameter table ftsSecret event |
        viewedGameLogProjection <$>
          gameAfterSecretsWithViewTrace adversary parameter (tableOtsSecret table)
            ftsSecret] := by
      rw [probEvent_map]
      apply OracleComp.probEvent_congr'
      · intro result _
        exact viewedWinningWitness_iff_logProjection parameter table ftsSecret event result
      · rfl
    _ = Pr[WinningRetainedLogWitnessFor parameter table ftsSecret event |
        retainedGameLogProjection <$>
          actualRetainedGameAfterTable adversary parameter ftsSecret table] := by
      apply OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      exact congrArg evalDist
        (gameAfterSecretsWithViewTrace_actualRetained_projection adversary parameter
          ftsSecret table)
    _ ≤ Pr[WinningRetainedWitnessFor parameter table ftsSecret event |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] := by
      rw [probEvent_map]
      exact probEvent_mono fun result _ hwitness =>
        logProjection_winningWitness_imp_retained parameter table ftsSecret event result hwitness

def RetainedFreshLayerOpeningWitness (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  RetainedWitnessFor parameter table ftsSecret
    fun f cache secretKey log forgery index leaves =>
      SettledForgedFreshLayerOpening f cache secretKey log index leaves forgery.signature

def RetainedBackwardChainOpeningWitness (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  RetainedWitnessFor parameter table ftsSecret
    fun f cache secretKey log forgery index leaves =>
      SettledForgedBackwardChainOpening f cache secretKey log index leaves forgery.signature

def WinningRetainedFreshLayerOpeningWitness (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  WinningRetainedWitnessFor parameter table ftsSecret
    fun f cache secretKey log forgery index leaves =>
      ¬Bad parameter (tableOtsSecret table) ftsSecret cache ∧
        SettledForgedFreshLayerOpening f cache secretKey log index leaves forgery.signature

def WinningRetainedBackwardChainOpeningWitness (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  WinningRetainedWitnessFor parameter table ftsSecret
    fun f cache secretKey log forgery index leaves =>
      ¬Bad parameter (tableOtsSecret table) ftsSecret cache ∧
        SettledForgedBackwardChainOpening f cache secretKey log index leaves forgery.signature

theorem probEvent_cleanFresh_le_actualRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[cleanFreshEvent parameter (tableOtsSecret table) ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter (tableOtsSecret table) ftsSecret] ≤
      Pr[WinningRetainedFreshLayerOpeningWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] := by
  calc
    _ ≤ Pr[fun result => result.1.2.2 = true ∧
        ViewedWinningTerminalWitnessFor parameter (tableOtsSecret table) ftsSecret
          (fun f cache secretKey log forgery index leaves =>
            ¬Bad parameter (tableOtsSecret table) ftsSecret cache ∧
              SettledForgedFreshLayerOpening f cache secretKey log index leaves
                forgery.signature)
          result |
          gameAfterSecretsWithViewTrace adversary parameter (tableOtsSecret table)
            ftsSecret] := by
      apply probEvent_mono
      intro _ _ hevent
      rcases hevent with ⟨⟨hbad, hverdict⟩, f, digest, hf, hvalid, hnotContains,
        hdigest, hadmissible, heval, hfresh⟩
      exact ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible,
        heval, hbad, hfresh⟩
    _ ≤ _ := probEvent_viewedWinningWitness_le_actualRetained adversary parameter table ftsSecret
      (fun f cache secretKey log forgery index leaves =>
        ¬Bad parameter (tableOtsSecret table) ftsSecret cache ∧
          SettledForgedFreshLayerOpening f cache secretKey log index leaves forgery.signature)

theorem probEvent_cleanBackward_le_actualRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[cleanBackwardEvent parameter (tableOtsSecret table) ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter (tableOtsSecret table) ftsSecret] ≤
      Pr[WinningRetainedBackwardChainOpeningWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] := by
  calc
    _ ≤ Pr[fun result => result.1.2.2 = true ∧
        ViewedWinningTerminalWitnessFor parameter (tableOtsSecret table) ftsSecret
          (fun f cache secretKey log forgery index leaves =>
            ¬Bad parameter (tableOtsSecret table) ftsSecret cache ∧
              SettledForgedBackwardChainOpening f cache secretKey log index leaves
                forgery.signature)
          result |
          gameAfterSecretsWithViewTrace adversary parameter (tableOtsSecret table)
            ftsSecret] := by
      apply probEvent_mono
      intro _ _ hevent
      rcases hevent with ⟨⟨hbad, hverdict⟩, f, digest, hf, hvalid, hnotContains,
        hdigest, hadmissible, heval, hbackward⟩
      exact ⟨hverdict, f, digest, hf, hvalid, hnotContains, hdigest, hadmissible,
        heval, hbad, hbackward⟩
    _ ≤ _ := probEvent_viewedWinningWitness_le_actualRetained adversary parameter table ftsSecret
      (fun f cache secretKey log forgery index leaves =>
        ¬Bad parameter (tableOtsSecret table) ftsSecret cache ∧
          SettledForgedBackwardChainOpening f cache secretKey log index leaves
            forgery.signature)

end SphincsSecurity.Concrete.OtsProbeSimulation
