import XmssSecurity.CappedGlobalFirstLaneProgram

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable def globalFirstLaneEraseImpl :
    QueryImpl GlobalFirstLaneWorld
      (OracleComp
        (RevealProbeOracleSimulation.World GlobalChainValueIndex)) := fun input =>
  match input with
  | .uniform n => RevealProbeOracleSimulation.uniformQuery n
  | .encodingQuery _ =>
      RevealProbeOracleSimulation.liftProbComp uniformHashOutput
  | .encodingSignAttempt _ =>
      RevealProbeOracleSimulation.liftProbComp uniformHashOutput
  | .probe index target => RevealProbeOracleSimulation.probeQuery index target
  | .reveal index => RevealProbeOracleSimulation.revealQuery index

noncomputable def globalFirstLaneErase
    (computation : OracleComp GlobalFirstLaneWorld α) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex) α :=
  simulateQ globalFirstLaneEraseImpl computation

structure GlobalFirstLaneErases
    (source : OracleComp GlobalFirstLaneWorld α)
    (target : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α) : Prop where
  eq : globalFirstLaneErase source = target

theorem GlobalFirstLaneErases.bind
    (hsource : GlobalFirstLaneErases source target)
    (hnext : ∀ result, GlobalFirstLaneErases (nextSource result)
      (nextTarget result)) :
    GlobalFirstLaneErases (source >>= nextSource) (target >>= nextTarget) := by
  constructor
  rw [globalFirstLaneErase, simulateQ_bind]
  change globalFirstLaneErase source >>= _ = _
  rw [hsource.eq]
  apply bind_congr
  exact fun result => (hnext result).eq

theorem GlobalFirstLaneErases.pure (result : α) :
    GlobalFirstLaneErases (pure result) (pure result) := by
  constructor
  simp [globalFirstLaneErase]

theorem globalFirstLaneErases_simulateQ_run
    (sourceImpl : QueryImpl spec
      (StateT stateType (OracleComp GlobalFirstLaneWorld)))
    (targetImpl : QueryImpl spec
      (StateT stateType
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))))
    (himpl : ∀ input state,
      GlobalFirstLaneErases ((sourceImpl input).run state)
        ((targetImpl input).run state))
    (computation : OracleComp spec α) (state : stateType) :
    GlobalFirstLaneErases
      ((simulateQ sourceImpl computation).run state)
      ((simulateQ targetImpl computation).run state) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result => exact GlobalFirstLaneErases.pure _
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind]
      apply (himpl input state).bind
      intro result
      exact ih result.1 result.2

theorem globalFirstLaneErase_liftProbComp (computation : ProbComp α) :
    globalFirstLaneErase
      (FirstLaneOracleSimulation.liftProbComp
        (Index := GlobalChainValueIndex) computation) =
    RevealProbeOracleSimulation.liftProbComp computation := by
  induction computation using OracleComp.inductionOn with
  | pure result =>
      simp [globalFirstLaneErase, FirstLaneOracleSimulation.liftProbComp,
        RevealProbeOracleSimulation.liftProbComp]
  | query_bind n next ih =>
      simp [globalFirstLaneErase, FirstLaneOracleSimulation.liftProbComp,
        FirstLaneOracleSimulation.uniformForwardImpl,
        FirstLaneOracleSimulation.uniformQuery,
        RevealProbeOracleSimulation.liftProbComp,
        RevealProbeOracleSimulation.uniformForwardImpl,
        RevealProbeOracleSimulation.uniformQuery, globalFirstLaneEraseImpl,
        ih]
      apply bind_congr
      exact ih

theorem globalFirstLaneErases_liftProbComp (computation : ProbComp α) :
    GlobalFirstLaneErases
      (FirstLaneOracleSimulation.liftProbComp
        (Index := GlobalChainValueIndex) computation)
      (RevealProbeOracleSimulation.liftProbComp computation) :=
  ⟨globalFirstLaneErase_liftProbComp computation⟩

theorem globalFirstLaneErases_uniformQuery (n : Nat) :
    GlobalFirstLaneErases
      (FirstLaneOracleSimulation.uniformQuery
        (Index := GlobalChainValueIndex) n)
      (RevealProbeOracleSimulation.uniformQuery
        (Index := GlobalChainValueIndex) n) := by
  constructor
  simp [globalFirstLaneErase, globalFirstLaneEraseImpl,
    FirstLaneOracleSimulation.uniformQuery,
    RevealProbeOracleSimulation.uniformQuery]

theorem globalFirstLaneErase_liftRevealProbe
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α) :
    globalFirstLaneErase (globalFirstLaneLiftRevealProbe computation) =
      computation := by
  induction computation using OracleComp.inductionOn with
  | pure result =>
      simp [globalFirstLaneErase, globalFirstLaneLiftRevealProbe]
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          simp [globalFirstLaneErase, globalFirstLaneLiftRevealProbe,
            globalFirstLaneRevealProbeImpl,
            FirstLaneOracleSimulation.uniformQuery,
            RevealProbeOracleSimulation.uniformQuery,
            globalFirstLaneEraseImpl, ih]
          apply bind_congr
          exact ih
      | probe index target =>
          simp [globalFirstLaneErase, globalFirstLaneLiftRevealProbe,
            globalFirstLaneRevealProbeImpl,
            FirstLaneOracleSimulation.probeQuery,
            RevealProbeOracleSimulation.probeQuery,
            globalFirstLaneEraseImpl, ih]
          apply bind_congr
          exact ih
      | reveal index =>
          simp [globalFirstLaneErase, globalFirstLaneLiftRevealProbe,
            globalFirstLaneRevealProbeImpl,
            FirstLaneOracleSimulation.revealQuery,
            RevealProbeOracleSimulation.revealQuery,
            globalFirstLaneEraseImpl, ih]
          apply bind_congr
          exact ih

theorem globalFirstLaneErases_liftRevealProbe
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α) :
    GlobalFirstLaneErases (globalFirstLaneLiftRevealProbe computation)
      computation :=
  ⟨globalFirstLaneErase_liftRevealProbe computation⟩

theorem globalFirstLaneErase_freshEncodingQuery
    (kind : EncodingSampleKind) (epoch : Epoch) (input : HashInput)
    (state : GlobalCausalHashState) :
    globalFirstLaneErase
      (globalFirstLaneFreshEncodingQuery kind epoch input state) = (do
      let output ← RevealProbeOracleSimulation.liftProbComp uniformHashOutput
      pure (output, state.setCache (state.cache.cacheQuery input output))) := by
  unfold globalFirstLaneFreshEncodingQuery
  cases kind with
  | side =>
      change globalFirstLaneErase
        (FirstLaneOracleSimulation.liftProbComp uniformHashOutput >>= fun output =>
          pure (output,
            state.setCache (state.cache.cacheQuery input output))) = _
      rw [globalFirstLaneErase, simulateQ_bind]
      change globalFirstLaneErase
          (FirstLaneOracleSimulation.liftProbComp uniformHashOutput) >>= _ = _
      rw [globalFirstLaneErase_liftProbComp]
      simp [globalFirstLaneErase]
  | query =>
      simp [globalFirstLaneErase, globalFirstLaneEraseImpl,
        FirstLaneOracleSimulation.encodingQuery]
  | sign =>
      simp [globalFirstLaneErase, globalFirstLaneEraseImpl,
        FirstLaneOracleSimulation.encodingSignAttemptQuery]

@[simp]
theorem globalFirstLane_globalLeafInputData_encodingInput
    (parameter : PublicParameter) (epoch : Epoch)
    (payload : Message × Randomness) :
    globalLeafInputData? parameter
      (Concrete.CacheView.encodingInput parameter epoch payload) = none := by
  unfold globalLeafInputData?
  split
  · rename_i hexists
    obtain ⟨data, hdata⟩ := hexists
    have hdomain := domain_eq_of_tweakableHashInput_eq parameter hdata.symm
    cases hdomain
  · rfl

noncomputable def globalFirstLaneErasedAttackerHashQueryFromHighRun
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (HashOutput × GlobalCausalHashState) :=
  (globalCausalAttackerHashQueryFromHigh high secretKey input).run state

set_option maxRecDepth 100000 in
theorem globalFirstLaneErase_attackerHashQueryFromHigh_of_nonencoding
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hepoch : encodingInputEpoch? secretKey.parameter input = none) :
    GlobalFirstLaneErases (α := HashOutput × GlobalCausalHashState)
      (globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state)
      (globalFirstLaneErasedAttackerHashQueryFromHighRun high secretKey input
        state) := by
  simpa only [globalFirstLaneAttackerHashQueryFromHighRun, hepoch,
    globalFirstLaneErasedAttackerHashQueryFromHighRun] using
      globalFirstLaneErases_liftRevealProbe
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run state)

set_option maxRecDepth 100000 in
theorem globalFirstLaneErase_attackerHashQueryFromHigh_encoding
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (epoch : Epoch) (payload : Message × Randomness)
    (state : GlobalCausalHashState) :
    GlobalFirstLaneErases (α := HashOutput × GlobalCausalHashState)
      (globalFirstLaneAttackerHashQueryFromHighRun high secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
          state)
      (globalFirstLaneErasedAttackerHashQueryFromHighRun high secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
          state) := by
  constructor
  unfold globalFirstLaneAttackerHashQueryFromHighRun
  rw [encodingInputEpoch?_encodingInput]
  cases hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch payload) with
  | some output =>
      have hplan : globalFilteredCausalAttackerHashPlan secretKey
          (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
            state = .cached output := by
        rw [globalFilteredCausalAttackerHashPlan, hcache]
      simp only
      unfold globalFirstLaneErasedAttackerHashQueryFromHighRun
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan]
      simp [globalFirstLaneErase]
  | none =>
      have hplan : globalFilteredCausalAttackerHashPlan secretKey
          (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
            state = .fresh := by
        simp [globalFilteredCausalAttackerHashPlan, hcache,
          globalFilteredCausalUncachedAttackerHashPlan,
          globalFilteredCausalLeafHashPlan]
      simp only
      unfold globalFirstLaneErasedAttackerHashQueryFromHighRun
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan]
      simp only
      rw [globalFirstLaneErase_freshEncodingQuery]
      rw [globalCausalHashQuery_run,
        randomOracle_run_none_eq_uniformHashOutput _ _ (by simpa using hcache)]
      simp [RevealProbeOracleSimulation.liftProbComp, simulateQ_map,
        Functor.map_map, Function.comp_def, globalCausalRecordedState_cache]

noncomputable def globalFirstLaneErasedEncodingHashQuery
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (HashOutput × GlobalCausalHashState) := do
  let input := Concrete.CacheView.encodingInput secretKey.parameter epoch
    (message, randomness)
  let result ← RevealProbeOracleSimulation.liftProbComp
    ((randomOracle input).run state.cache)
  pure (result.1, state.setCache result.2)

set_option maxRecDepth 100000 in
theorem globalFirstLaneErase_encodingHashQuery
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases (α := HashOutput × GlobalCausalHashState)
      (globalFirstLaneEncodingHashQuery secretKey epoch message randomness state)
      (globalFirstLaneErasedEncodingHashQuery secretKey epoch message randomness
        state) := by
  constructor
  unfold globalFirstLaneEncodingHashQuery
  unfold globalFirstLaneErasedEncodingHashQuery
  cases hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch
        (message, randomness)) with
  | some output =>
      simp [hcache, randomOracle, globalFirstLaneErase]
  | none =>
      rw [hcache, globalFirstLaneErase_freshEncodingQuery]
      rw [randomOracle_run_none_eq_uniformHashOutput _ _ hcache]
      simp [RevealProbeOracleSimulation.liftProbComp, simulateQ_map,
        Functor.map_map, Function.comp_def, GlobalCausalHashState.setCache]

noncomputable def globalFirstLaneErasedEncodingDigestQuery
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Digest × GlobalCausalHashState) := do
  let result ← globalFirstLaneErasedEncodingHashQuery secretKey epoch message
    randomness state
  pure (truncateHash result.1, result.2)

noncomputable def globalFirstLaneOriginalEncodingDigestQuery
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Digest × GlobalCausalHashState) := do
  let result ← RevealProbeOracleSimulation.liftProbComp
    ((simulateQ randomOracle
      (Concrete.encodingHash secretKey.parameter epoch message randomness)).run
        state.cache)
  pure (result.1, state.setCache result.2)

theorem globalFirstLaneErasedEncodingDigestQuery_eq_original
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState) :
    globalFirstLaneErasedEncodingDigestQuery secretKey epoch message randomness
      state =
    globalFirstLaneOriginalEncodingDigestQuery secretKey epoch message randomness
      state := by
  simp [globalFirstLaneErasedEncodingDigestQuery,
    globalFirstLaneErasedEncodingHashQuery,
    globalFirstLaneOriginalEncodingDigestQuery, Concrete.encodingHash,
    Concrete.tweakableHash, Concrete.oracleHash, Concrete.CacheView.encodingInput,
    RevealProbeOracleSimulation.liftProbComp, simulateQ_map,
    map_eq_bind_pure_comp, GlobalCausalHashState.setCache]

noncomputable def globalFirstLaneErasedSigningAttemptRaw
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState) := do
  let randomness ← RevealProbeOracleSimulation.liftProbComp
    Concrete.signingRandomness
  let encoded ← globalFirstLaneErasedEncodingHashQuery keyView.secretKey
    request.epoch request.message randomness state
  match TargetSum.decodeDigest (truncateHash encoded.1) with
  | none => pure (none, encoded.2)
  | some encoding => do
      let result ← (revealGlobalSignatureChains request encoding allChains
        (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
          request.epoch randomness encoding)).run encoded.2
      pure (some result.1, result.2)

set_option maxRecDepth 100000 in
theorem globalFirstLaneErase_signingAttempt_raw
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      (globalFirstLaneSigningAttempt keyView request state)
      (globalFirstLaneErasedSigningAttemptRaw keyView request state) := by
  unfold globalFirstLaneSigningAttempt
  unfold globalFirstLaneErasedSigningAttemptRaw
  apply (globalFirstLaneErases_liftProbComp Concrete.signingRandomness).bind
  intro randomness
  apply (globalFirstLaneErase_encodingHashQuery keyView.secretKey request.epoch
    request.message randomness state).bind
  intro encoded
  cases hdecode : TargetSum.decodeDigest (truncateHash encoded.1) with
  | none => exact GlobalFirstLaneErases.pure _
  | some encoding =>
      apply (globalFirstLaneErases_liftRevealProbe
        ((revealGlobalSignatureChains request encoding allChains
          (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
            request.epoch randomness encoding)).run encoded.2)).bind
      exact fun result => GlobalFirstLaneErases.pure _

noncomputable def globalFirstLaneErasedSigningAttempt
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState) := do
  let randomness ← RevealProbeOracleSimulation.liftProbComp
    Concrete.signingRandomness
  let encoded ← globalFirstLaneErasedEncodingDigestQuery keyView.secretKey
    request.epoch request.message randomness state
  match TargetSum.decodeDigest encoded.1 with
  | none => pure (none, encoded.2)
  | some encoding => do
      let result ← (revealGlobalSignatureChains request encoding allChains
        (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
          request.epoch randomness encoding)).run encoded.2
      pure (some result.1, result.2)

theorem globalFirstLaneErasedSigningAttemptRaw_eq
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    globalFirstLaneErasedSigningAttemptRaw keyView request state =
      globalFirstLaneErasedSigningAttempt keyView request state := by
  simp [globalFirstLaneErasedSigningAttemptRaw,
    globalFirstLaneErasedSigningAttempt,
    globalFirstLaneErasedEncodingDigestQuery, bind_assoc]

theorem globalFirstLaneErasedSigningAttempt_eq_original
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    globalFirstLaneErasedSigningAttempt keyView request state =
      globalFilteredCausalSigningAttempt keyView request state := by
  unfold globalFirstLaneErasedSigningAttempt
  unfold globalFilteredCausalSigningAttempt
  apply bind_congr
  intro randomness
  rw [globalFirstLaneErasedEncodingDigestQuery_eq_original]
  rfl

theorem globalFirstLaneErase_signingAttempt
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      (globalFirstLaneSigningAttempt keyView request state)
      (globalFilteredCausalSigningAttempt keyView request state) := by
  constructor
  rw [(globalFirstLaneErase_signingAttempt_raw keyView request state).eq,
    globalFirstLaneErasedSigningAttemptRaw_eq,
    globalFirstLaneErasedSigningAttempt_eq_original]

theorem globalFirstLaneErase_signBoundedAttempts
    (attempts : Nat) (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      (globalFirstLaneSignBoundedAttempts attempts keyView request state)
      (globalFilteredCausalSignBoundedAttempts attempts keyView request state) := by
  induction attempts generalizing state with
  | zero => exact GlobalFirstLaneErases.pure _
  | succ attempts ih =>
      unfold globalFirstLaneSignBoundedAttempts
      unfold globalFilteredCausalSignBoundedAttempts
      apply (globalFirstLaneErase_signingAttempt keyView request state).bind
      intro result
      cases result.1 with
      | none => exact ih result.2
      | some signature => exact GlobalFirstLaneErases.pure _

theorem globalFirstLaneErase_signingQuery
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      (globalFirstLaneSigningQuery keyView request state)
      (globalFilteredCausalSigningQuery keyView request state) := by
  exact globalFirstLaneErase_signBoundedAttempts signingAttemptLimit keyView
    request state

theorem globalFirstLaneErase_attackerHashQueryFromHigh
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    GlobalFirstLaneErases (α := HashOutput × GlobalCausalHashState)
      (globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state)
      (globalFirstLaneErasedAttackerHashQueryFromHighRun high secretKey input
        state) := by
  cases hepoch : encodingInputEpoch? secretKey.parameter input with
  | none =>
      exact globalFirstLaneErase_attackerHashQueryFromHigh_of_nonencoding high
        secretKey input state hepoch
  | some epoch =>
      obtain ⟨payload, hinput⟩ :=
        exists_encodingInput_of_encodingInputEpoch?_eq_some secretKey.parameter
          input epoch hepoch
      subst input
      exact globalFirstLaneErase_attackerHashQueryFromHigh_encoding high
        secretKey epoch payload state

theorem globalFirstLaneErase_uniformImpl
    (n : Nat) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      ((globalFirstLaneUniformImpl n).run state)
      ((globalCausalUniformImpl n).run state) := by
  unfold globalFirstLaneUniformImpl
  unfold globalCausalUniformImpl
  apply (globalFirstLaneErases_uniformQuery n).bind
  exact fun output => GlobalFirstLaneErases.pure _

theorem globalFirstLaneErase_hashImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : HashInput) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      ((globalFirstLaneHashImpl keyView edgeHigh input).run state)
      (globalFirstLaneErasedAttackerHashQueryFromHighRun
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey input
          state) := by
  exact globalFirstLaneErase_attackerHashQueryFromHigh
    (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey input state

theorem globalFirstLaneErase_signingImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      ((globalFirstLaneSigningImpl keyView request).run state)
      (globalFilteredCausalSigningQuery keyView request state) := by
  exact globalFirstLaneErase_signingQuery keyView request state

set_option maxRecDepth 100000 in
theorem globalFirstLaneErase_baseMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      ((globalFirstLaneBaseMappedAdversaryImpl keyView edgeHigh input).run state)
      ((globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh input).run
        state) := by
  cases input with
  | inl oracleInput =>
      cases oracleInput with
      | inl n =>
          exact globalFirstLaneErase_uniformImpl n state
      | inr hashInput =>
          simpa only [globalFirstLaneBaseMappedAdversaryImpl,
            globalFirstLaneOracleImpl, globalFirstLaneHashImpl,
            globalHighDirectBaseMappedAdversaryImpl,
            globalFirstLaneErasedAttackerHashQueryFromHighRun] using
              globalFirstLaneErase_hashImpl keyView edgeHigh hashInput state
  | inr request =>
      exact globalFirstLaneErase_signingImpl keyView request state

theorem globalFirstLaneErase_adversaryMain
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      ((simulateQ (globalFirstLaneBaseMappedAdversaryImpl keyView edgeHigh)
        (adversary.main keyView.publicKey)).run state)
      ((simulateQ (globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh)
        (adversary.main keyView.publicKey)).run state) := by
  exact globalFirstLaneErases_simulateQ_run _ _
    (globalFirstLaneErase_baseMappedAdversaryImpl keyView edgeHigh)
    (adversary.main keyView.publicKey) state

set_option maxRecDepth 100000 in
theorem globalFirstLaneErase_verifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      ((globalFirstLaneVerifierImpl keyView edgeHigh input).run state)
      ((globalHighDirectVerifierImpl keyView edgeHigh input).run state) := by
  simpa only [globalFirstLaneVerifierImpl,
    globalHighDirectVerifierImpl] using
      globalFirstLaneErase_baseMappedAdversaryImpl keyView edgeHigh
        (.inl input) state

theorem globalFirstLaneErase_verification
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (forgery : Forgery) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      ((simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
        (Concrete.scheme.verify keyView.publicKey forgery.epoch
          forgery.message forgery.signature)).run state)
      ((simulateQ (globalHighDirectVerifierImpl keyView edgeHigh)
        (Concrete.scheme.verify keyView.publicKey forgery.epoch
          forgery.message forgery.signature)).run state) := by
  exact globalFirstLaneErases_simulateQ_run _ _
    (globalFirstLaneErase_verifierImpl keyView edgeHigh)
    (Concrete.scheme.verify keyView.publicKey forgery.epoch forgery.message
      forgery.signature) state

set_option maxRecDepth 100000 in
theorem globalFirstLaneErase_detailedExecution
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      ((globalFirstLaneDetailedExecution adversary keyView edgeHigh).run state)
      ((globalHighDirectDetailedExecution adversary keyView edgeHigh).run
        state) := by
  unfold globalFirstLaneDetailedExecution
  unfold globalHighDirectDetailedExecution
  apply (globalFirstLaneErase_adversaryMain adversary keyView edgeHigh
    state).bind
  intro handled
  apply (globalFirstLaneErase_verification keyView edgeHigh handled.1
    handled.2).bind
  exact fun verified => GlobalFirstLaneErases.pure _

set_option maxRecDepth 100000 in
theorem globalFirstLaneErase_program
    (adversary : Adversary Concrete.scheme) :
    GlobalFirstLaneErases
      (globalFirstLaneProgram adversary)
      (globalHighDirectProgram adversary) := by
  unfold globalFirstLaneProgram
  unfold globalHighDirectProgram
  apply (globalFirstLaneErases_liftProbComp globalHighDirectKeygen).bind
  intro keyResult
  apply (globalFirstLaneErase_detailedExecution adversary keyResult.1
    keyResult.2 (globalFilteredCausalKeygenState keyResult.1)).bind
  exact fun execution => GlobalFirstLaneErases.pure _

set_option maxRecDepth 100000 in
theorem globalFirstLaneErase_publicProgram
    (adversary : Adversary Concrete.scheme) :
    GlobalFirstLaneErases
      (globalFirstLanePublicProgram adversary)
      (globalHighDirectPublicProgram adversary) := by
  unfold globalFirstLanePublicProgram
  unfold globalHighDirectPublicProgram
  apply (globalFirstLaneErase_program adversary).bind
  intro result
  exact globalFirstLaneErases_liftRevealProbe
    (RevealProbeOracleSimulation.emitObservedTrace
      (globalHighDirectForgeryPrimaryProbeTrace result))

end XmssSecurity.CappedChain
