import XmssSecurity.CappedGlobalFirstLaneProgram
import XmssSecurity.CappedGlobalChainHighPublicExperiment

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable instance (input :
    RevealProbeOracleSimulation.Query GlobalChainValueIndex) :
    Fintype ((RevealProbeOracleSimulation.World GlobalChainValueIndex).Range
      input) := by
  cases input <;> infer_instance

noncomputable instance (input :
    RevealProbeOracleSimulation.Query GlobalChainValueIndex) :
    Inhabited ((RevealProbeOracleSimulation.World GlobalChainValueIndex).Range
      input) := by
  cases input <;> infer_instance

noncomputable instance globalRevealProbeWorldIsUniformSpec :
    IsUniformSpec
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) :=
  IsUniformSpec.ofFintypeInhabited _

theorem evalDist_globalRevealProbeLiftProbComp
    (computation : ProbComp α) :
    evalDist (RevealProbeOracleSimulation.liftProbComp
      (Index := GlobalChainValueIndex) computation) = evalDist computation := by
  unfold RevealProbeOracleSimulation.liftProbComp
  apply OracleComp.evalDist_simulateQ_eq_evalDist
  intro n
  simp [RevealProbeOracleSimulation.uniformForwardImpl,
    RevealProbeOracleSimulation.uniformQuery]

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

theorem evalDist_globalFirstLaneErase
    (computation : OracleComp GlobalFirstLaneWorld α) :
    evalDist (globalFirstLaneErase computation) = evalDist computation := by
  unfold globalFirstLaneErase
  apply OracleComp.evalDist_simulateQ_eq_evalDist
  intro input
  cases input with
  | uniform n =>
      simp [globalFirstLaneEraseImpl,
        RevealProbeOracleSimulation.uniformQuery]
  | encodingQuery epoch =>
      rw [globalFirstLaneEraseImpl,
        evalDist_globalRevealProbeLiftProbComp]
      apply SPMF.ext
      intro output
      simp [uniformHashOutput]
  | encodingSignAttempt epoch =>
      rw [globalFirstLaneEraseImpl,
        evalDist_globalRevealProbeLiftProbComp]
      apply SPMF.ext
      intro output
      simp [uniformHashOutput]
  | probe index target =>
      simp [globalFirstLaneEraseImpl,
        RevealProbeOracleSimulation.probeQuery]
  | reveal index =>
      simp [globalFirstLaneEraseImpl,
        RevealProbeOracleSimulation.revealQuery]

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

theorem globalFirstLaneErases_add
    (sourceLeft : QueryImpl specLeft
      (StateT stateType (OracleComp GlobalFirstLaneWorld)))
    (sourceRight : QueryImpl specRight
      (StateT stateType (OracleComp GlobalFirstLaneWorld)))
    (targetLeft : QueryImpl specLeft
      (StateT stateType
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))))
    (targetRight : QueryImpl specRight
      (StateT stateType
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))))
    (hleft : ∀ input state, GlobalFirstLaneErases
      ((sourceLeft input).run state) ((targetLeft input).run state))
    (hright : ∀ input state, GlobalFirstLaneErases
      ((sourceRight input).run state) ((targetRight input).run state))
    (input : (specLeft + specRight).Domain) (state : stateType) :
    GlobalFirstLaneErases
      (((sourceLeft + sourceRight) input).run state)
      (((targetLeft + targetRight) input).run state) := by
  cases input with
  | inl input => exact hleft input state
  | inr input => exact hright input state

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

theorem GlobalFirstLaneErases.of_eq_liftRevealProbe
    (source : OracleComp GlobalFirstLaneWorld α)
    (target : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α)
    (hsource : source = globalFirstLaneLiftRevealProbe target) :
    GlobalFirstLaneErases source target := by
  rw [hsource]
  exact globalFirstLaneErases_liftRevealProbe target

noncomputable def globalFirstLaneErasedFreshQuery
    (input : HashInput) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (HashOutput × GlobalCausalHashState) := do
  let output ← RevealProbeOracleSimulation.liftProbComp uniformHashOutput
  pure (output, state.setCache (state.cache.cacheQuery input output))

theorem globalFirstLaneErase_freshEncodingQuery
    (kind : EncodingSampleKind) (epoch : Epoch) (input : HashInput)
    (state : GlobalCausalHashState) :
    globalFirstLaneErase
      (globalFirstLaneFreshEncodingQuery kind epoch input state) =
      globalFirstLaneErasedFreshQuery input state := by
  unfold globalFirstLaneErasedFreshQuery
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

set_option maxRecDepth 1000000 in
theorem globalFirstLaneErase_attackerHashQueryFromHigh_encoding_cached
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (epoch : Epoch) (payload : Message × Randomness)
    (state : GlobalCausalHashState) (output : HashOutput)
    (hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch payload) =
        some output) :
    globalFirstLaneErase
      (globalFirstLaneAttackerHashQueryFromHighRun high secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
          state) =
      ((globalCausalAttackerHashQueryFromHigh high secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
          ).run state) := by
  rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_some high secretKey
    (Concrete.CacheView.encodingInput secretKey.parameter epoch payload) state
    epoch (encodingInputEpoch?_encodingInput secretKey.parameter epoch payload)]
  rw [globalFirstLaneAttackerHashQueryAtEpoch_eq_cached _ _ _ _ _ hcache]
  have hplan : globalFilteredCausalAttackerHashPlan secretKey
      (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
        state = .cached output := by
    rw [globalFilteredCausalAttackerHashPlan, hcache]
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan]
  change globalFirstLaneErase
      (pure (output, globalCausalRecordedState secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
          state)) = _
  simp [globalFirstLaneErase]

set_option maxRecDepth 1000000 in
theorem globalFirstLaneErase_attackerHashQueryFromHigh_encoding_fresh_source
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (epoch : Epoch) (payload : Message × Randomness)
    (state : GlobalCausalHashState)
    (hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch payload) =
        none) :
    globalFirstLaneErase
      (globalFirstLaneAttackerHashQueryFromHighRun high secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
          state) = globalFirstLaneErasedFreshQuery
        (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
        (globalCausalRecordedState secretKey
          (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
            state) := by
  rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_some high secretKey
    (Concrete.CacheView.encodingInput secretKey.parameter epoch payload) state
    epoch (encodingInputEpoch?_encodingInput secretKey.parameter epoch payload)]
  rw [globalFirstLaneAttackerHashQueryAtEpoch_eq_fresh _ _ _ _ hcache]
  rw [globalFirstLaneErase_freshEncodingQuery]

theorem globalCausalHashQuery_eq_globalFirstLaneErasedFreshQuery
    (input : HashInput) (state : GlobalCausalHashState)
    (hcache : state.cache input = none) :
    (globalCausalHashQuery input).run state =
      globalFirstLaneErasedFreshQuery input state := by
  rw [globalCausalHashQuery_run,
    randomOracle_run_none_eq_uniformHashOutput _ _ hcache]
  unfold globalFirstLaneErasedFreshQuery
  simp [RevealProbeOracleSimulation.liftProbComp, simulateQ_map,
    Functor.map_map, Function.comp_def]

theorem globalCausalAttackerHashQueryFromHigh_fresh_eq_hashQuery
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .fresh) :
    (globalCausalAttackerHashQueryFromHigh high secretKey input).run state =
      (globalCausalHashQuery input).run
        (globalCausalRecordedState secretKey input state) := by
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan]

theorem globalCausalAttackerHashQueryFromHigh_fresh_eq_erasedFresh
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .fresh)
    (hcache : state.cache input = none) :
    (globalCausalAttackerHashQueryFromHigh high secretKey input).run state =
      globalFirstLaneErasedFreshQuery input
        (globalCausalRecordedState secretKey input state) :=
  (globalCausalAttackerHashQueryFromHigh_fresh_eq_hashQuery high secretKey input
    state hplan).trans
      (globalCausalHashQuery_eq_globalFirstLaneErasedFreshQuery input
        (globalCausalRecordedState secretKey input state) (by simpa using hcache))

theorem globalFirstLaneErase_attackerHashQueryFromHigh_encoding_fresh_target
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (epoch : Epoch) (payload : Message × Randomness)
    (state : GlobalCausalHashState)
    (hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch payload) =
        none) :
    ((globalCausalAttackerHashQueryFromHigh high secretKey
      (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
        ).run state) = globalFirstLaneErasedFreshQuery
      (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
      (globalCausalRecordedState secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
          state) := by
  let input := Concrete.CacheView.encodingInput secretKey.parameter epoch payload
  change (globalCausalAttackerHashQueryFromHigh high secretKey input).run state =
    globalFirstLaneErasedFreshQuery input
      (globalCausalRecordedState secretKey input state)
  have hcache' : state.cache input = none := by simpa [input] using hcache
  have hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .fresh := by
    apply globalFilteredCausalAttackerHashPlan_eq_ordinaryFresh secretKey state
      input hcache'
    · simp [input]
    · simp [input]
  exact globalCausalAttackerHashQueryFromHigh_fresh_eq_erasedFresh high secretKey
    input state hplan hcache'

theorem globalFirstLaneErase_attackerHashQueryFromHigh_encoding_fresh
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (epoch : Epoch) (payload : Message × Randomness)
    (state : GlobalCausalHashState)
    (hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch payload) =
        none) :
    globalFirstLaneErase
      (globalFirstLaneAttackerHashQueryFromHighRun high secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
          state) =
      ((globalCausalAttackerHashQueryFromHigh high secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
          ).run state) := by
  rw [globalFirstLaneErase_attackerHashQueryFromHigh_encoding_fresh_source
    high secretKey epoch payload state hcache]
  exact (globalFirstLaneErase_attackerHashQueryFromHigh_encoding_fresh_target
    high secretKey epoch payload state hcache).symm

theorem globalFirstLaneErase_attackerHashQueryFromHigh_encoding
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (epoch : Epoch) (payload : Message × Randomness)
    (state : GlobalCausalHashState) :
    GlobalFirstLaneErases (α := HashOutput × GlobalCausalHashState)
      (globalFirstLaneAttackerHashQueryFromHighRun high secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
          state)
      ((globalCausalAttackerHashQueryFromHigh high secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter epoch payload)
          ).run state) := by
  constructor
  cases hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch payload) with
  | some output =>
      exact globalFirstLaneErase_attackerHashQueryFromHigh_encoding_cached
        high secretKey epoch payload state output hcache
  | none =>
      exact globalFirstLaneErase_attackerHashQueryFromHigh_encoding_fresh
        high secretKey epoch payload state hcache

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

set_option maxRecDepth 1000000 in
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
  dsimp only
  cases hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter epoch
        (message, randomness)) with
  | some output =>
      simp [hcache, randomOracle, globalFirstLaneErase,
        RevealProbeOracleSimulation.liftProbComp, simulateQ_map,
        Functor.map_map, Function.comp_def, GlobalCausalHashState.setCache]
  | none =>
      simp only
      rw [globalFirstLaneErase_freshEncodingQuery]
      unfold globalFirstLaneErasedFreshQuery
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

theorem globalFirstLaneOriginalEncodingDigestQuery_bind
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState)
    (next : Digest × GlobalCausalHashState →
      OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex) α) :
    globalFirstLaneOriginalEncodingDigestQuery secretKey epoch message
        randomness state >>= next =
      RevealProbeOracleSimulation.liftProbComp
          ((simulateQ randomOracle
            (Concrete.encodingHash secretKey.parameter epoch message
              randomness)).run state.cache) >>= fun encoded =>
        next (encoded.1, state.setCache encoded.2) := by
  simp [globalFirstLaneOriginalEncodingDigestQuery, bind_assoc]

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

set_option maxRecDepth 1000000 in
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
  rw [globalFirstLaneOriginalEncodingDigestQuery_bind]
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

set_option maxRecDepth 1000000 in
theorem globalFirstLaneAttackerHashQueryFromHighRun_eq_lift_of_none
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hepoch : encodingInputEpoch? secretKey.parameter input = none) :
    globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state =
      globalFirstLaneLiftRevealProbe
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state) := by
  exact globalFirstLaneAttackerHashQueryFromHighRun_eq_none high secretKey input
    state hepoch

set_option maxRecDepth 100000 in
theorem globalFirstLaneErase_attackerHashQueryFromHigh
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    GlobalFirstLaneErases (α := HashOutput × GlobalCausalHashState)
      (globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state)
      ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
        state) := by
  cases hepoch : encodingInputEpoch? secretKey.parameter input with
  | none =>
      apply GlobalFirstLaneErases.of_eq_liftRevealProbe
      exact globalFirstLaneAttackerHashQueryFromHighRun_eq_lift_of_none high
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

theorem globalFirstLaneErase_signingImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      ((globalFirstLaneSigningImpl keyView request).run state)
      (globalFilteredCausalSigningQuery keyView request state) := by
  exact globalFirstLaneErase_signingQuery keyView request state

@[irreducible]
noncomputable def globalFirstLaneAdversaryExecution
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (state : GlobalCausalHashState) :
    OracleComp GlobalFirstLaneWorld (Forgery × GlobalCausalHashState) :=
  (simulateQ (globalFirstLaneBaseMappedAdversaryImpl keyView edgeHigh)
    (adversary.main keyView.publicKey)).run state

@[irreducible]
noncomputable def globalHighDirectAdversaryExecution
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Forgery × GlobalCausalHashState) :=
  (simulateQ (globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh)
    (adversary.main keyView.publicKey)).run state

@[irreducible]
noncomputable def globalFirstLaneBaseMappedQueryExecution
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) : OracleComp GlobalFirstLaneWorld
      ((OracleWorld + SigningSpec).Range input × GlobalCausalHashState) :=
  (globalFirstLaneBaseMappedAdversaryImpl keyView edgeHigh input).run state

@[irreducible]
noncomputable def globalHighDirectBaseMappedQueryExecution
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      ((OracleWorld + SigningSpec).Range input × GlobalCausalHashState) :=
  (globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh input).run state

theorem globalFirstLaneBaseMappedAdversaryImpl_hash
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : HashInput) :
    globalFirstLaneBaseMappedAdversaryImpl keyView edgeHigh
        (.inl (.inr input)) =
      globalFirstLaneHashImpl keyView edgeHigh input := by
  unfold globalFirstLaneBaseMappedAdversaryImpl
  rfl

theorem globalHighDirectBaseMappedAdversaryImpl_hash
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : HashInput) :
    globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh
        (.inl (.inr input)) =
      globalCausalAttackerHashQueryFromHigh
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey input := by
  unfold globalHighDirectBaseMappedAdversaryImpl
  rfl

theorem globalFirstLaneErase_directUniformImpl
    (n : Nat) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      ((globalFirstLaneUniformImpl n).run state)
      ((globalHighDirectUniformImpl n).run state) := by
  unfold globalHighDirectUniformImpl
  exact globalFirstLaneErase_uniformImpl n state

theorem globalFirstLaneErase_directSigningImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      ((globalFirstLaneSigningImpl keyView request).run state)
      ((globalHighDirectSigningImpl keyView request).run state) := by
  unfold globalHighDirectSigningImpl
  exact globalFirstLaneErase_signingImpl keyView request state

structure GlobalFirstLaneOracleErasure
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) : Prop where
  erase : ∀ input state, GlobalFirstLaneErases
    (globalFirstLaneOracleExecution keyView edgeHigh input state)
    (globalHighDirectOracleExecution keyView edgeHigh input state)

theorem globalFirstLaneOracleErasure
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    GlobalFirstLaneOracleErasure keyView edgeHigh := by
  constructor
  intro input state
  cases input with
  | inl n =>
      unfold globalFirstLaneOracleExecution globalHighDirectOracleExecution
      exact globalFirstLaneErase_directUniformImpl n state
  | inr hashInput =>
      unfold globalFirstLaneOracleExecution globalHighDirectOracleExecution
      exact globalFirstLaneErase_attackerHashQueryFromHigh
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey hashInput
          state

structure GlobalFirstLaneBaseMappedErasure
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) : Prop where
  erase : ∀ input state, GlobalFirstLaneErases
    ((globalFirstLaneBaseMappedAdversaryImpl keyView edgeHigh input).run state)
    ((globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh input).run state)

set_option maxRecDepth 1000000 in
theorem globalFirstLaneBaseMappedErasure
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    GlobalFirstLaneBaseMappedErasure keyView edgeHigh := by
  refine ⟨?_⟩
  unfold globalFirstLaneBaseMappedAdversaryImpl
  unfold globalHighDirectBaseMappedAdversaryImpl
  exact globalFirstLaneErases_add
    (sourceLeft := globalFirstLaneOracleImpl keyView edgeHigh)
    (sourceRight := globalFirstLaneSigningImpl keyView)
    (targetLeft := globalHighDirectOracleImpl keyView edgeHigh)
    (targetRight := globalHighDirectSigningImpl keyView)
    (hleft := (globalFirstLaneOracleErasure keyView edgeHigh).erase)
    (hright := globalFirstLaneErase_directSigningImpl keyView)

theorem globalFirstLaneErase_baseMappedUniformQueryExecution
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (n : Nat) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      (globalFirstLaneBaseMappedQueryExecution keyView edgeHigh
        (.inl (.inl n)) state)
      (globalHighDirectBaseMappedQueryExecution keyView edgeHigh
        (.inl (.inl n)) state) := by
  unfold globalFirstLaneBaseMappedQueryExecution
  unfold globalHighDirectBaseMappedQueryExecution
  unfold globalFirstLaneBaseMappedAdversaryImpl
  unfold globalHighDirectBaseMappedAdversaryImpl
  exact globalFirstLaneErase_uniformImpl n state

set_option maxRecDepth 1000000 in
theorem globalFirstLaneErase_baseMappedSigningQueryExecution
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (request : SignRequest) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      (globalFirstLaneBaseMappedQueryExecution keyView edgeHigh
        (.inr request) state)
      (globalHighDirectBaseMappedQueryExecution keyView edgeHigh
        (.inr request) state) := by
  unfold globalFirstLaneBaseMappedQueryExecution
  unfold globalHighDirectBaseMappedQueryExecution
  unfold globalFirstLaneBaseMappedAdversaryImpl
  unfold globalHighDirectBaseMappedAdversaryImpl
  exact globalFirstLaneErase_signingImpl keyView request state

def GlobalFirstLaneAdversaryErases
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (state : GlobalCausalHashState) : Prop :=
  GlobalFirstLaneErases
    (globalFirstLaneAdversaryExecution adversary keyView edgeHigh state)
    (globalHighDirectAdversaryExecution adversary keyView edgeHigh state)

set_option maxRecDepth 1000000 in
theorem globalFirstLaneErase_adversaryMain
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      (globalFirstLaneAdversaryExecution adversary keyView edgeHigh state)
      (globalHighDirectAdversaryExecution adversary keyView edgeHigh state) := by
  unfold globalFirstLaneAdversaryExecution
  unfold globalHighDirectAdversaryExecution
  exact globalFirstLaneErases_simulateQ_run _ _
    (globalFirstLaneBaseMappedErasure keyView edgeHigh).erase
    (adversary.main keyView.publicKey) state

theorem globalFirstLaneErase_verifierUniformQuery
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (n : Nat) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      ((globalFirstLaneVerifierImpl keyView edgeHigh (.inl n)).run state)
      ((globalHighDirectVerifierImpl keyView edgeHigh (.inl n)).run state) := by
  unfold globalFirstLaneVerifierImpl globalHighDirectVerifierImpl
  unfold globalFirstLaneOracleImpl globalHighDirectOracleImpl
    globalFirstLaneOracleExecution globalHighDirectOracleExecution
    globalHighDirectUniformImpl
  exact globalFirstLaneErase_uniformImpl n state

theorem globalFirstLaneVerifierImpl_hash
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : HashInput) :
    globalFirstLaneVerifierImpl keyView edgeHigh (.inr input) =
      globalFirstLaneHashImpl keyView edgeHigh input := by
  unfold globalFirstLaneVerifierImpl globalFirstLaneOracleImpl
    globalFirstLaneOracleExecution
  rfl

theorem globalHighDirectVerifierImpl_hash
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : HashInput) :
    globalHighDirectVerifierImpl keyView edgeHigh (.inr input) =
      globalCausalAttackerHashQueryFromHigh
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey input := by
  unfold globalHighDirectVerifierImpl globalHighDirectOracleImpl
    globalHighDirectOracleExecution
  rfl

def GlobalFirstLaneVerificationErases
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (forgery : Forgery) (state : GlobalCausalHashState) : Prop :=
  GlobalFirstLaneErases
    ((simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
      (Concrete.scheme.verify keyView.publicKey forgery.epoch
        forgery.message forgery.signature)).run state)
    ((simulateQ (globalHighDirectVerifierImpl keyView edgeHigh)
      (Concrete.scheme.verify keyView.publicKey forgery.epoch
        forgery.message forgery.signature)).run state)

set_option maxRecDepth 1000000 in
theorem globalFirstLaneErase_verification
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (forgery : Forgery) (state : GlobalCausalHashState) :
    GlobalFirstLaneVerificationErases keyView edgeHigh forgery state := by
  unfold GlobalFirstLaneVerificationErases
  apply globalFirstLaneErases_simulateQ_run
  intro input queryState
  unfold globalFirstLaneVerifierImpl globalHighDirectVerifierImpl
  exact (globalFirstLaneBaseMappedErasure keyView edgeHigh).erase (.inl input)
    queryState

set_option maxRecDepth 1000000 in
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
  have hadversary := globalFirstLaneErase_adversaryMain adversary keyView
    edgeHigh state
  unfold globalFirstLaneAdversaryExecution at hadversary
  unfold globalHighDirectAdversaryExecution at hadversary
  apply hadversary.bind
  intro handled
  have hverification := globalFirstLaneErase_verification keyView edgeHigh
    handled.1 handled.2
  unfold GlobalFirstLaneVerificationErases at hverification
  apply hverification.bind
  exact fun verified => GlobalFirstLaneErases.pure _

set_option maxRecDepth 1000000 in
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

set_option maxRecDepth 1000000 in
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

theorem evalDist_globalFirstLaneProgram_eq_globalHighDirectProgram
    (adversary : Adversary Concrete.scheme) :
    evalDist (globalFirstLaneProgram adversary) =
      evalDist (globalHighDirectProgram adversary) := by
  calc
    evalDist (globalFirstLaneProgram adversary) =
        evalDist (globalFirstLaneErase
          (globalFirstLaneProgram adversary)) :=
      (evalDist_globalFirstLaneErase
        (globalFirstLaneProgram adversary)).symm
    _ = evalDist (globalHighDirectProgram adversary) := by
      rw [(globalFirstLaneErase_program adversary).eq]

theorem evalDist_globalFirstLanePublicProgram_eq_globalHighDirectPublicProgram
    (adversary : Adversary Concrete.scheme) :
    evalDist (globalFirstLanePublicProgram adversary) =
      evalDist (globalHighDirectPublicProgram adversary) := by
  calc
    evalDist (globalFirstLanePublicProgram adversary) =
        evalDist (globalFirstLaneErase
          (globalFirstLanePublicProgram adversary)) :=
      (evalDist_globalFirstLaneErase
        (globalFirstLanePublicProgram adversary)).symm
    _ = evalDist (globalHighDirectPublicProgram adversary) := by
      rw [(globalFirstLaneErase_publicProgram adversary).eq]

end XmssSecurity.CappedChain
