import XmssSecurity.CappedGlobalChainKeygenGameCoupling
import XmssSecurity.CappedChain.CausalStrategyProgram

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

structure GlobalCausalHashState where
  cache : QueryCache HashSpec
  keygenCache : QueryCache HashSpec
  revealed : GlobalChainValueIndex → Option Digest
  probes : List (GlobalChainValueIndex × Digest)

def GlobalCausalHashState.empty : GlobalCausalHashState :=
  ⟨∅, ∅, fun _ => none, []⟩

def GlobalCausalHashState.finishKeygen
    (state : GlobalCausalHashState) : GlobalCausalHashState :=
  { state with keygenCache := state.cache }

def GlobalCausalHashState.recordProbe
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    GlobalCausalHashState :=
  { state with probes :=
      match probe with
      | none => state.probes
      | some value => state.probes ++ [value] }

@[simp]
theorem GlobalCausalHashState.recordProbe_cache
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    (state.recordProbe probe).cache = state.cache := rfl

@[simp]
theorem GlobalCausalHashState.recordProbe_keygenCache
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    (state.recordProbe probe).keygenCache = state.keygenCache := rfl

@[simp]
theorem GlobalCausalHashState.recordProbe_revealed
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    (state.recordProbe probe).revealed = state.revealed := rfl

def GlobalCausalHashState.recordReveal
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (value : Digest) : GlobalCausalHashState :=
  { state with revealed := Function.update state.revealed index (some value) }

noncomputable def globalCausalHashQuery
    (input : HashInput) :
    StateT GlobalCausalHashState
      (OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      HashOutput := fun state =>
  (fun result : HashOutput × QueryCache HashSpec =>
    (result.1, { state with cache := result.2 })) <$>
      RevealProbeOracleSimulation.liftProbComp
        ((randomOracle input).run state.cache)

theorem globalCausalHashQuery_run
    (input : HashInput) (state : GlobalCausalHashState) :
    (globalCausalHashQuery input).run state =
      (fun result : HashOutput × QueryCache HashSpec =>
        (result.1, { state with cache := result.2 })) <$>
          RevealProbeOracleSimulation.liftProbComp
            ((randomOracle input).run state.cache) := rfl

inductive GlobalCausalHashPlan where
  | cached (output : HashOutput)
  | reveal (index : GlobalChainValueIndex)
  | redirect (output : HashOutput)
  | fresh

noncomputable def globalCausalLeafHashPlan
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) : GlobalCausalHashPlan :=
  match state.keygenCache
      (keygenLeafTargetInput secretKey state.keygenCache input) with
  | some output => .redirect output
  | none => .fresh

noncomputable def globalCausalUncachedAttackerHashPlan
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    Option (GlobalChainValueIndex × Digest) → GlobalCausalHashPlan
  | some (index, target) =>
      match state.revealed index with
      | some value =>
          if value = target then
            if hnext : index.2.2.val + 1 < chainLength then
              .reveal (index.1, index.2.1,
                ⟨index.2.2.val + 1, hnext⟩)
            else globalCausalLeafHashPlan secretKey input state
          else globalCausalLeafHashPlan secretKey input state
      | none => globalCausalLeafHashPlan secretKey input state
  | none => globalCausalLeafHashPlan secretKey input state

noncomputable def globalCausalAttackerHashPlan
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) : GlobalCausalHashPlan :=
  match state.cache input with
  | some output => .cached output
  | none => globalCausalUncachedAttackerHashPlan secretKey input state
      (globalChainInputProbe? secretKey.parameter input)

@[irreducible]
noncomputable def globalCausalRecordedState
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) : GlobalCausalHashState :=
  state.recordProbe (globalChainInputProbe? secretKey.parameter input)

@[simp]
theorem globalCausalRecordedState_cache
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalRecordedState secretKey input state).cache = state.cache := by
  rw [globalCausalRecordedState]
  exact GlobalCausalHashState.recordProbe_cache state _

@[simp]
theorem globalCausalRecordedState_keygenCache
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalRecordedState secretKey input state).keygenCache =
      state.keygenCache := by
  rw [globalCausalRecordedState]
  exact GlobalCausalHashState.recordProbe_keygenCache state _

@[simp]
theorem globalCausalRecordedState_revealed
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalRecordedState secretKey input state).revealed =
      state.revealed := by
  rw [globalCausalRecordedState]
  exact GlobalCausalHashState.recordProbe_revealed state _

noncomputable def globalCausalRevealResultState
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (value : Digest) (output : HashOutput) : GlobalCausalHashState :=
  { ((globalCausalRecordedState secretKey input state).recordReveal
      index value) with
    cache := (globalCausalRecordedState secretKey input state).cache.cacheQuery
      input output }

noncomputable def globalCausalRevealHashQuery
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (HashOutput × GlobalCausalHashState) := do
  let value ← RevealProbeOracleSimulation.revealQuery index
  let output ← RevealProbeOracleSimulation.liftProbComp
    (Rom.sampleHashOutputWithDigest value)
  pure (output,
    globalCausalRevealResultState secretKey input state index value output)

noncomputable def globalCausalAttackerHashQuery
    (secretKey : SecretKey) (input : HashInput) :
    StateT GlobalCausalHashState
      (OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      HashOutput := fun state =>
  let recorded := globalCausalRecordedState secretKey input state
  match globalCausalAttackerHashPlan secretKey input state with
  | .cached output => pure (output, recorded)
  | .redirect output =>
      pure (output, { recorded with cache := recorded.cache.cacheQuery input output })
  | .fresh => (globalCausalHashQuery input).run recorded
  | .reveal index =>
      globalCausalRevealHashQuery secretKey input state index

theorem globalCausalAttackerHashQuery_run
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalAttackerHashQuery secretKey input).run state =
      (let recorded := globalCausalRecordedState secretKey input state
        match globalCausalAttackerHashPlan secretKey input state with
        | .cached output => pure (output, recorded)
        | .redirect output =>
            pure (output,
              { recorded with cache := recorded.cache.cacheQuery input output })
        | .fresh => (globalCausalHashQuery input).run recorded
        | .reveal index =>
            globalCausalRevealHashQuery secretKey input state index) := rfl

def globalCausalUniformImpl :
    QueryImpl unifSpec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun n => liftM (RevealProbeOracleSimulation.uniformQuery
    (Index := GlobalChainValueIndex) n)

noncomputable def globalCausalHashImpl :
    QueryImpl HashSpec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  globalCausalHashQuery

noncomputable def globalCausalXmssRomImpl :
    QueryImpl OracleWorld
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  globalCausalUniformImpl + globalCausalHashImpl

noncomputable def globalCausalVerifierXmssRomImpl
    (secretKey : SecretKey) :
    QueryImpl OracleWorld
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  globalCausalUniformImpl + globalCausalAttackerHashQuery secretKey

noncomputable def revealGlobalSignatureChains
    (request : SignRequest) (encoding : ChainIndex → ChainDigit) :
    List ChainIndex → Signature →
      StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex)) Signature
  | [], signature => pure signature
  | chain :: chains, signature => fun state => do
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      let value ← RevealProbeOracleSimulation.revealQuery index
      (revealGlobalSignatureChains request encoding chains
        (replaceSignatureChainValue signature chain value)).run
          (state.recordReveal index value)

noncomputable def revealGlobalSignatureOption
    (secretKey : SecretKey) (request : SignRequest) :
    Option Signature →
      StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))
        (Option Signature)
  | none => pure none
  | some signature => fun state =>
      match TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash state.cache secretKey.parameter
            request.epoch (request.message, signature.randomness)) with
      | none => pure (some signature, state)
      | some encoding => do
          let revealed ← (revealGlobalSignatureChains request encoding allChains
            signature).run state
          pure (some revealed.1, revealed.2)

noncomputable def globalCausalMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input =>
    match input with
    | .inl (.inl n) => globalCausalUniformImpl n
    | .inl (.inr hashInput) =>
        globalCausalAttackerHashQuery secretKey hashInput
    | .inr request => do
        let signature ← simulateQ globalCausalXmssRomImpl
          (Concrete.cappedScheme.sign publicKey secretKey request.epoch
            request.message)
        revealGlobalSignatureOption secretKey request signature

noncomputable def globalCausalActionTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT AttackerActionTrace
        (StateT GlobalCausalHashState
          (OracleComp
            (RevealProbeOracleSimulation.World GlobalChainValueIndex)))) :=
  (globalCausalMappedAdversaryImpl publicKey secretKey).withTraceAppend
    attackerActionFragment

noncomputable def globalCausalDetailedGameAfterKeygen
    (adversary : Adversary Concrete.cappedScheme)
    (publicKey : PublicKey) (secretKey : SecretKey) :
    StateT GlobalCausalHashState
      (OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      ((Forgery × Bool) × AttackerActionTrace) := do
  let result ← (simulateQ
    (globalCausalActionTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run
  let verified ← simulateQ (globalCausalVerifierXmssRomImpl secretKey)
    (Concrete.cappedScheme.verify publicKey result.1.epoch result.1.message
      result.1.signature)
  pure ((result.1, verified), result.2)

def globalCausalDetailedResult
    (keyResult : (PublicKey × SecretKey) × GlobalCausalHashState)
    (execution :
      ((Forgery × Bool) × AttackerActionTrace) × GlobalCausalHashState) :
    DetailedActionTracedResult :=
  ((((keyResult.1, keyResult.2.cache),
      (actionTraceOutcome keyResult.1.1 keyResult.1.2 execution.1,
        execution.2.cache))), execution.1.2)

noncomputable def globalCausalStrategyProgram
    (adversary : Adversary Concrete.cappedScheme) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (List Bool → GlobalChainValueIndex × Digest) := do
  let keyResult ← (simulateQ globalCausalXmssRomImpl Concrete.keygen).run
    GlobalCausalHashState.empty
  let execution ← (globalCausalDetailedGameAfterKeygen adversary
    keyResult.1.1 keyResult.1.2).run keyResult.2.finishKeygen
  pure (globalActionTracedRevealProbeView
    (globalCausalDetailedResult keyResult execution)).strategy

theorem globalCausalHashQuery_run_isProbeQueryBoundP
    (input : HashInput) (state : GlobalCausalHashState) :
    (globalCausalHashQuery input).run state |>.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold globalCausalHashQuery
  apply (OracleComp.isQueryBoundP_map_iff _ _ 0).2
  exact RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
    ((randomOracle input).run state.cache) 0

theorem globalCausalUniformImpl_run_isProbeQueryBoundP
    (n : Nat) (state : GlobalCausalHashState) :
    (globalCausalUniformImpl n).run state |>.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold globalCausalUniformImpl
  rw [OracleComp.liftM_run_StateT]
  have huniform :
      (RevealProbeOracleSimulation.uniformQuery
        (Index := GlobalChainValueIndex) n).IsQueryBoundP
          RevealProbeOracleSimulation.IsProbeQuery 0 := by
    rw [RevealProbeOracleSimulation.uniformQuery,
      OracleComp.isQueryBoundP_query_iff]
    simp [RevealProbeOracleSimulation.IsProbeQuery]
  have hbind := OracleComp.isQueryBoundP_bind
    (n := 0) (m := 0) huniform fun result _hresult =>
      OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery) (result, state) 0
  simpa using hbind

theorem globalCausalXmssRomImpl_step_isProbeQueryBoundP
    (input : OracleWorld.Domain) (state : GlobalCausalHashState) :
    (globalCausalXmssRomImpl input).run state |>.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  cases input with
  | inl n => exact globalCausalUniformImpl_run_isProbeQueryBoundP n state
  | inr hashInput =>
      exact globalCausalHashQuery_run_isProbeQueryBoundP hashInput state

theorem simulate_globalCausalXmssRomImpl_isProbeQueryBoundP
    (computation : OracleComp OracleWorld alpha)
    (state : GlobalCausalHashState) :
    (simulateQ globalCausalXmssRomImpl computation).run state
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  refine OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step
    (OracleComp.isQueryBoundP_false computation 0) ?_ state
  intro input currentState
  simpa using globalCausalXmssRomImpl_step_isProbeQueryBoundP
    input currentState

theorem globalCausalAttackerHashQuery_run_isProbeQueryBoundP
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalAttackerHashQuery secretKey input).run state
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  rw [globalCausalAttackerHashQuery_run]
  generalize hplan :
    globalCausalAttackerHashPlan secretKey input state = plan
  cases plan with
  | cached output => simp
  | redirect output => simp
  | fresh =>
      exact globalCausalHashQuery_run_isProbeQueryBoundP input
        (globalCausalRecordedState secretKey input state)
  | reveal index =>
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP index 0)
      intro value _hvalue
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
          (Rom.sampleHashOutputWithDigest value) 0)
      intro output _houtput
      exact OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery)
        (output,
          globalCausalRevealResultState secretKey input state index value
            output) 0

theorem globalCausalVerifierXmssRomImpl_step_isProbeQueryBoundP
    (secretKey : SecretKey) (input : OracleWorld.Domain)
    (state : GlobalCausalHashState) :
    (globalCausalVerifierXmssRomImpl secretKey input).run state
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  cases input with
  | inl n => exact globalCausalUniformImpl_run_isProbeQueryBoundP n state
  | inr hashInput =>
      exact globalCausalAttackerHashQuery_run_isProbeQueryBoundP
        secretKey hashInput state

theorem simulate_globalCausalVerifierXmssRomImpl_isProbeQueryBoundP
    (secretKey : SecretKey) (computation : OracleComp OracleWorld alpha)
    (state : GlobalCausalHashState) :
    (simulateQ (globalCausalVerifierXmssRomImpl secretKey) computation).run
        state |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  refine OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step
    (OracleComp.isQueryBoundP_false computation 0) ?_ state
  intro input currentState
  simpa using globalCausalVerifierXmssRomImpl_step_isProbeQueryBoundP
    secretKey input currentState

theorem revealGlobalSignatureChains_run_isProbeQueryBoundP
    (request : SignRequest) (encoding : ChainIndex → ChainDigit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) :
    (revealGlobalSignatureChains request encoding chains signature).run state
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  induction chains generalizing signature state with
  | nil => simp [revealGlobalSignatureChains]
  | cons chain chains ih =>
      rw [revealGlobalSignatureChains]
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP index 0)
      intro value _hvalue
      exact ih (replaceSignatureChainValue signature chain value)
        (state.recordReveal index value)

theorem revealGlobalSignatureOption_run_isProbeQueryBoundP
    (secretKey : SecretKey) (request : SignRequest)
    (signatureOption : Option Signature) (state : GlobalCausalHashState) :
    (revealGlobalSignatureOption secretKey request signatureOption).run state
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  cases signatureOption with
  | none => simp [revealGlobalSignatureOption]
  | some signature =>
      rw [revealGlobalSignatureOption]
      split
      · simp
      · rename_i encoding hdecode
        rw [StateT.run_bind]
        have hreveal := revealGlobalSignatureChains_run_isProbeQueryBoundP
          request encoding allChains signature state
        apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0) hreveal
        intro revealed _hrevealed
        exact OracleComp.isQueryBoundP_pure
          (p := RevealProbeOracleSimulation.IsProbeQuery)
          (some revealed.1, revealed.2) 0

theorem globalCausalMappedAdversaryImpl_step_isProbeQueryBoundP
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    (globalCausalMappedAdversaryImpl publicKey secretKey input).run state
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · exact globalCausalUniformImpl_run_isProbeQueryBoundP n state
    · exact globalCausalAttackerHashQuery_run_isProbeQueryBoundP
        secretKey hashInput state
  · unfold globalCausalMappedAdversaryImpl
    rw [StateT.run_bind]
    have hsign := simulate_globalCausalXmssRomImpl_isProbeQueryBoundP
      (Concrete.cappedScheme.sign publicKey secretKey request.epoch
        request.message) state
    have hbind := OracleComp.isQueryBoundP_bind
      (n := 0) (m := 0) hsign fun result _hresult =>
        revealGlobalSignatureOption_run_isProbeQueryBoundP secretKey request
          result.1 result.2
    simpa using hbind

theorem globalCausalActionTracedMappedAdversaryImpl_step_isProbeQueryBoundP
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    ((globalCausalActionTracedMappedAdversaryImpl publicKey secretKey input).run
        |>.run state).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold globalCausalActionTracedMappedAdversaryImpl
  rw [QueryImpl.withTraceAppend_apply, WriterT.run_bind',
    WriterT.run_monadLift', StateT.run_bind]
  have hstep := globalCausalMappedAdversaryImpl_step_isProbeQueryBoundP
    publicKey secretKey input state
  have hbind := OracleComp.isQueryBoundP_bind
    (n := 0) (m := 0) hstep fun result _hresult =>
      OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery)
        ((result.1, attackerActionFragment input result.1), result.2) 0
  simpa [WriterT.run_tell] using hbind

theorem simulate_globalCausalActionTracedMappedAdversaryImpl_isProbeQueryBoundP
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (state : GlobalCausalHashState) :
    ((simulateQ
        (globalCausalActionTracedMappedAdversaryImpl publicKey secretKey)
        computation).run |>.run state).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result => simp [simulateQ_pure, WriterT.run_pure]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, WriterT.run_bind', StateT.run_bind]
      have hstep :=
        globalCausalActionTracedMappedAdversaryImpl_step_isProbeQueryBoundP
          publicKey secretKey input state
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0) hstep
      intro handled _hhandled
      apply (OracleComp.isQueryBoundP_map_iff _ _ 0).2
      exact ih handled.1.1 handled.2

theorem globalCausalDetailedGameAfterKeygen_run_isProbeQueryBoundP
    (adversary : Adversary Concrete.cappedScheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (state : GlobalCausalHashState) :
    (globalCausalDetailedGameAfterKeygen adversary publicKey secretKey).run
        state |>.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold globalCausalDetailedGameAfterKeygen
  rw [StateT.run_bind]
  have hadversary :=
    simulate_globalCausalActionTracedMappedAdversaryImpl_isProbeQueryBoundP
      publicKey secretKey (adversary.main publicKey) state
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0) hadversary
  intro handled _hhandled
  rw [StateT.run_bind]
  have hverify := simulate_globalCausalVerifierXmssRomImpl_isProbeQueryBoundP
    secretKey
    (Concrete.cappedScheme.verify publicKey handled.1.1.epoch
      handled.1.1.message handled.1.1.signature) handled.2
  have hbind := OracleComp.isQueryBoundP_bind
    (n := 0) (m := 0) hverify fun verified _hverified =>
      OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery)
        (((handled.1.1, verified.1), handled.1.2), verified.2) 0
  simpa using hbind

theorem globalCausalStrategyProgram_isProbeQueryBoundP
    (adversary : Adversary Concrete.cappedScheme) :
    (globalCausalStrategyProgram adversary).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold globalCausalStrategyProgram
  have hkeygen := simulate_globalCausalXmssRomImpl_isProbeQueryBoundP
    Concrete.keygen GlobalCausalHashState.empty
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0) hkeygen
  intro keyResult _hkeyResult
  have hexecution :=
    globalCausalDetailedGameAfterKeygen_run_isProbeQueryBoundP adversary
      keyResult.1.1 keyResult.1.2 keyResult.2.finishKeygen
  have hbind := OracleComp.isQueryBoundP_bind
    (n := 0) (m := 0) hexecution fun execution _hexecution =>
      OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery)
        (globalActionTracedRevealProbeView
          (globalCausalDetailedResult keyResult execution)).strategy 0
  simpa using hbind

end XmssSecurity.CappedChain
