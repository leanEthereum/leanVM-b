import XmssSecurity.CappedChain.CausalStrategyCoupling

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

abbrev CausalHashState := XmssSecurity.CausalHashState

def CausalHashState.empty : CausalHashState :=
  ⟨∅, ∅, fun _ => none, []⟩

def CausalHashState.finishKeygen (state : CausalHashState) : CausalHashState :=
  { state with keygenCache := state.cache }

def CausalHashState.recordProbe
    (state : CausalHashState) (probe : Option (ChainValueIndex × Digest)) :
    CausalHashState :=
  { state with probes :=
      match probe with
      | none => state.probes
      | some value => state.probes ++ [value] }

@[simp]
theorem CausalHashState.recordProbe_cache
    (state : CausalHashState)
    (probe : Option (ChainValueIndex × Digest)) :
    (state.recordProbe probe).cache = state.cache := by
  rfl

@[simp]
theorem CausalHashState.recordProbe_keygenCache
    (state : CausalHashState)
    (probe : Option (ChainValueIndex × Digest)) :
    (state.recordProbe probe).keygenCache = state.keygenCache := by
  rfl

@[simp]
theorem CausalHashState.recordProbe_revealed
    (state : CausalHashState)
    (probe : Option (ChainValueIndex × Digest)) :
    (state.recordProbe probe).revealed = state.revealed := by
  rfl

def CausalHashState.recordReveal
    (state : CausalHashState) (index : ChainValueIndex) (value : Digest) :
    CausalHashState :=
  { state with revealed := Function.update state.revealed index (some value) }

noncomputable def causalHashQuery
    (input : HashInput) :
    StateT CausalHashState
      (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)) HashOutput :=
  fun state =>
    (fun result : HashOutput × QueryCache HashSpec =>
      (result.1, { state with cache := result.2 })) <$>
        RevealProbeOracleSimulation.liftProbComp
          ((randomOracle input).run state.cache)

theorem causalHashQuery_run (input : HashInput) (state : CausalHashState) :
    (causalHashQuery input).run state =
      (fun result : HashOutput × QueryCache HashSpec =>
        (result.1, { state with cache := result.2 })) <$>
          RevealProbeOracleSimulation.liftProbComp
            ((randomOracle input).run state.cache) := rfl

abbrev CausalHashPlan := XmssSecurity.CausalHashPlan

noncomputable def causalLeafHashPlan
    (secretKey : SecretKey) (input : HashInput) (state : CausalHashState) :
    CausalHashPlan :=
  match state.keygenCache
      (keygenLeafTargetInput secretKey state.keygenCache input) with
  | some output => .redirect output
  | none => .fresh

noncomputable def causalUncachedAttackerHashPlan
    (secretKey : SecretKey) (input : HashInput) (state : CausalHashState) :
    Option (ChainValueIndex × Digest) → CausalHashPlan
  | some (index, target) =>
      match state.revealed index with
      | some value =>
          if value = target then
            if hnext : index.2.val + 1 < chainLength then
              .reveal (index.1, ⟨index.2.val + 1, hnext⟩)
            else causalLeafHashPlan secretKey input state
          else causalLeafHashPlan secretKey input state
      | none => causalLeafHashPlan secretKey input state
  | none => causalLeafHashPlan secretKey input state

noncomputable def causalAttackerHashPlan
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) : CausalHashPlan :=
  match state.cache input with
  | some output => .cached output
  | none => causalUncachedAttackerHashPlan secretKey input state
      (chainInputProbe? secretKey.parameter chain input)

@[irreducible]
noncomputable def causalRecordedState
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) : CausalHashState :=
  CausalHashState.recordProbe state
    (chainInputProbe? secretKey.parameter chain input)

@[simp]
theorem causalRecordedState_cache
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    (causalRecordedState secretKey chain input state).cache = state.cache := by
  rw [causalRecordedState]
  exact CausalHashState.recordProbe_cache state _

@[simp]
theorem causalRecordedState_keygenCache
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    (causalRecordedState secretKey chain input state).keygenCache =
      state.keygenCache := by
  rw [causalRecordedState]
  exact CausalHashState.recordProbe_keygenCache state _

@[simp]
theorem causalRecordedState_revealed
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    (causalRecordedState secretKey chain input state).revealed =
      state.revealed := by
  rw [causalRecordedState]
  exact CausalHashState.recordProbe_revealed state _

theorem causalHashState_recordProbe_eq_original
    (state : CausalHashState)
    (probe : Option (ChainValueIndex × Digest)) :
    CausalHashState.recordProbe state probe =
      XmssSecurity.CausalHashState.recordProbe state probe := by
  rfl

theorem causalRecordedState_eq_original
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    causalRecordedState secretKey chain input state =
      XmssSecurity.causalRecordedState secretKey chain input state := by
  rw [causalRecordedState, XmssSecurity.causalRecordedState]
  have hprobe : chainInputProbe? secretKey.parameter chain input =
      XmssSecurity.chainInputProbe? secretKey.parameter chain input := by rfl
  rw [hprobe]
  exact causalHashState_recordProbe_eq_original state _

noncomputable def causalRevealResultState
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) (value : Digest)
    (output : HashOutput) : CausalHashState :=
  { ((causalRecordedState secretKey chain input state).recordReveal
      index value) with
    cache := (causalRecordedState secretKey chain input state).cache.cacheQuery
      input output }

noncomputable def causalRevealHashQuery
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      (HashOutput × CausalHashState) := do
  let value ← RevealProbeOracleSimulation.revealQuery index
  let output ← RevealProbeOracleSimulation.liftProbComp
    (Rom.sampleHashOutputWithDigest value)
  pure (output, causalRevealResultState secretKey chain input state index value output)

noncomputable def causalAttackerHashQuery
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput) :
    StateT CausalHashState
      (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)) HashOutput :=
  fun state =>
    let recorded := causalRecordedState secretKey chain input state
    match causalAttackerHashPlan secretKey chain input state with
    | .cached output => pure (output, recorded)
    | .redirect output =>
        pure (output, { recorded with cache := recorded.cache.cacheQuery input output })
    | .fresh => (causalHashQuery input).run recorded
    | .reveal index => causalRevealHashQuery secretKey chain input state index

theorem causalAttackerHashQuery_run
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    (causalAttackerHashQuery secretKey chain input).run state =
      (let recorded := causalRecordedState secretKey chain input state
        match causalAttackerHashPlan secretKey chain input state with
        | .cached output => pure (output, recorded)
        | .redirect output =>
            pure (output,
              { recorded with cache := recorded.cache.cacheQuery input output })
        | .fresh => (causalHashQuery input).run recorded
        | .reveal index =>
            causalRevealHashQuery secretKey chain input state index) := rfl

noncomputable def causalHashImpl :
    QueryImpl HashSpec
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  causalHashQuery

noncomputable def causalXmssRomImpl :
    QueryImpl OracleWorld
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  causalUniformImpl + causalHashImpl

noncomputable def causalVerifierXmssRomImpl
    (secretKey : SecretKey) (chain : ChainIndex) :
    QueryImpl OracleWorld
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  causalUniformImpl + causalAttackerHashQuery secretKey chain

noncomputable def revealFixedChainSignatureOption
    (secretKey : SecretKey) (chain : ChainIndex) (request : SignRequest) :
    Option Signature →
      StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))
        (Option Signature)
  | none => pure none
  | some signature => fun state =>
      match TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash state.cache secretKey.parameter
            request.epoch (request.message, signature.randomness)) with
      | none => pure (some signature, state)
      | some encoding =>
          let index := (request.epoch, encoding chain)
          do
            let value ← RevealProbeOracleSimulation.revealQuery index
            pure (some (replaceSignatureChainValue signature chain value),
              state.recordReveal index value)

noncomputable def causalMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  fun input =>
    match input with
    | .inl (.inl n) => causalUniformImpl n
    | .inl (.inr hashInput) =>
        causalAttackerHashQuery secretKey chain hashInput
    | .inr request => do
        let signature ← simulateQ causalXmssRomImpl
          (Concrete.scheme.sign publicKey secretKey request.epoch request.message)
        revealFixedChainSignatureOption secretKey chain request signature

noncomputable def causalActionTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT AttackerActionTrace
        (StateT CausalHashState
          (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)))) :=
  (causalMappedAdversaryImpl publicKey secretKey chain).withTraceAppend
    attackerActionFragment

noncomputable def causalDetailedGameAfterKeygen
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex) :
    StateT CausalHashState
      (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))
      ((Forgery × Bool) × AttackerActionTrace) := do
  let result ← (simulateQ
    (causalActionTracedMappedAdversaryImpl publicKey secretKey chain)
      (adversary.main publicKey)).run
  let verified ← simulateQ (causalVerifierXmssRomImpl secretKey chain)
    (Concrete.scheme.verify publicKey result.1.epoch result.1.message
      result.1.signature)
  pure ((result.1, verified), result.2)

def causalDetailedResult
    (keyResult : (PublicKey × SecretKey) × CausalHashState)
    (execution : ((Forgery × Bool) × AttackerActionTrace) × CausalHashState) :
    DetailedActionTracedResult :=
  ((((keyResult.1, keyResult.2.cache),
      (actionTraceOutcome keyResult.1.1 keyResult.1.2 execution.1,
        execution.2.cache))), execution.1.2)

noncomputable def causalStrategyProgram
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      (List Bool → ChainValueIndex × Digest) := do
  let keyResult ← (simulateQ causalXmssRomImpl Concrete.keygen).run
    CausalHashState.empty
  let execution ← (causalDetailedGameAfterKeygen adversary keyResult.1.1
    keyResult.1.2 chain).run keyResult.2.finishKeygen
  pure (actionTracedRevealProbeView chain
    (causalDetailedResult keyResult execution)).strategy

theorem causalHashQuery_run_isProbeQueryBoundP
    (input : HashInput) (state : CausalHashState) :
    (causalHashQuery input).run state |>.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold causalHashQuery
  apply (OracleComp.isQueryBoundP_map_iff _ _ 0).2
  exact RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
    ((randomOracle input).run state.cache) 0

theorem causalUniformImpl_run_isProbeQueryBoundP
    (n : ℕ) (state : CausalHashState) :
    (causalUniformImpl n).run state |>.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold causalUniformImpl
  rw [OracleComp.liftM_run_StateT]
  have huniform :
      (RevealProbeOracleSimulation.uniformQuery
        (Index := ChainValueIndex) n).IsQueryBoundP
          RevealProbeOracleSimulation.IsProbeQuery 0 := by
    rw [RevealProbeOracleSimulation.uniformQuery,
      OracleComp.isQueryBoundP_query_iff]
    simp [RevealProbeOracleSimulation.IsProbeQuery]
  have hbind := OracleComp.isQueryBoundP_bind
    (n := 0) (m := 0) huniform fun result _hresult =>
      OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery) (result, state) 0
  simpa using hbind

theorem causalXmssRomImpl_step_isProbeQueryBoundP
    (input : OracleWorld.Domain) (state : CausalHashState) :
    (causalXmssRomImpl input).run state |>.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  cases input with
  | inl n =>
      exact causalUniformImpl_run_isProbeQueryBoundP n state
  | inr hashInput =>
      exact causalHashQuery_run_isProbeQueryBoundP hashInput state

theorem simulate_causalXmssRomImpl_isProbeQueryBoundP
    (computation : OracleComp OracleWorld α) (state : CausalHashState) :
    (simulateQ causalXmssRomImpl computation).run state |>.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  refine OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step
    (OracleComp.isQueryBoundP_false computation 0) ?_ state
  intro input currentState
  simpa using causalXmssRomImpl_step_isProbeQueryBoundP input currentState

theorem causalAttackerHashQuery_run_isProbeQueryBoundP
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    (causalAttackerHashQuery secretKey chain input).run state |>.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  rw [causalAttackerHashQuery_run]
  generalize hplan : causalAttackerHashPlan secretKey chain input state = plan
  cases plan with
  | cached output => simp
  | redirect output => simp
  | fresh =>
      exact causalHashQuery_run_isProbeQueryBoundP input
        (causalRecordedState secretKey chain input state)
  | reveal index =>
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP index 0)
      intro value _hvalue
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
          (Rom.sampleHashOutputWithDigest value) 0)
      intro output _houtput
      exact OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery) (output,
          { ((causalRecordedState secretKey chain input state).recordReveal
              index value) with
            cache := (causalRecordedState secretKey chain input state).cache.cacheQuery
              input output }) 0

theorem causalVerifierXmssRomImpl_step_isProbeQueryBoundP
    (secretKey : SecretKey) (chain : ChainIndex)
    (input : OracleWorld.Domain) (state : CausalHashState) :
    (causalVerifierXmssRomImpl secretKey chain input).run state
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  cases input with
  | inl n => exact causalUniformImpl_run_isProbeQueryBoundP n state
  | inr hashInput =>
      exact causalAttackerHashQuery_run_isProbeQueryBoundP secretKey chain
        hashInput state

theorem simulate_causalVerifierXmssRomImpl_isProbeQueryBoundP
    (secretKey : SecretKey) (chain : ChainIndex)
    (computation : OracleComp OracleWorld α) (state : CausalHashState) :
    (simulateQ (causalVerifierXmssRomImpl secretKey chain) computation).run
        state |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  refine OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step
    (OracleComp.isQueryBoundP_false computation 0) ?_ state
  intro input currentState
  simpa using causalVerifierXmssRomImpl_step_isProbeQueryBoundP secretKey chain
    input currentState

theorem revealFixedChainSignatureOption_run_isProbeQueryBoundP
    (secretKey : SecretKey) (chain : ChainIndex) (request : SignRequest)
    (signatureOption : Option Signature) (state : CausalHashState) :
    (revealFixedChainSignatureOption secretKey chain request signatureOption).run
        state |>.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  cases signatureOption with
  | none =>
      rw [revealFixedChainSignatureOption]
      exact OracleComp.isQueryBoundP_pure
        (spec := RevealProbeOracleSimulation.World ChainValueIndex)
        (p := RevealProbeOracleSimulation.IsProbeQuery) (none, state) 0
  | some signature =>
      rw [revealFixedChainSignatureOption]
      change (match TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash state.cache secretKey.parameter
            request.epoch (request.message, signature.randomness)) with
        | none => pure (some signature, state)
        | some encoding =>
            let index := (request.epoch, encoding chain)
            do
              let value ← RevealProbeOracleSimulation.revealQuery index
              pure (some (replaceSignatureChainValue signature chain value),
                state.recordReveal index value)
        ).IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0
      split
      · exact OracleComp.isQueryBoundP_pure
          (spec := RevealProbeOracleSimulation.World ChainValueIndex)
          (p := RevealProbeOracleSimulation.IsProbeQuery)
          (some signature, state) 0
      · rename_i encoding hdecode
        apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
          (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP
            (request.epoch, encoding chain) 0)
        intro value _hvalue
        exact OracleComp.isQueryBoundP_pure
          (p := RevealProbeOracleSimulation.IsProbeQuery)
          (some (replaceSignatureChainValue signature chain value),
            state.recordReveal (request.epoch, encoding chain) value) 0

theorem causalMappedAdversaryImpl_step_isProbeQueryBoundP
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    (causalMappedAdversaryImpl publicKey secretKey chain input).run state
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · exact causalUniformImpl_run_isProbeQueryBoundP n state
    · exact causalAttackerHashQuery_run_isProbeQueryBoundP
        secretKey chain hashInput state
  · unfold causalMappedAdversaryImpl
    rw [StateT.run_bind]
    have hsign := simulate_causalXmssRomImpl_isProbeQueryBoundP
      (Concrete.scheme.sign publicKey secretKey request.epoch request.message) state
    have hbind := OracleComp.isQueryBoundP_bind
      (n := 0) (m := 0) hsign fun result _hresult =>
        revealFixedChainSignatureOption_run_isProbeQueryBoundP secretKey chain
          request result.1 result.2
    simpa using hbind

theorem simulate_causalMappedAdversaryImpl_isProbeQueryBoundP
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState) :
    (simulateQ (causalMappedAdversaryImpl publicKey secretKey chain)
        computation).run state |>.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  refine OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step
    (OracleComp.isQueryBoundP_false computation 0) ?_ state
  intro input currentState
  simpa using causalMappedAdversaryImpl_step_isProbeQueryBoundP publicKey
    secretKey chain input currentState

theorem causalActionTracedMappedAdversaryImpl_step_isProbeQueryBoundP
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    ((causalActionTracedMappedAdversaryImpl publicKey secretKey chain input).run
        |>.run state).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold causalActionTracedMappedAdversaryImpl
  rw [QueryImpl.withTraceAppend_apply, WriterT.run_bind',
    WriterT.run_monadLift', StateT.run_bind]
  have hstep := causalMappedAdversaryImpl_step_isProbeQueryBoundP publicKey
    secretKey chain input state
  have hbind := OracleComp.isQueryBoundP_bind
    (n := 0) (m := 0) hstep fun result _hresult =>
      OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery)
        ((result.1, attackerActionFragment input result.1), result.2) 0
  simpa [WriterT.run_tell] using hbind

theorem simulate_causalActionTracedMappedAdversaryImpl_isProbeQueryBoundP
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState) :
    ((simulateQ
        (causalActionTracedMappedAdversaryImpl publicKey secretKey chain)
        computation).run |>.run state).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result =>
      simp [simulateQ_pure, WriterT.run_pure]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, WriterT.run_bind', StateT.run_bind]
      have hstep :=
        causalActionTracedMappedAdversaryImpl_step_isProbeQueryBoundP
          publicKey secretKey chain input state
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0) hstep
      intro handled _hhandled
      apply (OracleComp.isQueryBoundP_map_iff _ _ 0).2
      exact ih handled.1.1 handled.2

theorem causalDetailedGameAfterKeygen_run_isProbeQueryBoundP
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (state : CausalHashState) :
    (causalDetailedGameAfterKeygen adversary publicKey secretKey chain).run
        state |>.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold causalDetailedGameAfterKeygen
  rw [StateT.run_bind]
  have hadversary :=
    simulate_causalActionTracedMappedAdversaryImpl_isProbeQueryBoundP
      publicKey secretKey chain (adversary.main publicKey) state
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0) hadversary
  intro handled _hhandled
  rw [StateT.run_bind]
  have hverify := simulate_causalVerifierXmssRomImpl_isProbeQueryBoundP
    secretKey chain
    (Concrete.scheme.verify publicKey handled.1.1.epoch handled.1.1.message
      handled.1.1.signature) handled.2
  have hbind := OracleComp.isQueryBoundP_bind
    (n := 0) (m := 0) hverify fun verified _hverified =>
      OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery)
        (((handled.1.1, verified.1), handled.1.2), verified.2) 0
  simpa using hbind

theorem causalStrategyProgram_isProbeQueryBoundP
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    (causalStrategyProgram adversary chain).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold causalStrategyProgram
  have hkeygen := simulate_causalXmssRomImpl_isProbeQueryBoundP Concrete.keygen
    CausalHashState.empty
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0) hkeygen
  intro keyResult _hkeyResult
  have hexecution := causalDetailedGameAfterKeygen_run_isProbeQueryBoundP
    adversary keyResult.1.1 keyResult.1.2 chain keyResult.2.finishKeygen
  have hbind := OracleComp.isQueryBoundP_bind
    (n := 0) (m := 0) hexecution fun execution _hexecution =>
      OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery)
        (actionTracedRevealProbeView chain
          (causalDetailedResult keyResult execution)).strategy 0
  simpa using hbind


end XmssSecurity.CappedChain
