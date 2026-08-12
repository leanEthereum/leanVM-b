import XmssSecurity.CausalStrategyCoupling

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

structure CausalHashState where
  cache : QueryCache HashSpec
  probes : List (ChainValueIndex × Digest)

def CausalHashState.empty : CausalHashState :=
  ⟨∅, []⟩

def CausalHashState.recordProbe
    (state : CausalHashState) (probe : Option (ChainValueIndex × Digest)) :
    CausalHashState :=
  match probe with
  | none => state
  | some value => { state with probes := state.probes ++ [value] }

noncomputable def causalHashQuery
    (input : HashInput) :
    StateT CausalHashState
      (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)) HashOutput :=
  fun state =>
    (fun result : HashOutput × QueryCache HashSpec =>
      (result.1, { state with cache := result.2 })) <$>
        RevealProbeOracleSimulation.liftProbComp
          ((randomOracle input).run state.cache)

noncomputable def causalAttackerHashQuery
    (parameter : PublicParameter) (chain : ChainIndex) (input : HashInput) :
    StateT CausalHashState
      (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)) HashOutput :=
  fun state =>
    (fun result : HashOutput × QueryCache HashSpec =>
      (result.1,
        { (state.recordProbe (chainInputProbe? parameter chain input)) with
          cache := result.2 })) <$>
      RevealProbeOracleSimulation.liftProbComp
        ((randomOracle input).run state.cache)

noncomputable def causalHashImpl :
    QueryImpl HashSpec
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  causalHashQuery

def causalUniformImpl :
    QueryImpl unifSpec
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  fun n => liftM (RevealProbeOracleSimulation.uniformQuery
    (Index := ChainValueIndex) n)

noncomputable def causalXmssRomImpl :
    QueryImpl OracleWorld
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  causalUniformImpl + causalHashImpl

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
          (fun updated => (some updated, state)) <$>
            revealSignatureChainValue chain request.epoch encoding signature

noncomputable def causalMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  fun input =>
    match input with
    | .inl (.inl n) => causalUniformImpl n
    | .inl (.inr hashInput) =>
        causalAttackerHashQuery publicKey.parameter chain hashInput
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
  let verified ← simulateQ causalXmssRomImpl
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
    keyResult.1.2 chain).run keyResult.2
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
    (parameter : PublicParameter) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    (causalAttackerHashQuery parameter chain input).run state |>.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold causalAttackerHashQuery
  apply (OracleComp.isQueryBoundP_map_iff _ _ 0).2
  exact RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
    ((randomOracle input).run state.cache) 0

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
            (fun updated => (some updated, state)) <$>
              revealSignatureChainValue chain request.epoch encoding signature
        ).IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0
      split
      · exact OracleComp.isQueryBoundP_pure
          (spec := RevealProbeOracleSimulation.World ChainValueIndex)
          (p := RevealProbeOracleSimulation.IsProbeQuery)
          (some signature, state) 0
      · rename_i encoding hdecode
        apply (OracleComp.isQueryBoundP_map_iff _ _ 0).2
        exact revealSignatureChainValue_isProbeQueryBoundP chain request.epoch
          encoding signature

theorem causalMappedAdversaryImpl_step_isProbeQueryBoundP
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    (causalMappedAdversaryImpl publicKey secretKey chain input).run state
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · exact causalUniformImpl_run_isProbeQueryBoundP n state
    · exact causalAttackerHashQuery_run_isProbeQueryBoundP
        publicKey.parameter chain hashInput state
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
  have hverify := simulate_causalXmssRomImpl_isProbeQueryBoundP
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
    adversary keyResult.1.1 keyResult.1.2 chain keyResult.2
  have hbind := OracleComp.isQueryBoundP_bind
    (n := 0) (m := 0) hexecution fun execution _hexecution =>
      OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery)
        (actionTracedRevealProbeView chain
          (causalDetailedResult keyResult execution)).strategy 0
  simpa using hbind


end XmssSecurity
