import XmssSecurity.Proof.CappedGlobalCausalStrategyKeygenHybrid

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable def globalCausalSigningQueryAfterRealRom
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState) := do
  let signed ← RevealProbeOracleSimulation.liftProbComp
    ((simulateQ xmssRomImpl
      (Concrete.scheme.sign publicKey secretKey request.epoch request.message)).run
        state.cache)
  (revealGlobalSignatureOption secretKey request signed.1).run
    { state with cache := signed.2 }

theorem simulate_eagerTrace_globalCausalSigningQuery_eq_afterRealRom
    (table : GlobalChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((do
          let signature ← simulateQ globalCausalXmssRomImpl
            (Concrete.scheme.sign publicKey secretKey request.epoch
              request.message)
          revealGlobalSignatureOption secretKey request signature).run
            state)).run =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalCausalSigningQueryAfterRealRom
          publicKey secretKey request state)).run := by
  rw [StateT.run_bind, simulateQ_bind, WriterT.run_bind',
    simulate_eagerTrace_simulate_globalCausalXmssRomImpl_reconstruct]
  unfold globalCausalSigningQueryAfterRealRom
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]

noncomputable def globalCausalMappedAdversaryAfterRealRomImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input state =>
    match input with
    | .inl (.inl n) => (globalCausalUniformImpl n).run state
    | .inl (.inr hashInput) =>
        (globalCausalAttackerHashQuery secretKey hashInput).run state
    | .inr request =>
        globalCausalSigningQueryAfterRealRom
          publicKey secretKey request state

theorem simulate_eagerTrace_globalCausalMappedAdversaryImpl_step_eq_afterRealRom
    (table : GlobalChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalMappedAdversaryImpl publicKey secretKey input).run state) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalMappedAdversaryAfterRealRomImpl
          publicKey secretKey input).run state) := by
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput <;> rfl
  · apply WriterT.ext
    exact simulate_eagerTrace_globalCausalSigningQuery_eq_afterRealRom
      table publicKey secretKey request state

theorem simulate_eagerTrace_simulate_globalCausalMappedAdversaryImpl_eq_afterRealRom
    (table : GlobalChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalCausalHashState) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalCausalMappedAdversaryImpl publicKey secretKey)
          computation).run state) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalCausalMappedAdversaryAfterRealRomImpl
          publicKey secretKey) computation).run state) := by
  calc
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalCausalMappedAdversaryImpl publicKey secretKey)
          computation).run state) =
      (simulateQ
        ((RevealProbeOracleSimulation.eagerTraceImpl table).mapStateTBase
          (globalCausalMappedAdversaryAfterRealRomImpl publicKey secretKey))
        computation).run state :=
      simulateQ_StateT_compose
        (globalCausalMappedAdversaryImpl publicKey secretKey)
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((RevealProbeOracleSimulation.eagerTraceImpl table).mapStateTBase
          (globalCausalMappedAdversaryAfterRealRomImpl publicKey secretKey))
        (simulate_eagerTrace_globalCausalMappedAdversaryImpl_step_eq_afterRealRom
          table publicKey secretKey) computation state
    _ = simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalCausalMappedAdversaryAfterRealRomImpl
          publicKey secretKey) computation).run state) :=
      (QueryImpl.simulateQ_mapStateTBase_run
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalCausalMappedAdversaryAfterRealRomImpl publicKey secretKey)
        computation state).symm

noncomputable def globalCausalActionTracedMappedAdversaryAfterRealRomImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT AttackerActionTrace
        (StateT GlobalCausalHashState
          (OracleComp
            (RevealProbeOracleSimulation.World GlobalChainValueIndex)))) :=
  (globalCausalMappedAdversaryAfterRealRomImpl publicKey secretKey).withTraceAppend
    attackerActionFragment

theorem simulate_eagerTrace_globalCausalActionTracedMappedAdversaryImpl_step_eq_afterRealRom
    (table : GlobalChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((globalCausalActionTracedMappedAdversaryImpl
          publicKey secretKey input).run).run state) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((globalCausalActionTracedMappedAdversaryAfterRealRomImpl
          publicKey secretKey input).run).run state) := by
  unfold globalCausalActionTracedMappedAdversaryImpl
    globalCausalActionTracedMappedAdversaryAfterRealRomImpl
  rw [QueryImpl.withTraceAppend_apply, QueryImpl.withTraceAppend_apply,
    WriterT.run_bind', WriterT.run_bind', WriterT.run_monadLift',
    WriterT.run_monadLift', StateT.run_bind, StateT.run_bind,
    simulateQ_bind, simulateQ_bind, StateT.run_map, StateT.run_map,
    simulateQ_map, simulateQ_map,
    simulate_eagerTrace_globalCausalMappedAdversaryImpl_step_eq_afterRealRom]

theorem simulate_eagerTrace_simulate_globalCausalActionTracedMappedAdversaryImpl_eq_afterRealRom
    (table : GlobalChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalCausalHashState) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((simulateQ
          (globalCausalActionTracedMappedAdversaryImpl publicKey secretKey)
          computation).run).run state) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((simulateQ
          (globalCausalActionTracedMappedAdversaryAfterRealRomImpl
            publicKey secretKey) computation).run).run state) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, WriterT.run_bind', StateT.run_bind]
      rw [simulate_eagerTrace_globalCausalActionTracedMappedAdversaryImpl_step_eq_afterRealRom]
      apply bind_congr
      intro handled
      rw [StateT.run_map, StateT.run_map, simulateQ_map, simulateQ_map, ih]

noncomputable def globalCausalDetailedGameAfterKeygenAfterRealRom
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) :
    StateT GlobalCausalHashState
      (OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      ((Forgery × Bool) × AttackerActionTrace) := do
  let result ← (simulateQ
    (globalCausalActionTracedMappedAdversaryAfterRealRomImpl
      publicKey secretKey) (adversary.main publicKey)).run
  let verified ← simulateQ (globalCausalVerifierXmssRomImpl secretKey)
    (Concrete.scheme.verify publicKey result.1.epoch result.1.message
      result.1.signature)
  pure ((result.1, verified), result.2)

theorem simulate_eagerTrace_globalCausalDetailedGameAfterKeygen_eq_afterRealRom
    (table : GlobalChainValueIndex → Digest)
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (state : GlobalCausalHashState) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalDetailedGameAfterKeygen
          adversary publicKey secretKey).run state) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalDetailedGameAfterKeygenAfterRealRom
          adversary publicKey secretKey).run state) := by
  unfold globalCausalDetailedGameAfterKeygen
    globalCausalDetailedGameAfterKeygenAfterRealRom
  rw [StateT.run_bind, StateT.run_bind, simulateQ_bind, simulateQ_bind,
    simulate_eagerTrace_simulate_globalCausalActionTracedMappedAdversaryImpl_eq_afterRealRom]

noncomputable def globalCausalStrategyAfterRealKeygenAndSigning
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (List Bool → GlobalChainValueIndex × Digest) := do
  let causalKeyResult := globalCausalKeyResultOfReal keyResult
  let execution ← (globalCausalDetailedGameAfterKeygenAfterRealRom adversary
    causalKeyResult.1.1 causalKeyResult.1.2).run
      causalKeyResult.2.finishKeygen
  pure (globalActionTracedRevealProbeView
    (globalCausalDetailedResult causalKeyResult execution)).strategy

theorem simulate_eagerTrace_globalCausalStrategyAfterRealKeygen_eq_afterRealSigning
    (table : GlobalChainValueIndex → Digest)
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalCausalStrategyAfterRealKeygen adversary keyResult) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalCausalStrategyAfterRealKeygenAndSigning
          adversary keyResult) := by
  unfold globalCausalStrategyAfterRealKeygen
    globalCausalStrategyAfterRealKeygenAndSigning
  rw [simulateQ_bind, simulateQ_bind,
    simulate_eagerTrace_globalCausalDetailedGameAfterKeygen_eq_afterRealRom]

theorem simulate_eagerTrace_compileStrategyProbes_globalAfterRealKeygen_eq_afterRealSigning
    (table : GlobalChainValueIndex → Digest) (queries : Nat)
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (RevealProbeOracleSimulation.compileStrategyProbes queries
          (globalCausalStrategyAfterRealKeygen adversary keyResult)) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (RevealProbeOracleSimulation.compileStrategyProbes queries
          (globalCausalStrategyAfterRealKeygenAndSigning
            adversary keyResult)) := by
  unfold RevealProbeOracleSimulation.compileStrategyProbes
  rw [simulateQ_bind, simulateQ_bind,
    simulate_eagerTrace_globalCausalStrategyAfterRealKeygen_eq_afterRealSigning]

end XmssSecurity.CappedChain
