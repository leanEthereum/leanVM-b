import XmssSecurity.CausalStrategyKeygenHybrid

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable def causalSigningQueryAfterRealRom
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      (Option Signature × CausalHashState) := do
  let signed ← RevealProbeOracleSimulation.liftProbComp
    ((simulateQ xmssRomImpl
      (Concrete.singleAttemptScheme.sign publicKey secretKey request.epoch request.message)).run
        state.cache)
  (revealFixedChainSignatureOption secretKey chain request signed.1).run
    { state with cache := signed.2 }

theorem simulate_eagerTrace_causalSigningQuery_eq_afterRealRom
    (table : ChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((do
          let signature ← simulateQ causalXmssRomImpl
            (Concrete.singleAttemptScheme.sign publicKey secretKey request.epoch
              request.message)
          revealFixedChainSignatureOption secretKey chain request signature).run
            state)).run =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (causalSigningQueryAfterRealRom publicKey secretKey chain request state)).run := by
  rw [StateT.run_bind, simulateQ_bind, WriterT.run_bind',
    simulate_eagerTrace_simulate_causalXmssRomImpl_reconstruct]
  unfold causalSigningQueryAfterRealRom
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]

noncomputable def causalMappedAdversaryAfterRealRomImpl
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  fun input state =>
    match input with
    | .inl (.inl n) => (causalUniformImpl n).run state
    | .inl (.inr hashInput) =>
        (causalAttackerHashQuery secretKey chain hashInput).run state
    | .inr request =>
        causalSigningQueryAfterRealRom publicKey secretKey chain request state

theorem simulate_eagerTrace_causalMappedAdversaryImpl_step_eq_afterRealRom
    (table : ChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalMappedAdversaryImpl publicKey secretKey chain input).run state) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalMappedAdversaryAfterRealRomImpl
          publicKey secretKey chain input).run state) := by
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput <;> rfl
  · apply WriterT.ext
    exact simulate_eagerTrace_causalSigningQuery_eq_afterRealRom
      table publicKey secretKey chain request state

theorem simulate_eagerTrace_simulate_causalMappedAdversaryImpl_eq_afterRealRom
    (table : ChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (causalMappedAdversaryImpl publicKey secretKey chain)
          computation).run state) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (causalMappedAdversaryAfterRealRomImpl
          publicKey secretKey chain) computation).run state) := by
  calc
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (causalMappedAdversaryImpl publicKey secretKey chain)
          computation).run state) =
      (simulateQ
        ((RevealProbeOracleSimulation.eagerTraceImpl table).mapStateTBase
          (causalMappedAdversaryAfterRealRomImpl publicKey secretKey chain))
        computation).run state :=
      simulateQ_StateT_compose
        (causalMappedAdversaryImpl publicKey secretKey chain)
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((RevealProbeOracleSimulation.eagerTraceImpl table).mapStateTBase
          (causalMappedAdversaryAfterRealRomImpl publicKey secretKey chain))
        (simulate_eagerTrace_causalMappedAdversaryImpl_step_eq_afterRealRom
          table publicKey secretKey chain) computation state
    _ = simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (causalMappedAdversaryAfterRealRomImpl
          publicKey secretKey chain) computation).run state) :=
      (QueryImpl.simulateQ_mapStateTBase_run
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (causalMappedAdversaryAfterRealRomImpl publicKey secretKey chain)
        computation state).symm

noncomputable def causalActionTracedMappedAdversaryAfterRealRomImpl
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT AttackerActionTrace
        (StateT CausalHashState
          (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)))) :=
  (causalMappedAdversaryAfterRealRomImpl publicKey secretKey chain).withTraceAppend
    attackerActionFragment

theorem simulate_eagerTrace_causalActionTracedMappedAdversaryImpl_step_eq_afterRealRom
    (table : ChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((causalActionTracedMappedAdversaryImpl
          publicKey secretKey chain input).run).run state) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((causalActionTracedMappedAdversaryAfterRealRomImpl
          publicKey secretKey chain input).run).run state) := by
  unfold causalActionTracedMappedAdversaryImpl
    causalActionTracedMappedAdversaryAfterRealRomImpl
  rw [QueryImpl.withTraceAppend_apply, QueryImpl.withTraceAppend_apply,
    WriterT.run_bind', WriterT.run_bind', WriterT.run_monadLift',
    WriterT.run_monadLift', StateT.run_bind, StateT.run_bind,
    simulateQ_bind, simulateQ_bind, StateT.run_map, StateT.run_map,
    simulateQ_map, simulateQ_map,
    simulate_eagerTrace_causalMappedAdversaryImpl_step_eq_afterRealRom]

theorem simulate_eagerTrace_simulate_causalActionTracedMappedAdversaryImpl_eq_afterRealRom
    (table : ChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((simulateQ
          (causalActionTracedMappedAdversaryImpl publicKey secretKey chain)
          computation).run).run state) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((simulateQ
          (causalActionTracedMappedAdversaryAfterRealRomImpl
            publicKey secretKey chain) computation).run).run state) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, WriterT.run_bind', StateT.run_bind]
      rw [simulate_eagerTrace_causalActionTracedMappedAdversaryImpl_step_eq_afterRealRom]
      apply bind_congr
      intro handled
      rw [StateT.run_map, StateT.run_map, simulateQ_map, simulateQ_map, ih]

noncomputable def causalDetailedGameAfterKeygenAfterRealRom
    (adversary : Adversary Concrete.singleAttemptScheme)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex) :
    StateT CausalHashState
      (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))
      ((Forgery × Bool) × AttackerActionTrace) := do
  let result ← (simulateQ
    (causalActionTracedMappedAdversaryAfterRealRomImpl
      publicKey secretKey chain) (adversary.main publicKey)).run
  let verified ← simulateQ (causalVerifierXmssRomImpl secretKey chain)
    (Concrete.singleAttemptScheme.verify publicKey result.1.epoch result.1.message
      result.1.signature)
  pure ((result.1, verified), result.2)

theorem simulate_eagerTrace_causalDetailedGameAfterKeygen_eq_afterRealRom
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.singleAttemptScheme)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (state : CausalHashState) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalDetailedGameAfterKeygen adversary publicKey secretKey chain).run
          state) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalDetailedGameAfterKeygenAfterRealRom
          adversary publicKey secretKey chain).run state) := by
  unfold causalDetailedGameAfterKeygen
    causalDetailedGameAfterKeygenAfterRealRom
  rw [StateT.run_bind, StateT.run_bind, simulateQ_bind, simulateQ_bind,
    simulate_eagerTrace_simulate_causalActionTracedMappedAdversaryImpl_eq_afterRealRom]

noncomputable def causalStrategyAfterRealKeygenAndSigning
    (adversary : Adversary Concrete.singleAttemptScheme) (chain : ChainIndex)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      (List Bool → ChainValueIndex × Digest) := do
  let causalKeyResult := causalKeyResultOfReal keyResult
  let execution ← (causalDetailedGameAfterKeygenAfterRealRom adversary
    causalKeyResult.1.1 causalKeyResult.1.2 chain).run
      causalKeyResult.2.finishKeygen
  pure (actionTracedRevealProbeView chain
    (causalDetailedResult causalKeyResult execution)).strategy

theorem simulate_eagerTrace_causalStrategyAfterRealKeygen_eq_afterRealSigning
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.singleAttemptScheme) (chain : ChainIndex)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (causalStrategyAfterRealKeygen adversary chain keyResult) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (causalStrategyAfterRealKeygenAndSigning
          adversary chain keyResult) := by
  unfold causalStrategyAfterRealKeygen
    causalStrategyAfterRealKeygenAndSigning
  rw [simulateQ_bind, simulateQ_bind,
    simulate_eagerTrace_causalDetailedGameAfterKeygen_eq_afterRealRom]

theorem simulate_eagerTrace_compileStrategyProbes_afterRealKeygen_eq_afterRealSigning
    (table : ChainValueIndex → Digest) (queries : Nat)
    (adversary : Adversary Concrete.singleAttemptScheme) (chain : ChainIndex)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (RevealProbeOracleSimulation.compileStrategyProbes queries
          (causalStrategyAfterRealKeygen adversary chain keyResult)) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (RevealProbeOracleSimulation.compileStrategyProbes queries
          (causalStrategyAfterRealKeygenAndSigning
            adversary chain keyResult)) := by
  unfold RevealProbeOracleSimulation.compileStrategyProbes
  rw [simulateQ_bind, simulateQ_bind,
    simulate_eagerTrace_causalStrategyAfterRealKeygen_eq_afterRealSigning]

theorem simulate_eagerTrace_compileStrategyProbes_causalStrategyProgram_eq_afterRealKeygenAndSigning
    (table : ChainValueIndex → Digest) (queries : Nat)
    (adversary : Adversary Concrete.singleAttemptScheme) (chain : ChainIndex) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (RevealProbeOracleSimulation.compileStrategyProbes queries
          (causalStrategyProgram adversary chain))).run =
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅ >>= fun keyResult =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (RevealProbeOracleSimulation.compileStrategyProbes queries
            (causalStrategyAfterRealKeygenAndSigning
              adversary chain keyResult))).run) := by
  rw [simulate_eagerTrace_compileStrategyProbes_causalStrategyProgram_eq_afterRealKeygen]
  apply bind_congr
  intro keyResult
  rw [simulate_eagerTrace_compileStrategyProbes_afterRealKeygen_eq_afterRealSigning]

end XmssSecurity
