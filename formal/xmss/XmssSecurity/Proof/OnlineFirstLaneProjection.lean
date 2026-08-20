import XmssSecurity.Proof.OnlineFirstLaneGame
import XmssSecurity.Proof.CappedExactFirstLaneEager
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000

def onlineFirstLaneStateOfExact
    (state : GlobalExactTracedState) : GlobalHighDirectTracedState :=
  (state.causalState, state.attackerTrace)

theorem globalExactTracedLift_projects
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : GlobalExactTracedState) :
    Prod.map id onlineFirstLaneStateOfExact <$>
        (globalExactTracedLift keyView input base).run state =
      (onlineFirstLaneLift input base).run
        (onlineFirstLaneStateOfExact state) := by
  simp [globalExactTracedLift, globalExactTracedNextState,
    onlineFirstLaneLift, onlineFirstLaneStateOfExact,
    map_eq_bind_pure_comp]

theorem onlineFirstLaneMappedAdversaryImpl_projects_uniform
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (n : Nat)
    (state : GlobalExactTracedState) :
    Prod.map id onlineFirstLaneStateOfExact <$>
        (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
          (.inl (.inl n))).run state =
      (onlineFirstLaneMappedAdversaryImpl keyView edgeHigh
        (.inl (.inl n))).run
        (onlineFirstLaneStateOfExact state) := by
  unfold globalFirstLaneExactTracedMappedAdversaryImpl
    globalFirstLaneExactTracedOracleImpl onlineFirstLaneMappedAdversaryImpl
  simp only [QueryImpl.add_apply]
  rw [globalExactTracedLift_projects]
  rfl

theorem onlineFirstLaneMappedAdversaryImpl_projects_hash
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (hashInput : HashInput)
    (state : GlobalExactTracedState) :
    Prod.map id onlineFirstLaneStateOfExact <$>
        (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
          (.inl (.inr hashInput))).run state =
      (onlineFirstLaneMappedAdversaryImpl keyView edgeHigh
        (.inl (.inr hashInput))).run
          (onlineFirstLaneStateOfExact state) := by
  unfold globalFirstLaneExactTracedMappedAdversaryImpl
    globalFirstLaneExactTracedOracleImpl onlineFirstLaneMappedAdversaryImpl
  simp only [QueryImpl.add_apply]
  rw [globalExactTracedLift_projects]
  rfl

theorem onlineFirstLaneMappedAdversaryImpl_projects_sign
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (request : SignRequest)
    (state : GlobalExactTracedState) :
    Prod.map id onlineFirstLaneStateOfExact <$>
        (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
          (.inr request)).run state =
      (onlineFirstLaneMappedAdversaryImpl keyView edgeHigh (.inr request)).run
        (onlineFirstLaneStateOfExact state) := by
  unfold globalFirstLaneExactTracedMappedAdversaryImpl
      globalFirstLaneExactTracedSigningImpl
      onlineFirstLaneMappedAdversaryImpl
  simp only [QueryImpl.add_apply]
  rw [globalExactTracedLift_projects]

theorem onlineFirstLaneMappedAdversaryImpl_projects
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalExactTracedState) :
    Prod.map id onlineFirstLaneStateOfExact <$>
        (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh input
          ).run state =
      (onlineFirstLaneMappedAdversaryImpl keyView edgeHigh input).run
        (onlineFirstLaneStateOfExact state) := by
  rcases input with (worldInput | request)
  · rcases worldInput with n | hashInput
    · exact onlineFirstLaneMappedAdversaryImpl_projects_uniform keyView
        edgeHigh n state
    · exact onlineFirstLaneMappedAdversaryImpl_projects_hash keyView
        edgeHigh hashInput state
  · exact onlineFirstLaneMappedAdversaryImpl_projects_sign keyView edgeHigh
      request state

theorem onlineFirstLaneVerifierImpl_projects
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (state : GlobalExactTracedState) :
    Prod.map id onlineFirstLaneStateOfExact <$>
        (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run
          state =
      (onlineFirstLaneVerifierImpl keyView edgeHigh input).run
        (onlineFirstLaneStateOfExact state) := by
  simp [globalFirstLaneExactTracedVerifierImpl,
    onlineFirstLaneVerifierImpl, onlineFirstLaneStateOfExact,
    Functor.map_map]

theorem onlineFirstLane_adversary_projects
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (state : GlobalExactTracedState) :
    Prod.map id onlineFirstLaneStateOfExact <$>
        (simulateQ
          (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh)
          (adversary.main keyView.publicKey)).run state =
      (simulateQ (onlineFirstLaneMappedAdversaryImpl keyView edgeHigh)
        (adversary.main keyView.publicKey)).run
          (onlineFirstLaneStateOfExact state) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh)
    (onlineFirstLaneMappedAdversaryImpl keyView edgeHigh)
    onlineFirstLaneStateOfExact
    (onlineFirstLaneMappedAdversaryImpl_projects keyView edgeHigh)
    (adversary.main keyView.publicKey) state

theorem onlineFirstLane_verifier_projects
    (computation : OracleComp OracleWorld α)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (state : GlobalExactTracedState) :
    Prod.map id onlineFirstLaneStateOfExact <$>
        (simulateQ (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
          computation).run state =
      (simulateQ (onlineFirstLaneVerifierImpl keyView edgeHigh)
        computation).run (onlineFirstLaneStateOfExact state) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
    (onlineFirstLaneVerifierImpl keyView edgeHigh)
    onlineFirstLaneStateOfExact
    (onlineFirstLaneVerifierImpl_projects keyView edgeHigh)
    computation state

theorem onlineFirstLaneVerification_projects
    (forgery : Forgery)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (state : GlobalExactTracedState) :
    Prod.map id onlineFirstLaneStateOfExact <$> (do
        let verified ← (simulateQ
          (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey forgery.epoch
            forgery.message forgery.signature)).run state
        let finalTrace := appendVerificationEncodingObservation keyView.secretKey
          forgery state.causalState.cache verified.2.causalState.cache
            verified.2.encodingTrace
        pure ((forgery, verified.1),
          { verified.2 with encodingTrace := finalTrace })) = (do
        let verified ← (simulateQ
          (onlineFirstLaneVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey forgery.epoch
            forgery.message forgery.signature)).run
              (onlineFirstLaneStateOfExact state)
        pure ((forgery, verified.1), verified.2)) := by
  let finishExact := fun verified : Bool × GlobalExactTracedState =>
    ((forgery, verified.1), onlineFirstLaneStateOfExact verified.2)
  let finishOnline := fun verified : Bool × GlobalHighDirectTracedState =>
    ((forgery, verified.1), verified.2)
  simp only [map_bind, map_pure]
  change finishExact <$> (simulateQ
      (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
      (Concrete.scheme.verify keyView.publicKey forgery.epoch
        forgery.message forgery.signature)).run state =
    finishOnline <$> (simulateQ
      (onlineFirstLaneVerifierImpl keyView edgeHigh)
      (Concrete.scheme.verify keyView.publicKey forgery.epoch
        forgery.message forgery.signature)).run
          (onlineFirstLaneStateOfExact state)
  rw [← onlineFirstLane_verifier_projects
    (Concrete.scheme.verify keyView.publicKey forgery.epoch
      forgery.message forgery.signature) keyView edgeHigh state]
  simp [finishExact, finishOnline, Functor.map_map,
    onlineFirstLaneStateOfExact]

theorem onlineFirstLaneDetailedExecution_projects
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (state : GlobalExactTracedState) :
    Prod.map id onlineFirstLaneStateOfExact <$>
        (globalFirstLaneExactTracedDetailedExecution adversary keyView
          edgeHigh).run state =
      (onlineFirstLaneDetailedExecution adversary keyView edgeHigh).run
        (onlineFirstLaneStateOfExact state) := by
  unfold globalFirstLaneExactTracedDetailedExecution
    onlineFirstLaneDetailedExecution
  simp only [StateT.run_mk]
  let exactAdversary := (simulateQ
    (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh)
      (adversary.main keyView.publicKey)).run state
  let onlineAdversary := (simulateQ
    (onlineFirstLaneMappedAdversaryImpl keyView edgeHigh)
      (adversary.main keyView.publicKey)).run
        (onlineFirstLaneStateOfExact state)
  let onlineTail := fun handled : Forgery × GlobalHighDirectTracedState => do
    let verified ← (simulateQ
      (onlineFirstLaneVerifierImpl keyView edgeHigh)
      (Concrete.scheme.verify keyView.publicKey handled.1.epoch
        handled.1.message handled.1.signature)).run handled.2
    pure ((handled.1, verified.1), verified.2)
  calc
    _ = exactAdversary >>= fun handled =>
        onlineTail (handled.1, onlineFirstLaneStateOfExact handled.2) := by
      rw [map_bind]
      apply bind_congr
      intro handled
      exact onlineFirstLaneVerification_projects handled.1 keyView edgeHigh
        handled.2
    _ = (Prod.map id onlineFirstLaneStateOfExact <$> exactAdversary) >>=
        onlineTail := by
      rw [bind_map_left]
      simp [onlineTail, Prod.map]
    _ = onlineAdversary >>= onlineTail := by
      rw [onlineFirstLane_adversary_projects adversary keyView edgeHigh state]
    _ = _ := by rfl

def onlineFirstLaneResultOfExact
    (result : GlobalExactTracedResult) : OnlineFirstLaneResult :=
  (result.1, Prod.map id onlineFirstLaneStateOfExact result.2)

theorem onlineFirstLaneCoreProgram_projects
    (adversary : Adversary) :
    onlineFirstLaneResultOfExact <$>
        globalFirstLaneExactTracedProgram adversary =
      onlineFirstLaneCoreProgram adversary := by
  unfold globalFirstLaneExactTracedProgram onlineFirstLaneCoreProgram
  simp only [map_bind]
  apply bind_congr
  intro keyResult
  have hprojection := onlineFirstLaneDetailedExecution_projects adversary
    keyResult.1 keyResult.2 (GlobalExactTracedState.initial
      (globalFilteredCausalKeygenState keyResult.1))
  have hmapped := congrArg
    (fun computation => (fun execution => (keyResult, execution)) <$>
      computation) hprojection
  simpa [onlineFirstLaneResultOfExact, Functor.map_map,
    Function.comp_def, onlineFirstLaneStateOfExact] using hmapped

theorem onlineFirstLaneForgeryProbes_projection
    (result : GlobalExactTracedResult) :
    onlineFirstLaneForgeryProbes (onlineFirstLaneResultOfExact result) =
      globalHighDirectExactForgeryPrimaryProbeTrace result := by
  rfl

theorem onlineFirstLaneProgram_projects
    (adversary : Adversary) :
    onlineFirstLaneResultOfExact <$>
        globalFirstLaneExactTracedPublicProgram adversary =
      onlineFirstLaneProgram adversary := by
  unfold globalFirstLaneExactTracedPublicProgram onlineFirstLaneProgram
  let tail := fun result : OnlineFirstLaneResult => do
    let _ ← globalFirstLaneLiftRevealProbe
      (RevealProbeOracleSimulation.emitObservedTrace
        (onlineFirstLaneForgeryProbes result))
    pure result
  have hprojection := onlineFirstLaneCoreProgram_projects adversary
  have hbound := congrArg (fun computation => computation >>= tail) hprojection
  simpa [tail, bind_map_left, onlineFirstLaneForgeryProbes_projection]
    using hbound

theorem FirstLaneOracleSimulation.onlineExperiment_map
    (fuel : Nat) (project : α → β)
    (computation : OracleComp (FirstLaneOracleSimulation.World Index) α)
    [Fintype Index] [DecidableEq Index] :
    FirstLaneOracleSimulation.onlineExperiment fuel
        (project <$> computation) =
      FirstLaneOracleSimulation.onlineExperiment fuel computation := by
  unfold FirstLaneOracleSimulation.onlineExperiment
  apply bind_congr
  intro table
  rw [simulateQ_map]
  simp only [StateT.run_map, ExceptT.run_map, Functor.map_map]
  apply congrArg (fun observe => observe <$>
    ((simulateQ (FirstLaneOracleSimulation.onlineImpl table) computation).run
      (FirstLaneOracleSimulation.OnlineState.empty fuel)).run)
  funext result
  cases result <;> rfl

theorem FirstLaneOracleSimulation.enforceHazardBound_map
    (fuel : Nat) (project : α → β)
    (computation : OracleComp (FirstLaneOracleSimulation.World Index) α)
    [Fintype Index] [DecidableEq Index] :
    FirstLaneOracleSimulation.enforceHazardBound fuel
        (project <$> computation) =
      project <$> FirstLaneOracleSimulation.enforceHazardBound fuel
        computation := by
  unfold FirstLaneOracleSimulation.enforceHazardBound
  rw [simulateQ_map]
  simp [StateT.run_map, Functor.map_map]

theorem onlineFirstLaneExperiment_eq_exact
    (fuel : Nat) (adversary : Adversary) :
    onlineFirstLaneExperiment fuel adversary =
      FirstLaneOracleSimulation.onlineExperiment fuel
        (globalFirstLaneExactTracedPublicProgram adversary) := by
  unfold onlineFirstLaneExperiment
  rw [← onlineFirstLaneProgram_projects adversary]
  exact FirstLaneOracleSimulation.onlineExperiment_map fuel
    onlineFirstLaneResultOfExact
      (globalFirstLaneExactTracedPublicProgram adversary)

theorem enforcedOnlineFirstLaneExperiment_eq_exact
    (fuel : Nat) (adversary : Adversary) :
    enforcedOnlineFirstLaneExperiment fuel adversary =
      FirstLaneOracleSimulation.onlineExperiment fuel
        (FirstLaneOracleSimulation.enforceHazardBound fuel
          (globalFirstLaneExactTracedPublicProgram adversary)) := by
  unfold enforcedOnlineFirstLaneExperiment
  rw [← onlineFirstLaneProgram_projects adversary,
    FirstLaneOracleSimulation.enforceHazardBound_map]
  exact FirstLaneOracleSimulation.onlineExperiment_map fuel
    onlineFirstLaneResultOfExact
      (FirstLaneOracleSimulation.enforceHazardBound fuel
        (globalFirstLaneExactTracedPublicProgram adversary))

end XmssSecurity.CappedChain
