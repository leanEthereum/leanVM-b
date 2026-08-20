import XmssSecurity.Proof.CappedExactFirstLaneTransport
import XmssSecurity.Proof.CappedChain.DirectQueryAccounting

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000

theorem globalExactTracedLift_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState
      (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : GlobalExactTracedState)
    (fuel : Nat)
    (hbase : (base.run state.causalState).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery fuel) :
    ((globalExactTracedLift keyView input base).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery fuel := by
  unfold globalExactTracedLift
  simp only [StateT.run_mk]
  rw [map_eq_bind_pure_comp]
  apply OracleComp.isQueryBoundP_bind (n := fuel) (m := 0) hbase
  intro result _hresult
  exact OracleComp.isQueryBoundP_pure
    (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0

theorem globalFirstLaneExactTracedOracleImpl_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (state : GlobalExactTracedState) :
    ((globalFirstLaneExactTracedOracleImpl keyView edgeHigh input).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
        (if input matches .inr _ then 1 else 0) := by
  unfold globalFirstLaneExactTracedOracleImpl
  apply globalExactTracedLift_hazardBound
  exact globalFirstLaneOracleExecution_hazardBound keyView edgeHigh input
    state.causalState

theorem globalFirstLaneExactTracedSigningImpl_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest)
    (state : GlobalExactTracedState) :
    ((globalFirstLaneExactTracedSigningImpl keyView request).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 0 := by
  unfold globalFirstLaneExactTracedSigningImpl
  apply globalExactTracedLift_hazardBound
  exact globalFirstLaneSigningImpl_hazardBound keyView request
    state.causalState

theorem globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalExactTracedState) :
    ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh input).run
      state).IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
        (directHashActionCost input) := by
  rcases input with (worldInput | request)
  · rcases worldInput with uniformInput | hashInput
    · unfold globalFirstLaneExactTracedMappedAdversaryImpl
      simpa [directHashActionCost] using
        globalFirstLaneExactTracedOracleImpl_hazardBound keyView edgeHigh
          (.inl uniformInput) state
    · unfold globalFirstLaneExactTracedMappedAdversaryImpl
      simpa [directHashActionCost] using
        globalFirstLaneExactTracedOracleImpl_hazardBound keyView edgeHigh
          (.inr hashInput) state
  · unfold globalFirstLaneExactTracedMappedAdversaryImpl
    simpa [directHashActionCost] using
      globalFirstLaneExactTracedSigningImpl_hazardBound keyView request state

theorem globalFirstLaneExactTracedVerifierImpl_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (state : GlobalExactTracedState) :
    ((globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
        (if input matches .inr _ then 1 else 0) := by
  rw [globalFirstLaneExactTracedVerifierImpl_run_eq_map]
  rw [map_eq_bind_pure_comp]
  apply OracleComp.isQueryBoundP_bind
    (n := if input matches .inr _ then 1 else 0) (m := 0)
    (globalFirstLaneOracleImpl_hazardBound keyView edgeHigh input
      state.causalState)
  intro result _hresult
  exact OracleComp.isQueryBoundP_pure
    (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0

end XmssSecurity.CappedChain
