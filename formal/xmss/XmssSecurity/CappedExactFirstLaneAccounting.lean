import XmssSecurity.CappedExactFirstLaneCoupling
import XmssSecurity.CappedExactFirstLaneTransport
import XmssSecurity.CappedGlobalChainExpectedAccounting
import XmssSecurity.CappedGlobalChainHighBoundedCoupling
import XmssSecurity.CappedGlobalFirstLaneBounds

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000

def encodingQueryCount : EncodingActionTrace → Nat
  | [] => 0
  | .query _ _ :: rest => (encodingQueryCount rest).succ
  | .sign _ _ :: rest => encodingQueryCount rest

@[simp]
theorem encodingQueryCount_append
    (left right : EncodingActionTrace) :
    encodingQueryCount (left ++ right) =
      encodingQueryCount left + encodingQueryCount right := by
  induction left with
  | nil => simp [encodingQueryCount]
  | cons action rest ih =>
      cases action <;> simp [encodingQueryCount, ih, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc]

noncomputable def encodingActionCost (secretKey : SecretKey) :
    (OracleWorld + SigningSpec).Domain → Nat
  | .inl input =>
      if CappedEncodingMonitor.IsEncodingHashQuery
          secretKey.parameter input then 1 else 0
  | .inr _ => 0

theorem encodingActionTraceUpdate_queryCount_le
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : QueryCache HashSpec × SigningCacheTrace)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalState : QueryCache HashSpec × SigningCacheTrace)
    (trace : EncodingActionTrace) :
    encodingQueryCount
        (encodingActionTraceUpdate secretKey input initialState output
          finalState trace) ≤
      encodingQueryCount trace + encodingActionCost secretKey input := by
  classical
  rcases input with (worldInput | request)
  · rcases worldInput with uniformInput | hashInput
    · simp [encodingActionTraceUpdate, encodingObservation?,
        encodingActionCost]
    · by_cases hcache : initialState.1 hashInput = none
      · cases hepoch : encodingInputEpoch? secretKey.parameter hashInput with
        | none =>
            simp [encodingActionTraceUpdate, encodingObservation?,
              encodingActionCost, CappedEncodingMonitor.IsEncodingHashQuery,
              hcache, hepoch]
        | some epoch =>
            simp [encodingActionTraceUpdate, encodingObservation?,
              encodingActionCost, CappedEncodingMonitor.IsEncodingHashQuery,
              hcache, hepoch, encodingQueryCount]
      · simp [encodingActionTraceUpdate, encodingObservation?,
          encodingActionCost, CappedEncodingMonitor.IsEncodingHashQuery,
          hcache]
  · cases output with
    | none =>
        simp [encodingActionTraceUpdate, encodingObservation?,
          encodingActionCost]
    | some signature =>
        let hashInput := Concrete.CacheView.encodingInput
          secretKey.parameter request.epoch
          (request.message, signature.randomness)
        by_cases hinitial : initialState.1 hashInput = none
        · cases hfinal : finalState.1 hashInput with
          | none =>
              simp [encodingActionTraceUpdate, encodingObservation?,
                encodingActionCost, hashInput, hinitial, hfinal]
          | some hashOutput =>
              simp [encodingActionTraceUpdate, encodingObservation?,
                encodingActionCost, hashInput, hinitial, hfinal,
                encodingQueryCount]
        · simp [encodingActionTraceUpdate, encodingObservation?,
            encodingActionCost, hashInput, hinitial]

theorem encoding_add_globalChain_actionCost_le_direct
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) :
    encodingActionCost secretKey input +
        globalChainProbeActionCost secretKey input ≤
      directHashActionCost input := by
  rcases input with (worldInput | request)
  · rcases worldInput with uniformInput | hashInput
    · simp [encodingActionCost, globalChainProbeActionCost,
        directHashActionCost, CappedEncodingMonitor.IsEncodingHashQuery]
    · by_cases hencoding : CappedEncodingMonitor.IsEncodingHashQuery
          secretKey.parameter (.inr hashInput)
      · have hirrelevant : ¬GlobalChainProbeRelevantInput secretKey hashInput := by
          intro hrelevant
          exact encodingHashQuery_globalChainRelevant_disjoint secretKey
            (.inr hashInput) ⟨hencoding, by
              simpa [Rom.IsRelevantHashQuery] using hrelevant⟩
        simp [encodingActionCost, globalChainProbeActionCost,
          directHashActionCost, hencoding, hirrelevant]
      · simp only [encodingActionCost, globalChainProbeActionCost,
          directHashActionCost, hencoding, ↓reduceIte, zero_add]
        split <;> omega
  · simp [encodingActionCost, globalChainProbeActionCost,
      directHashActionCost]

noncomputable def globalHighExactRuntimeHazardCount
    (state : GlobalHighExactMonitoredState) : Nat :=
  encodingQueryCount state.2 +
    RevealProbeOracleSimulation.observedProbeCount state.1.1.trace

theorem globalHighExactMonitoredMappedAdversaryImpl_support_hazardCount_growth
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighExactMonitoredState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalHighExactMonitoredState)
    (hresult : result ∈ support
      ((globalHighExactMonitoredMappedAdversaryImpl right input).run state)) :
    globalHighExactRuntimeHazardCount result.2 ≤
      globalHighExactRuntimeHazardCount state + directHashActionCost input := by
  rw [globalHighExactMonitoredMappedAdversaryImpl_query_eq_map] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, hbase, hresultEq⟩ := hresult
  subst result
  have hencoding := encodingActionTraceUpdate_queryCount_le
    right.1.1.secretKey input (state.1.1.causal.cache, []) baseResult.1
      (baseResult.2.1.causal.cache, []) state.2
  have hchain :=
    globalHighMonitoredMappedAdversaryImpl_support_relevantProbeCount_growth
      right input state.1 baseResult hbase
  have hcost := encoding_add_globalChain_actionCost_le_direct
    right.1.1.secretKey input
  simp only [globalHighExactRuntimeHazardCount, globalHighExactQueryResult,
    Prod.fst, Prod.snd]
  omega

theorem globalFirstLaneExactTracedLift_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState
      (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : GlobalFirstLaneExactTracedState)
    (fuel : Nat)
    (hbase : (base.run state.causalState).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery fuel) :
    ((globalFirstLaneExactTracedLift keyView input base).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery fuel := by
  unfold globalFirstLaneExactTracedLift
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
    (state : GlobalFirstLaneExactTracedState) :
    ((globalFirstLaneExactTracedOracleImpl keyView edgeHigh input).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
        (if input matches .inr _ then 1 else 0) := by
  unfold globalFirstLaneExactTracedOracleImpl
  apply globalFirstLaneExactTracedLift_hazardBound
  exact globalFirstLaneOracleExecution_hazardBound keyView edgeHigh input
    state.causalState

theorem globalFirstLaneExactTracedSigningImpl_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest)
    (state : GlobalFirstLaneExactTracedState) :
    ((globalFirstLaneExactTracedSigningImpl keyView request).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 0 := by
  unfold globalFirstLaneExactTracedSigningImpl
  apply globalFirstLaneExactTracedLift_hazardBound
  exact globalFirstLaneSigningImpl_hazardBound keyView request
    state.causalState

theorem globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalFirstLaneExactTracedState) :
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
    (state : GlobalFirstLaneExactTracedState) :
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

theorem globalFirstLaneExactTracedAdversary_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalFirstLaneExactTracedState)
    (fuel : Nat)
    (hbound : computation.IsQueryBoundP
      (fun input => directHashActionCost input = 1) fuel) :
    ((simulateQ
      (globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh)
        computation).run state).IsQueryBoundP
          FirstLaneOracleSimulation.IsHazardQuery fuel := by
  apply OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step hbound
  intro input queryState
  have hstep := globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound
    keyView edgeHigh input queryState
  by_cases hcost : directHashActionCost input = 1
  · simpa [hcost] using hstep
  · have hzero : directHashActionCost input = 0 := by
      rcases input with (worldInput | request)
      · rcases worldInput with uniformInput | hashInput
        · rfl
        · exact (hcost rfl).elim
      · rfl
    simpa [hcost, hzero] using hstep

theorem globalFirstLaneExactTracedVerifier_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalFirstLaneExactTracedState)
    (fuel : Nat)
    (hbound : computation.IsQueryBoundP (· matches .inr _) fuel) :
    ((simulateQ (globalFirstLaneExactTracedVerifierImpl keyView edgeHigh)
      computation).run state).IsQueryBoundP
        FirstLaneOracleSimulation.IsHazardQuery fuel := by
  apply OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step hbound
  intro input queryState
  exact globalFirstLaneExactTracedVerifierImpl_hazardBound keyView edgeHigh
    input queryState

end XmssSecurity.CappedChain
