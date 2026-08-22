import XmssSecurity.Proof.CappedGlobalChainHighSigningMerkleRetention
import XmssSecurity.Proof.ObservedTraceMonitor

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000

structure GlobalMonitoredCausalState where
  causal : GlobalCausalHashState
  trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex

def GlobalMonitoredCausalState.observed
    (table : GlobalChainValueIndex → Digest)
    (state : GlobalMonitoredCausalState) :
    Option (AdaptiveRevealMonitor.State GlobalChainValueIndex) :=
  RevealProbeOracleSimulation.advanceObserved table
    AdaptiveRevealMonitor.State.empty state.trace

def GlobalMonitoredCausalState.bad
    (table : GlobalChainValueIndex → Digest)
    (state : GlobalMonitoredCausalState) : Prop :=
  state.observed table = none

def globalMonitoredCausalResult
    (initial : GlobalMonitoredCausalState)
    (result : (α × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    α × GlobalMonitoredCausalState :=
  (result.1.1, {
    causal := result.1.2
    trace := initial.trace ++ result.2
  })

theorem GlobalMonitoredCausalState.bad_implies_runObserved
    (table : GlobalChainValueIndex → Digest)
    (state : GlobalMonitoredCausalState)
    (hbad : state.bad table) :
    RevealProbeOracleSimulation.runObserved table
      AdaptiveRevealMonitor.State.empty state.trace = true := by
  apply (RevealProbeOracleSimulation.advanceObserved_eq_none_iff_runObserved_eq_true
    table AdaptiveRevealMonitor.State.empty state.trace).1
  exact hbad

noncomputable def monitorGlobalCausalTrace
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    StateT GlobalMonitoredCausalState ProbComp α := fun state =>
  globalMonitoredCausalResult state <$> computation state.causal

theorem monitorGlobalCausalTrace_run
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (state : GlobalMonitoredCausalState) :
    (monitorGlobalCausalTrace computation).run state =
      globalMonitoredCausalResult state <$> computation state.causal :=
  rfl

def GlobalMonitoredFilteredStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftCache : QueryCache HashSpec)
    (rightState : GlobalMonitoredCausalState) : Prop :=
  ∃ monitor, rightState.observed right.2 = some monitor ∧
    RevealProbeOracleSimulation.StateAgrees right.2 monitor ∧
    monitor.revealed = rightState.causal.revealed ∧
    GlobalFilteredCausalStateRelation left right leftCache
      rightState.causal ∧
    GlobalMerkleKeygenCacheRetained right.1.secretKey rightState.causal

theorem globalMonitoredFilteredStateRelation_initial
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftCache : QueryCache HashSpec)
    (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right leftCache
      rightState)
    (hretained : GlobalMerkleKeygenCacheRetained right.1.secretKey
      rightState)
    (hhidden : ∀ index, rightState.revealed index = none) :
    GlobalMonitoredFilteredStateRelation left right leftCache
      ⟨rightState, []⟩ := by
  have hnoHit : ¬ ∃ index, right.2 index ∈
      (AdaptiveRevealMonitor.State.empty :
        AdaptiveRevealMonitor.State GlobalChainValueIndex).pending index := by
    simp [AdaptiveRevealMonitor.State.empty]
  refine ⟨AdaptiveRevealMonitor.State.empty, ?_,
    RevealProbeOracleSimulation.stateAgrees_empty right.2, ?_, hstate,
      hretained⟩
  · simp [GlobalMonitoredCausalState.observed,
      RevealProbeOracleSimulation.advanceObserved,
      RevealProbeOracleSimulation.tableHits, hnoHit]
  funext index
  simp [AdaptiveRevealMonitor.State.empty, hhidden index]

theorem globalFilteredCausalRevealResultState_transition
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (value : Digest) (output : HashOutput) :
    CausalRevealTransition state.revealed index value
      (globalFilteredCausalRevealResultState secretKey input state index value
        output).revealed := by
  constructor
  · simp [globalFilteredCausalRevealResultState]
  · intro candidate hne
    simp [globalFilteredCausalRevealResultState,
      Function.update_of_ne hne]

theorem relTriple_monitorGlobalCausalTrace_of_filtered_until_hit
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftComputation : ProbComp (α × QueryCache HashSpec))
    (rightComputation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (rightState : GlobalMonitoredCausalState)
    (monitor : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (hmonitor : rightState.observed right.2 = some monitor)
    (hmonitorAgrees : RevealProbeOracleSimulation.StateAgrees right.2 monitor)
    (hrevealed : monitor.revealed = rightState.causal.revealed)
    (hcouple : RelTriple leftComputation
      (rightComputation rightState.causal)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1.1 ∧
          GlobalFilteredCausalStateRelation left right leftResult.2
            rightResult.1.2) ∨
          RevealProbeOracleSimulation.runObserved right.2 monitor
            rightResult.2 = true))
    (htrace : ∀ result ∈ support (rightComputation rightState.causal),
      RevealProbeOracleSimulation.TraceAgrees right.2 result.2 ∧
        ReplaysCausalReveals rightState.causal.revealed result.2
          result.1.2.revealed)
    (hretainedStep : ∀ result ∈ support
      (rightComputation rightState.causal),
      GlobalMerkleKeygenCacheRetained right.1.secretKey result.1.2) :
    RelTriple leftComputation
      ((monitorGlobalCausalTrace rightComputation).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨
          rightResult.2.bad right.2) := by
  rw [monitorGlobalCausalTrace_run]
  change RevealProbeOracleSimulation.advanceObserved right.2
    AdaptiveRevealMonitor.State.empty rightState.trace = some monitor
      at hmonitor
  have hmapped : RelTriple (id <$> leftComputation)
      (globalMonitoredCausalResult rightState <$>
        rightComputation rightState.causal)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨
          rightResult.2.bad right.2) :=
    relTriple_map (f := id)
      (g := globalMonitoredCausalResult rightState)
      (relTriple_post_mono (relTriple_with_support hcouple)
      (fun leftResult rightResult hresult => by
        have htraceResult := htrace rightResult hresult.2.2
        have hretainedResult := hretainedStep rightResult hresult.2.2
        rcases hresult.1 with hexact | hhit
        · cases hadvance : RevealProbeOracleSimulation.advanceObserved right.2
              monitor rightResult.2 with
          | none =>
              right
              change RevealProbeOracleSimulation.advanceObserved right.2
                AdaptiveRevealMonitor.State.empty
                  (rightState.trace ++ rightResult.2) = none
              rw [RevealProbeOracleSimulation.advanceObserved_append,
                hmonitor]
              exact hadvance
          | some finalMonitor =>
              left
              refine ⟨hexact.1, finalMonitor, ?_, ?_, ?_, hexact.2,
                hretainedResult⟩
              · change RevealProbeOracleSimulation.advanceObserved right.2
                    AdaptiveRevealMonitor.State.empty
                      (rightState.trace ++ rightResult.2) = some finalMonitor
                rw [RevealProbeOracleSimulation.advanceObserved_append,
                  hmonitor]
                exact hadvance
              · exact RevealProbeOracleSimulation.advanceObserved_preserves_stateAgrees
                  right.2 monitor finalMonitor rightResult.2 hadvance
                    hmonitorAgrees
              · exact RevealProbeOracleSimulation.advanceObserved_preserves_replayed_reveals
                  right.2 monitor finalMonitor rightState.causal.revealed
                    rightResult.1.2.revealed rightResult.2 hadvance
                      hmonitorAgrees hrevealed htraceResult.1 htraceResult.2
        · right
          change RevealProbeOracleSimulation.advanceObserved right.2
            AdaptiveRevealMonitor.State.empty
              (rightState.trace ++ rightResult.2) = none
          rw [RevealProbeOracleSimulation.advanceObserved_append, hmonitor]
          exact (RevealProbeOracleSimulation.advanceObserved_eq_none_iff_runObserved_eq_true
            right.2 monitor rightResult.2).2 hhit))
  simpa only [id_map] using hmapped

end XmssSecurity.CappedChain
