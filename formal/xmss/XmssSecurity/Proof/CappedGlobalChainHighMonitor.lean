import XmssSecurity.Proof.CappedGlobalChainHighSigningMerkleRetention
import XmssSecurity.Proof.ObservedTraceMonitor

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

structure GlobalMonitoredCausalState where
  causal : GlobalCausalHashState
  monitor : Option
    (AdaptiveRevealMonitor.State GlobalChainValueIndex)
  trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex

def GlobalMonitoredCausalState.bad
    (state : GlobalMonitoredCausalState) : Prop :=
  state.monitor = none

def GlobalMonitoredCausalState.TraceConsistent
    (table : GlobalChainValueIndex → Digest)
    (state : GlobalMonitoredCausalState) : Prop :=
  state.monitor = RevealProbeOracleSimulation.advanceObserved table
    AdaptiveRevealMonitor.State.empty state.trace

def globalMonitoredCausalResult
    (table : GlobalChainValueIndex → Digest)
    (initial : GlobalMonitoredCausalState)
    (result : (α × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    α × GlobalMonitoredCausalState :=
  (result.1.1, {
    causal := result.1.2
    monitor := initial.monitor.bind fun monitor =>
      RevealProbeOracleSimulation.advanceObserved table monitor result.2
    trace := initial.trace ++ result.2
  })

theorem globalMonitoredCausalResult_traceConsistent
    (table : GlobalChainValueIndex → Digest)
    (initial : GlobalMonitoredCausalState)
    (result : (α × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hinitial : initial.TraceConsistent table) :
    (globalMonitoredCausalResult table initial result).2.TraceConsistent
      table := by
  unfold GlobalMonitoredCausalState.TraceConsistent at hinitial ⊢
  change (initial.monitor.bind fun monitor =>
      RevealProbeOracleSimulation.advanceObserved table monitor result.2) =
    RevealProbeOracleSimulation.advanceObserved table
      AdaptiveRevealMonitor.State.empty (initial.trace ++ result.2)
  rw [hinitial, RevealProbeOracleSimulation.advanceObserved_append]

theorem globalMonitoredCausalState_initial_traceConsistent
    (table : GlobalChainValueIndex → Digest)
    (causal : GlobalCausalHashState) :
    GlobalMonitoredCausalState.TraceConsistent table
      ⟨causal, some AdaptiveRevealMonitor.State.empty, []⟩ := by
  simp [GlobalMonitoredCausalState.TraceConsistent,
    RevealProbeOracleSimulation.advanceObserved,
    RevealProbeOracleSimulation.tableHits,
    AdaptiveRevealMonitor.State.empty]

theorem GlobalMonitoredCausalState.bad_implies_runObserved
    (table : GlobalChainValueIndex → Digest)
    (state : GlobalMonitoredCausalState)
    (hconsistent : state.TraceConsistent table)
    (hbad : state.bad) :
    RevealProbeOracleSimulation.runObserved table
      AdaptiveRevealMonitor.State.empty state.trace = true := by
  apply (RevealProbeOracleSimulation.advanceObserved_eq_none_iff_runObserved_eq_true
    table AdaptiveRevealMonitor.State.empty state.trace).1
  rw [← hconsistent]
  exact hbad

noncomputable def monitorGlobalCausalTrace
    (table : GlobalChainValueIndex → Digest)
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    StateT GlobalMonitoredCausalState ProbComp α := fun state =>
  globalMonitoredCausalResult table state <$> computation state.causal

theorem monitorGlobalCausalTrace_run
    (table : GlobalChainValueIndex → Digest)
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (state : GlobalMonitoredCausalState) :
    (monitorGlobalCausalTrace table computation).run state =
      globalMonitoredCausalResult table state <$> computation state.causal :=
  rfl

theorem monitorGlobalCausalTrace_preserves_bad
    (table : GlobalChainValueIndex → Digest)
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (state : GlobalMonitoredCausalState) (hbad : state.bad)
    (result : α × GlobalMonitoredCausalState)
    (hresult : result ∈ support
      ((monitorGlobalCausalTrace table computation).run state)) :
    result.2.bad := by
  rw [monitorGlobalCausalTrace_run, support_map] at hresult
  obtain ⟨raw, _hraw, rfl⟩ := hresult
  change state.monitor.bind _ = none
  rw [hbad]
  rfl

theorem monitorGlobalCausalTrace_preserves_traceConsistent
    (table : GlobalChainValueIndex → Digest)
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (state : GlobalMonitoredCausalState)
    (hconsistent : state.TraceConsistent table)
    (result : α × GlobalMonitoredCausalState)
    (hresult : result ∈ support
      ((monitorGlobalCausalTrace table computation).run state)) :
    result.2.TraceConsistent table := by
  rw [monitorGlobalCausalTrace_run, support_map] at hresult
  obtain ⟨raw, _hraw, rfl⟩ := hresult
  exact globalMonitoredCausalResult_traceConsistent table state raw hconsistent

def GlobalMonitoredFilteredStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftCache : QueryCache HashSpec)
    (rightState : GlobalMonitoredCausalState) : Prop :=
  ∃ monitor, rightState.monitor = some monitor ∧
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
      ⟨rightState, some AdaptiveRevealMonitor.State.empty, []⟩ := by
  refine ⟨AdaptiveRevealMonitor.State.empty, rfl,
    RevealProbeOracleSimulation.stateAgrees_empty right.2, ?_, hstate,
      hretained⟩
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
    (hmonitor : rightState.monitor = some monitor)
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
      ((monitorGlobalCausalTrace right.2 rightComputation).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨
          rightResult.2.bad) := by
  rw [monitorGlobalCausalTrace_run]
  have hmapped : RelTriple (id <$> leftComputation)
      (globalMonitoredCausalResult right.2 rightState <$>
        rightComputation rightState.causal)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨
          rightResult.2.bad) :=
    relTriple_map (f := id)
      (g := globalMonitoredCausalResult right.2 rightState)
      (relTriple_post_mono (relTriple_with_support hcouple)
      (fun leftResult rightResult hresult => by
        have htraceResult := htrace rightResult hresult.2.2
        have hretainedResult := hretainedStep rightResult hresult.2.2
        rcases hresult.1 with hexact | hhit
        · cases hadvance : RevealProbeOracleSimulation.advanceObserved right.2
              monitor rightResult.2 with
          | none =>
              right
              change (rightState.monitor.bind fun current =>
                RevealProbeOracleSimulation.advanceObserved right.2 current
                  rightResult.2) = none
              rw [hmonitor]
              exact hadvance
          | some finalMonitor =>
              left
              refine ⟨hexact.1, finalMonitor, ?_, ?_, ?_, hexact.2,
                hretainedResult⟩
              · change (rightState.monitor.bind fun current =>
                    RevealProbeOracleSimulation.advanceObserved right.2 current
                      rightResult.2) = some finalMonitor
                rw [hmonitor]
                exact hadvance
              · exact RevealProbeOracleSimulation.advanceObserved_preserves_stateAgrees
                  right.2 monitor finalMonitor rightResult.2 hadvance
                    hmonitorAgrees
              · exact RevealProbeOracleSimulation.advanceObserved_preserves_replayed_reveals
                  right.2 monitor finalMonitor rightState.causal.revealed
                    rightResult.1.2.revealed rightResult.2 hadvance
                      hmonitorAgrees hrevealed htraceResult.1 htraceResult.2
        · right
          change (rightState.monitor.bind fun current =>
            RevealProbeOracleSimulation.advanceObserved right.2 current
              rightResult.2) = none
          rw [hmonitor]
          exact (RevealProbeOracleSimulation.advanceObserved_eq_none_iff_runObserved_eq_true
            right.2 monitor rightResult.2).2 hhit))
  simpa only [id_map] using hmapped

end XmssSecurity.CappedChain
