import XmssSecurity.Proof.CappedGlobalChainHighSigningMerkleRetention
import XmssSecurity.Proof.ObservedTraceMonitor

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

structure OnlineMonitoredCausalState where
  causal : GlobalCausalHashState
  monitor : Option
    (AdaptiveRevealMonitor.State GlobalChainValueIndex)

def OnlineMonitoredCausalState.bad
    (state : OnlineMonitoredCausalState) : Prop :=
  state.monitor = none

def onlineMonitoredCausalResult
    (table : GlobalChainValueIndex → Digest)
    (initial : OnlineMonitoredCausalState)
    (result : (α × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    α × OnlineMonitoredCausalState :=
  (result.1.1, {
    causal := result.1.2
    monitor := initial.monitor.bind fun monitor =>
      RevealProbeOracleSimulation.advanceObserved table monitor result.2
  })

noncomputable def monitorGlobalCausalOnline
    (table : GlobalChainValueIndex → Digest)
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    StateT OnlineMonitoredCausalState ProbComp α := fun state =>
  onlineMonitoredCausalResult table state <$> computation state.causal

theorem monitorGlobalCausalOnline_preserves_bad
    (table : GlobalChainValueIndex → Digest)
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (state : OnlineMonitoredCausalState)
    (hbad : state.bad)
    (result : α × OnlineMonitoredCausalState)
    (hresult : result ∈ support
      ((monitorGlobalCausalOnline table computation).run state)) :
    result.2.bad := by
  change state.monitor = none at hbad
  change result.2.monitor = none
  change result ∈ support
    (onlineMonitoredCausalResult table state <$> computation state.causal)
      at hresult
  rw [support_map] at hresult
  obtain ⟨raw, _hraw, rfl⟩ := hresult
  simp [onlineMonitoredCausalResult, hbad]

def OnlineMonitoredFilteredStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftCache : QueryCache HashSpec)
    (rightState : OnlineMonitoredCausalState) : Prop :=
  ∃ monitor, rightState.monitor = some monitor ∧
    RevealProbeOracleSimulation.StateAgrees right.2 monitor ∧
    monitor.revealed = rightState.causal.revealed ∧
    GlobalFilteredCausalStateRelation left right leftCache
      rightState.causal ∧
    GlobalMerkleKeygenCacheRetained right.1.secretKey rightState.causal

theorem onlineMonitoredFilteredStateRelation_initial
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
    OnlineMonitoredFilteredStateRelation left right leftCache
      ⟨rightState, some AdaptiveRevealMonitor.State.empty⟩ := by
  refine ⟨AdaptiveRevealMonitor.State.empty, rfl,
    RevealProbeOracleSimulation.stateAgrees_empty right.2, ?_, hstate,
      hretained⟩
  funext index
  simp [AdaptiveRevealMonitor.State.empty, hhidden index]

theorem relTriple_monitorGlobalCausalOnline_of_filtered_until_hit
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftComputation : ProbComp (α × QueryCache HashSpec))
    (rightComputation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (rightState : OnlineMonitoredCausalState)
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
      ((monitorGlobalCausalOnline right.2 rightComputation).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          OnlineMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨
          rightResult.2.bad) := by
  have hmapped : RelTriple (id <$> leftComputation)
      (onlineMonitoredCausalResult right.2 rightState <$>
        rightComputation rightState.causal)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          OnlineMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨
          rightResult.2.bad) :=
    relTriple_map (f := id)
      (g := onlineMonitoredCausalResult right.2 rightState)
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
  change RelTriple leftComputation
    (onlineMonitoredCausalResult right.2 rightState <$>
      rightComputation rightState.causal) _
  simpa only [id_map] using hmapped

end XmssSecurity.CappedChain
