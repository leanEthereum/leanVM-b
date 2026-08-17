import XmssSecurity.CausalObservedMonitor
import XmssSecurity.CappedChain.CausalFilteredSimulator

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem simulate_eagerTrace_filteredCausalSigningAttempt_eq_original
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (filteredCausalSigningAttempt keyView selected request state)).run =
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (XmssSecurity.filteredCausalSigningQuery keyView selected request state)).run := by
  rfl

theorem simulate_eagerTrace_filteredCausalSigningAttempt_support_replays
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredCausalSigningAttempt keyView selected request state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  rw [simulate_eagerTrace_filteredCausalSigningAttempt_eq_original] at hresult
  exact XmssSecurity.simulate_eagerTrace_filteredCausalSigningQuery_support_replays
    table keyView selected request state result hresult

theorem simulate_eagerTrace_filteredCausalSignBoundedAttempts_support_replays
    (attempts : Nat) (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredCausalSignBoundedAttempts attempts keyView selected request
          state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  induction attempts generalizing state result with
  | zero =>
      simp only [filteredCausalSignBoundedAttempts, simulateQ_pure,
        WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ReplaysCausalReveals.nil state.revealed
  | succ attempts ih =>
      rw [simulate_eagerTrace_filteredCausalSignBoundedAttempts_succ,
        mem_support_bind_iff] at hresult
      obtain ⟨attemptResult, hattempt, hcontinuation⟩ := hresult
      have hreplayAttempt :=
        simulate_eagerTrace_filteredCausalSigningAttempt_support_replays table
          keyView selected request state attemptResult hattempt
      cases hoption : attemptResult.1.1 with
      | some signature =>
          unfold filteredCausalSignTraceContinuation at hcontinuation
          rw [hoption] at hcontinuation
          simp only [support_pure, Set.mem_singleton_iff] at hcontinuation
          subst result
          exact hreplayAttempt
      | none =>
          unfold filteredCausalSignTraceContinuation at hcontinuation
          rw [hoption, support_map] at hcontinuation
          obtain ⟨rest, hrest, rfl⟩ := hcontinuation
          exact hreplayAttempt.append
            (ih attemptResult.1.2 rest hrest)

theorem simulate_eagerTrace_filteredCausalSigningQuery_support_replays
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredCausalSigningQuery keyView selected request state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  unfold filteredCausalSigningQuery at hresult
  exact simulate_eagerTrace_filteredCausalSignBoundedAttempts_support_replays
    signingAttemptLimit table keyView selected request state result hresult

def CappedMonitoredFilteredStateRelation
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftCache : QueryCache HashSpec) (right : MonitoredCausalState) : Prop :=
  ∃ monitor,
    right.monitor = some monitor ∧
      RevealProbeOracleSimulation.StateAgrees table monitor ∧
      monitor.revealed = right.causal.revealed ∧
      FilteredCausalStateRelation parameter selected leftBase rightBase table
        leftCache right.causal

theorem relTriple_cappedMonitorCausalTrace_of_filtered_until_hit
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftComputation : ProbComp (α × QueryCache HashSpec))
    (rightComputation : CausalHashState → ProbComp
      ((α × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (rightState : MonitoredCausalState)
    (monitor : AdaptiveRevealMonitor.State ChainValueIndex)
    (hmonitor : rightState.monitor = some monitor)
    (hmonitorAgrees : RevealProbeOracleSimulation.StateAgrees table monitor)
    (hrevealed : monitor.revealed = rightState.causal.revealed)
    (hcouple : RelTriple leftComputation
      (rightComputation rightState.causal)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1.1 ∧
          FilteredCausalStateRelation parameter selected leftBase rightBase table
            leftResult.2 rightResult.1.2) ∨
          RevealProbeOracleSimulation.runObserved table monitor rightResult.2 =
            true))
    (htrace : ∀ result ∈ support (rightComputation rightState.causal),
      RevealProbeOracleSimulation.TraceAgrees table result.2 ∧
        ReplaysCausalReveals rightState.causal.revealed result.2
          result.1.2.revealed) :
    RelTriple leftComputation
      ((monitorCausalTrace table rightComputation).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          CappedMonitoredFilteredStateRelation parameter selected leftBase rightBase
            table leftResult.2 rightResult.2) ∨
          rightResult.2.bad) := by
  rw [monitorCausalTrace_run]
  have hmapped : RelTriple (id <$> leftComputation)
      (monitoredCausalResult table rightState <$>
        rightComputation rightState.causal)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          CappedMonitoredFilteredStateRelation parameter selected leftBase rightBase
            table leftResult.2 rightResult.2) ∨
          rightResult.2.bad) :=
    relTriple_map (f := id)
      (g := monitoredCausalResult table rightState)
      (relTriple_post_mono (relTriple_with_support hcouple)
      (fun leftResult rightResult hresult => by
        have htraceResult := htrace rightResult hresult.2.2
        rcases hresult.1 with hexact | hhit
        · cases hadvance : RevealProbeOracleSimulation.advanceObserved table
              monitor rightResult.2 with
          | none =>
              right
              change (rightState.monitor.bind fun current =>
                RevealProbeOracleSimulation.advanceObserved table current
                  rightResult.2) = none
              rw [hmonitor]
              exact hadvance
          | some finalMonitor =>
              left
              refine ⟨hexact.1, finalMonitor, ?_, ?_, ?_, hexact.2⟩
              · change (rightState.monitor.bind fun current =>
                    RevealProbeOracleSimulation.advanceObserved table current
                      rightResult.2) = some finalMonitor
                rw [hmonitor]
                exact hadvance
              · exact RevealProbeOracleSimulation.advanceObserved_preserves_stateAgrees
                  table monitor finalMonitor rightResult.2 hadvance
                    hmonitorAgrees
              · exact RevealProbeOracleSimulation.advanceObserved_preserves_replayed_reveals
                  table monitor finalMonitor rightState.causal.revealed
                    rightResult.1.2.revealed rightResult.2 hadvance
                      hmonitorAgrees hrevealed htraceResult.1 htraceResult.2
        · right
          change (rightState.monitor.bind fun current =>
            RevealProbeOracleSimulation.advanceObserved table current
              rightResult.2) = none
          rw [hmonitor]
          exact (RevealProbeOracleSimulation.advanceObserved_eq_none_iff_runObserved_eq_true
            table monitor rightResult.2).2 hhit))
  simpa only [id_map] using hmapped

theorem filteredCausalStateRelation_iff_original
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftBase rightBase : QueryCache HashSpec)
    (table : ChainValueIndex → Digest)
    (leftCache : QueryCache HashSpec) (rightState : CausalHashState) :
    FilteredCausalStateRelation parameter selected leftBase rightBase table
        leftCache rightState ↔
      XmssSecurity.FilteredCausalStateRelation parameter selected leftBase
        rightBase table leftCache rightState := by
  unfold FilteredCausalStateRelation
  unfold XmssSecurity.FilteredCausalStateRelation
  constructor
  · rintro ⟨hagrees, hfiltered, hle, hkeygen, hreveals⟩
    refine ⟨?_, ?_, hle, hkeygen, ?_⟩
    · intro input hinput
      apply hagrees input
      simpa [SigningComparableHashInput,
        XmssSecurity.SigningComparableHashInput] using hinput
    · intro input
      exact hfiltered input
    · intro index value hvalue
      exact hreveals index value hvalue
  · rintro ⟨hagrees, hfiltered, hle, hkeygen, hreveals⟩
    refine ⟨?_, ?_, hle, hkeygen, ?_⟩
    · intro input hinput
      apply hagrees input
      simpa [SigningComparableHashInput,
        XmssSecurity.SigningComparableHashInput] using hinput
    · intro input
      exact hfiltered input
    · intro index value hvalue
      exact hreveals index value hvalue

set_option maxRecDepth 100000 in
theorem relTriple_programmed_monitoredSigningQuery
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest))
    (hrel : ProgrammedActualKeygenStableRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1 ∈ support (actualFixedChainKeygen selected))
    (leftCache : QueryCache HashSpec) (rightState : MonitoredCausalState)
    (hstate : XmssSecurity.MonitoredFilteredStateRelation left.secretKey.parameter selected
      left.cache right.1.cache right.2 leftCache rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ xmssRomImpl
        (Concrete.scheme.sign left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey)
          request.epoch request.message)).run leftCache)
      ((monitorCausalTrace right.2 (fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
          (filteredCausalSigningQuery right.1 selected request
            causalState)).run)).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          XmssSecurity.MonitoredFilteredStateRelation left.secretKey.parameter selected
            left.cache right.1.cache right.2 leftResult.2 rightResult.2) ∨
          rightResult.2.bad) := by
  obtain ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal⟩ := hstate
  have hcausalLocal : FilteredCausalStateRelation left.secretKey.parameter
      selected left.cache right.1.cache right.2 leftCache rightState.causal := by
    exact (filteredCausalStateRelation_iff_original _ _ _ _ _ _ _).2 hcausal
  apply XmssSecurity.relTriple_monitorCausalTrace_of_filtered_until_hit
    (α := Option Signature) left.secretKey.parameter selected left.cache
      right.1.cache right.2 _ _ rightState monitor hmonitor hmonitorAgrees
        hrevealed
  · apply relTriple_post_mono
      (relTriple_programmed_filteredCausalSigningQuery selected left right hrel
        hleftSupport hrightSupport leftCache rightState.causal hcausalLocal request)
    intro leftResult rightResult hresult
    refine Or.inl ⟨hresult.1, ?_⟩
    exact (filteredCausalStateRelation_iff_original _ _ _ _ _ _ _).1 hresult.2
  · intro result hresult
    exact ⟨XmssSecurity.RevealProbeOracleSimulation.simulate_eagerTrace_support_traceAgrees
        right.2 _ result hresult,
      simulate_eagerTrace_filteredCausalSigningQuery_support_replays right.2
        right.1 selected request rightState.causal result hresult⟩

end XmssSecurity.CappedChain
