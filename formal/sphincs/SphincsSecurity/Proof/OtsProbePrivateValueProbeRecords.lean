import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeHistoryLiveRisk
import SphincsSecurity.Proof.OtsProbePrivateValueProbeHistory

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def privateRecordedResult (target : Position) (result : Option (ResolvedRunResult α)) :
    Option (ResolvedRunResult α) :=
  (retainCompletableResult result).map (replacePrivateRunResult target 0)

noncomputable def runPrivateRecords
    (target : Position) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) : ProbComp (Option (ResolvedRunResult α)) :=
  privateRecordedResult target <$> runResolvedFromTable context fuel table computation

theorem mem_support_runPrivateRecords_iff
    (target : Position) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (record : ResolvedRunResult α) :
    some record ∈ support (runPrivateRecords target context fuel table computation) ↔
      ∃ result, some result ∈ support (runResolvedFromTable context fuel table computation) ∧
        DeferredCompletable result.table result.context ∧ record = replacePrivateRunResult target 0 result := by
  unfold runPrivateRecords
  rw [support_map, Set.mem_image]
  constructor
  · rintro ⟨result, hresult, heq⟩
    cases result with
    | none => simp [privateRecordedResult, retainCompletableResult] at heq
    | some result =>
        by_cases hcomplete : DeferredCompletable result.table result.context
        · simp only [privateRecordedResult, retainCompletableResult, if_pos hcomplete, Option.map_some, Option.some.injEq] at heq
          exact ⟨result, hresult, hcomplete, heq.symm⟩
        · simp [privateRecordedResult, retainCompletableResult, hcomplete] at heq
  · rintro ⟨result, hresult, hcomplete, rfl⟩
    exact ⟨some result, hresult, by simp [privateRecordedResult, retainCompletableResult, hcomplete]⟩

noncomputable def runPrivateProbeRecords
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (output : HashOutput) :
    ProbComp (Option (ResolvedRunResult (PrivateValueCut α))) :=
  runPrivateRecords target (replacePrivatePosition target output context) fuel table (privatePositionProbeCutAt target computation ordinal)

theorem runPrivateProbeRecords_supported_history
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (output : HashOutput)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (record : ResolvedRunResult (PrivateValueCut α))
    (hrecord : some record ∈ support (runPrivateProbeRecords target computation context fuel table ordinal output)) :
    context.state.pendingAt (.position target) ⊆ record.context.state.pendingAt (.position target) ∧
      (record.context.state.pendingAt (.position target)).card ≤ (context.state.pendingAt (.position target)).card + ordinal ∧
      truncateHash output ∉ record.context.state.pendingAt (.position target) := by
  obtain ⟨result, hresult, hcomplete, rfl⟩ := (mem_support_runPrivateRecords_iff target
    (replacePrivatePosition target output context) fuel table (privatePositionProbeCutAt target computation ordinal) record).mp hrecord
  have hinitial : PrivateTargetState target output (context.state.pendingAt (.position target))
      (replacePrivatePosition target output context) :=
    ⟨hstate, by simp [replacePrivatePosition, DeferredStructuralValues.install], hhidden, rfl⟩
  have hhistory := privatePositionProbeCutAt_history_bound target output computation
    (replacePrivatePosition target output context) fuel table _ ordinal hinitial result hresult
  refine ⟨hhistory.2.1, hhistory.2.2, ?_⟩
  obtain ⟨completion, hcompletion⟩ := hcomplete
  have houtput := hcompletion.2.1 target output hhistory.1.2.1
  intro hhit
  change truncateHash output ∈ result.context.state.pendingAt (.position target) at hhit
  have hpending := (LazyRevealProbe.State.mem_pendingAt_iff result.context.state (.position target) (truncateHash output)).mp hhit
  exact hcompletion.2.2.1 (.position target) (truncateHash output) hpending (by rw [houtput])

theorem probOutput_runPrivateProbeRecords_eq_zero_of_history_hit
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (output : HashOutput)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (record : ResolvedRunResult (PrivateValueCut α)) (hhit : truncateHash output ∈ record.context.state.pendingAt (.position target)) :
    Pr[= some record | runPrivateProbeRecords target computation context fuel table ordinal output] = 0 := by
  apply probOutput_eq_zero_of_not_mem_support
  intro hrecord
  exact (runPrivateProbeRecords_supported_history target computation context fuel table ordinal output hstate hhidden record hrecord).2.2 hhit

theorem probOutput_runPrivateProbeRecords_eq_zero_of_missing_initial_pending
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (output : HashOutput)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (record : ResolvedRunResult (PrivateValueCut α))
    (hmissing : ¬context.state.pendingAt (.position target) ⊆ record.context.state.pendingAt (.position target)) :
    Pr[= some record | runPrivateProbeRecords target computation context fuel table ordinal output] = 0 := by
  apply probOutput_eq_zero_of_not_mem_support
  intro hrecord
  exact hmissing (runPrivateProbeRecords_supported_history target computation context fuel table ordinal output hstate hhidden record hrecord).1

end SphincsSecurity.Concrete.OtsProbeSimulation
