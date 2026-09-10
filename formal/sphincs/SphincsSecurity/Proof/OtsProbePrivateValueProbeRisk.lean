import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrivateValueCompatibleRecords
import SphincsSecurity.Proof.OtsProbePrivateValueHistoryRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem probOutput_filter_some_of_predicate
    (run : ProbComp (Option α)) (predicate : α → Prop) (record : α) (hrecord : predicate record) :
    Pr[= some record | (fun result => result.filter (fun value => decide (predicate value))) <$> run] =
      Pr[= some record | run] := by
  apply probOutput_map_eq_single (some record)
  · intro result _ heq
    cases result with
    | none => simp at heq
    | some value =>
        by_cases hvalue : predicate value
        · simpa [Option.filter, hvalue] using heq
        · simp [Option.filter, hvalue] at heq
  · simp [Option.filter, hrecord]

theorem probOutput_runPrivateProbeRecords_eq_of_compatible
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (before after : HashOutput) (record : ResolvedRunResult (PrivateValueCut α))
    (hbefore : truncateHash before ∉ record.context.state.pendingAt (.position target))
    (hafter : truncateHash after ∉ record.context.state.pendingAt (.position target)) :
    Pr[= some record | runPrivateProbeRecords target computation context fuel table ordinal before] =
      Pr[= some record | runPrivateProbeRecords target computation context fuel table ordinal after] := by
  by_cases hsubset : context.state.pendingAt (.position target) ⊆ record.context.state.pendingAt (.position target)
  · have hcompatible : PrivateRecordCompatible target before after record := ⟨hbefore, hafter⟩
    have hdist := evalDist_runPrivateCompatibleRecords_preload_eq target before after
      (privatePositionProbeCutAt target computation ordinal) context fuel table ordinal hstate hhidden
      (fun hhit => hbefore (hsubset hhit)) (fun hhit => hafter (hsubset hhit))
      (privatePositionProbeCutAt_no_disclosure target computation ordinal)
      (privatePositionProbeCutAt_probe_bound target computation ordinal)
    simp only [runPrivateCompatibleRecords_eq_filter] at hdist
    have hprob := congrArg (fun distribution => distribution (some record)) hdist
    change Pr[= some record | (fun result => result.filter (fun value => decide (PrivateRecordCompatible target before after value))) <$>
        runPrivateProbeRecords target computation context fuel table ordinal before] =
      Pr[= some record | (fun result => result.filter (fun value => decide (PrivateRecordCompatible target before after value))) <$>
        runPrivateProbeRecords target computation context fuel table ordinal after] at hprob
    simpa only [probOutput_filter_some_of_predicate _ _ record hcompatible] using hprob
  · rw [probOutput_runPrivateProbeRecords_eq_zero_of_missing_initial_pending target computation context fuel table ordinal before
      hstate hhidden record hsubset,
      probOutput_runPrivateProbeRecords_eq_zero_of_missing_initial_pending target computation context fuel table ordinal after
        hstate hhidden record hsubset]

theorem probEvent_samplePrivateProbeRecords_hit_le_occurrence
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (candidate : ResolvedRunResult (PrivateValueCut α) → Option Digest)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (hcard : (context.state.pendingAt (.position target)).card + ordinal ≤ 2 ^ 126) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) |
      samplePrivateHistoryGuess (runPrivateProbeRecords target computation context fuel table ordinal) candidate] ≤
      Pr[fun pair => pair.2 ≠ none |
        samplePrivateHistoryGuess (runPrivateProbeRecords target computation context fuel table ordinal) candidate] *
          ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  apply probEvent_samplePrivateHistoryGuess_hit_le_of_supported_compatible _ candidate
    (fun record => record.context.state.pendingAt (.position target))
  · exact probOutput_runPrivateProbeRecords_eq_of_compatible target computation context fuel table ordinal hstate hhidden
  · intro output record hhit
    exact probOutput_runPrivateProbeRecords_eq_zero_of_history_hit target computation context fuel table ordinal output hstate hhidden record hhit
  · intro output record hrecord
    exact (runPrivateProbeRecords_supported_history target computation context fuel table ordinal output hstate hhidden record hrecord).2.1.trans hcard

noncomputable def privateProbeRecordCandidate (target : Position) (record : ResolvedRunResult (PrivateValueCut α)) : Option Digest :=
  (privatePositionAccessCandidate target (some record.value)).filter
    (fun digest => digest ∉ record.context.state.pendingAt (.position target))

theorem privatePositionCutCharge_probe_record_eq_indicator
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (output : HashOutput)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (record : Option (ResolvedRunResult (PrivateValueCut α)))
    (hrecord : record ∈ support (runPrivateProbeRecords target computation context fuel table ordinal output)) :
    privatePositionCutCharge target record = if record.bind (privateProbeRecordCandidate target) ≠ none then 1 else 0 := by
  cases record with
  | none => simp [privatePositionCutCharge]
  | some record =>
      obtain ⟨result, hresult, _, rfl⟩ := (mem_support_runPrivateRecords_iff target
        (replacePrivatePosition target output context) fuel table (privatePositionProbeCutAt target computation ordinal) record).mp hrecord
      have hinitial : PrivateTargetState target output (context.state.pendingAt (.position target))
          (replacePrivatePosition target output context) :=
        ⟨hstate, by simp [replacePrivatePosition, DeferredStructuralValues.install], hhidden, rfl⟩
      have hfinal := (privatePositionProbeCutAt_history_bound target output computation
        (replacePrivatePosition target output context) fuel table _ ordinal hinitial result hresult).1
      have herased : PrivateTargetState target 0 (result.context.state.pendingAt (.position target))
          (replacePrivateRunResult target 0 result).context :=
        ⟨hfinal.1, by simp [replacePrivateRunResult, replacePrivatePosition, DeferredStructuralValues.install], hfinal.2.2.1, rfl⟩
      simp only [privatePositionCutCharge, Option.bind_some, privateProbeRecordCandidate]
      cases hcandidate : privatePositionAccessCandidate target (some (replacePrivateRunResult target 0 result).value) with
      | none => simp
      | some digest =>
          dsimp only
          rw [herased.materializedCandidateCharge_eq]
          by_cases hmem : digest ∈ result.context.state.pendingAt (.position target) <;>
            simp [replacePrivateRunResult, replacePrivatePosition, hmem]

noncomputable def sampledPrivateProbeCharge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat) : ENNReal :=
  ∑' output, Pr[= output | LazyRevealProbe.sampleHashOutput] *
    ∑' record, Pr[= record | runPrivateProbeRecords target computation context fuel table ordinal output] * privatePositionCutCharge target record

theorem probEvent_samplePrivateProbeRecords_occurrence_eq_charge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed) :
    Pr[fun pair => pair.2 ≠ none | samplePrivateHistoryGuess
      (runPrivateProbeRecords target computation context fuel table ordinal) (privateProbeRecordCandidate target)] =
        sampledPrivateProbeCharge target computation context fuel table ordinal := by
  unfold samplePrivateHistoryGuess sampledPrivateProbeCharge
  rw [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro output
  congr 1
  rw [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro record
  by_cases hrecord : record ∈ support (runPrivateProbeRecords target computation context fuel table ordinal output)
  · rw [privatePositionCutCharge_probe_record_eq_indicator target computation context fuel table ordinal output hstate hhidden record hrecord]
    simp only [probEvent_pure]
  · simp [probOutput_eq_zero_of_not_mem_support hrecord]

theorem probEvent_samplePrivateProbeRecords_hit_le_charge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (hcard : (context.state.pendingAt (.position target)).card + ordinal ≤ 2 ^ 126) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) | samplePrivateHistoryGuess
      (runPrivateProbeRecords target computation context fuel table ordinal) (privateProbeRecordCandidate target)] ≤
        sampledPrivateProbeCharge target computation context fuel table ordinal *
          ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  rw [← probEvent_samplePrivateProbeRecords_occurrence_eq_charge target computation context fuel table ordinal hstate hhidden]
  exact probEvent_samplePrivateProbeRecords_hit_le_occurrence target computation context fuel table ordinal
    (privateProbeRecordCandidate target) hstate hhidden hcard

end SphincsSecurity.Concrete.OtsProbeSimulation
