import SphincsSecurity.Proof.JointProbeOriginalLiveValues
import SphincsSecurity.Proof.OtsProbeErasedRun
import SphincsSecurity.Proof.JointProbeInterpreterOrder

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (ResolvedRunResult HistoryResolvedPrefix)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

def JointHistoryReturned (event : α → Prop)
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (Option (HistoryResolvedPrefix α))) : Prop :=
  ∃ entry, cleanJointHistory result = some entry ∧ event entry.value

private theorem flattened_resolved_event (event : α → Prop) (result : Option (ResolvedRunResult (Option α))) :
    (∃ entry, flattenOptionalResolved result = some entry ∧ event entry.value) ↔
      ∃ value, OtsProbeSimulation.resolvedPrefixValue result = some (some value) ∧ event value := by
  cases result with
  | none => simp [flattenOptionalResolved, OtsProbeSimulation.resolvedPrefixValue]
  | some entry =>
      cases hv : entry.value <;> simp [flattenOptionalResolved, OtsProbeSimulation.resolvedPrefixValue, hv]

private theorem flattened_history_event (event : α → Prop) (result : Option (HistoryResolvedPrefix (Option α))) :
    (∃ entry, flattenOptionalHistory result = some entry ∧ event entry.value) ↔
      ∃ value, OtsProbeSimulation.historyPrefixValue result = some (some value) ∧ event value := by
  cases result with
  | none => simp [flattenOptionalHistory, OtsProbeSimulation.historyPrefixValue]
  | some entry =>
      cases hv : entry.value <;> simp [flattenOptionalHistory, OtsProbeSimulation.historyPrefixValue, hv]

theorem probEvent_sampled_jointReturned_le_erasedHistory
    (targets : Finset Position) (computation : OracleComp JointProbeWorld α) (event : α → Prop)
    (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel fuel : Nat) :
    (∑' otsTable, Pr[= otsTable | OtsProbeSimulation.sampleOtsHashTable] *
      Pr[JointReturned event | AdaptiveRevealProbe.runDetailed table state ftsFuel
        (runJointResolved computation (OtsProbeSimulation.ensuredInitialContext targets) fuel otsTable)]) ≤
      Pr[JointHistoryReturned event | AdaptiveRevealProbe.runDetailed table state ftsFuel
        (runJointErasedHistory computation (OtsProbeSimulation.ensuredInitialContext targets) 0 [])] := by
  have h := OtsProbeSimulation.probEvent_sampled_resolved_value_le_erased_history targets
    (runJointFts table computation state ftsFuel) fuel (fun output => ∃ value, output = some (some value) ∧ event value) (by simp)
  have hl (otsTable) : Pr[JointReturned event | AdaptiveRevealProbe.runDetailed table state ftsFuel
      (runJointResolved computation (OtsProbeSimulation.ensuredInitialContext targets) fuel otsTable)] =
      Pr[fun result => ∃ value, OtsProbeSimulation.resolvedPrefixValue result = some (some value) ∧ event value |
        OtsProbeSimulation.runResolvedFromTable (OtsProbeSimulation.ensuredInitialContext targets) fuel otsTable
          (runJointFts table computation state ftsFuel)] := by
    change Pr[(fun result : Option (ResolvedRunResult α) => ∃ entry, result = some entry ∧ event entry.value) ∘ cleanJointResolved | _] = _
    rw [← probEvent_map, runJointFts_resolved_commute, probEvent_map]
    exact probEvent_congr' (fun result _ => flattened_resolved_event event result) rfl
  have hr : Pr[JointHistoryReturned event | AdaptiveRevealProbe.runDetailed table state ftsFuel
      (runJointErasedHistory computation (OtsProbeSimulation.ensuredInitialContext targets) 0 [])] =
      Pr[fun result => ∃ value, OtsProbeSimulation.historyPrefixValue result = some (some value) ∧ event value |
        OtsProbeSimulation.runResolvedHistoryPrefix (OtsProbeSimulation.eraseProbeQueries (runJointFts table computation state ftsFuel))
          (OtsProbeSimulation.ensuredInitialContext targets) 0 []] := by
    change Pr[(fun result : Option (HistoryResolvedPrefix α) => ∃ entry, result = some entry ∧ event entry.value) ∘ cleanJointHistory | _] = _
    rw [← probEvent_map, runJointFts_erasedHistory_commute, probEvent_map]
    exact probEvent_congr' (fun result _ => flattened_history_event event result) rfl
  simp_rw [hl, hr]
  exact h

end SphincsSecurity.Concrete.FtsProbeSimulation
