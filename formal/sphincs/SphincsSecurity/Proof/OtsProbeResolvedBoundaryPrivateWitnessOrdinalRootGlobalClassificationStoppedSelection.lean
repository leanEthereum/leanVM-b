import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedSample
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionBoundary

/-!
# Selected stopped snapshots as ordinal selections

The stopped structural marker contains exactly the candidate-time data read by the ordinal
selection experiment. This file packages that deterministic projection before the root and
non-root probability branches are coupled.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def PrivateOrdinalSelection.GoodForActualRoot
    (target : Position) (output : HashOutput) (ordinal : Nat)
    (selection : PrivateOrdinalSelection) : Prop :=
  selection.candidate = ⟨.position target, truncateHash output⟩ ∧
    selection.context.state.values (.position target) = none ∧
    Coordinate.position target ∉ selection.context.state.revealed ∧
    selection.context.values target = some output ∧
    CandidatesAvoidRoot target (truncateHash output)
      (selection.candidates.take ordinal)

theorem PrivateOrdinalSelection.GoodForActualRoot.goodForRoots
    {selection : PrivateOrdinalSelection} {target : Position}
    {output : HashOutput} {rightRoot : Digest} {ordinal : Nat}
    (hactual : selection.GoodForActualRoot target output ordinal)
    (hright : CandidatesAvoidRoot target rightRoot
      (selection.candidates.take ordinal)) :
    selection.GoodForRoots target output rightRoot ordinal := by
  refine ⟨hactual.1, hactual.2.1, hactual.2.2.1, hactual.2.2.2.1, ?_⟩
  intro candidate hcandidate
  exact ⟨hactual.2.2.2.2 candidate hcandidate, hright candidate hcandidate⟩

theorem selectedPrivateSnapshotOrdinal?_goodForActualRoot
    {source : PrivateWitnessSnapshotOutput} {ordinal : Nat}
    (hhit : SelectedPrivateSnapshotHitAt source ordinal) :
    ∃ selected : Fin source.2.length, ∃ target output,
      selected.val = ordinal ∧
      selectedPrivateSnapshotOrdinal? ordinal source.2 =
        some (privateOrdinalSelectionOfSnapshot selected) ∧
      (privateOrdinalSelectionOfSnapshot selected).GoodForActualRoot
        target output ordinal := by
  obtain ⟨selected, hordinal, target, output, hcandidate, hstate, hhidden, hvalue,
    havoid⟩ := hhit
  subst ordinal
  refine ⟨selected, target, output, rfl, ?_, ?_⟩
  · rw [selectedPrivateSnapshotOrdinal?_eq_some selected.isLt]
  · refine ⟨?_, hstate, hhidden, hvalue, ?_⟩
    · exact hcandidate
    · rw [privateOrdinalSelectionOfSnapshot_candidates_take]
      exact havoid

theorem selectedPrivateSnapshotHitAt_root_or_nonRoot
    {source : PrivateWitnessSnapshotOutput} {ordinal : Nat}
    (hhit : SelectedPrivateSnapshotHitAt source ordinal) :
    (∃ selected : Fin source.2.length, ∃ target output,
      selected.val = ordinal ∧
      selectedPrivateSnapshotOrdinal? ordinal source.2 =
        some (privateOrdinalSelectionOfSnapshot selected) ∧
      (privateOrdinalSelectionOfSnapshot selected).GoodForActualRoot target output ordinal ∧
      IsLayerRoot target) ∨
    (∃ selected : Fin source.2.length, ∃ target output,
      selected.val = ordinal ∧
      selectedPrivateSnapshotOrdinal? ordinal source.2 =
        some (privateOrdinalSelectionOfSnapshot selected) ∧
      (privateOrdinalSelectionOfSnapshot selected).GoodForActualRoot target output ordinal ∧
      ¬IsLayerRoot target) := by
  classical
  obtain ⟨selected, target, output, hordinal, hselection, hgood⟩ :=
    selectedPrivateSnapshotOrdinal?_goodForActualRoot hhit
  by_cases hroot : IsLayerRoot target
  · exact Or.inl ⟨selected, target, output, hordinal, hselection, hgood, hroot⟩
  · exact Or.inr ⟨selected, target, output, hordinal, hselection, hgood, hroot⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
