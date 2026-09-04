import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedFiber

/-!
# Delayed source comparison root

An independent comparison root turns the delayed actual-root match into the exchangeable
root-selection event. The only exception is equality with one of the earlier candidate digests.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option linter.constructorNameAsVariable false

def DelayedRootGoodForComparisonAt
    (source : PrivateWitnessSnapshotOutput) (ordinal : Nat)
    (target : Position) (rightRoot : Digest) : Prop :=
  WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal source ∧
    delayedSnapshotLayerRootPosition? ordinal source = some target ∧
    CandidatesAvoidRoot target rightRoot
      ((source.2.map PlannedProbeSnapshot.toProbe).take ordinal)

def DelayedRootComparisonExceptionAt
    (source : PrivateWitnessSnapshotOutput) (ordinal : Nat)
    (target : Position) (rightRoot : Digest) : Prop :=
  WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal source ∧
    delayedSnapshotLayerRootPosition? ordinal source = some target ∧
    ¬CandidatesAvoidRoot target rightRoot
      ((source.2.map PlannedProbeSnapshot.toProbe).take ordinal)

theorem delayedRootFiber_split_comparison
    {source : PrivateWitnessSnapshotOutput} {ordinal : Nat}
    {target : Position} {rightRoot : Digest}
    (hdelayed : WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal source)
    (hposition : delayedSnapshotLayerRootPosition? ordinal source = some target) :
    DelayedRootGoodForComparisonAt source ordinal target rightRoot ∨
      DelayedRootComparisonExceptionAt source ordinal target rightRoot := by
  by_cases hright : CandidatesAvoidRoot target rightRoot
      ((source.2.map PlannedProbeSnapshot.toProbe).take ordinal)
  · exact Or.inl ⟨hdelayed, hposition, hright⟩
  · exact Or.inr ⟨hdelayed, hposition, hright⟩

theorem DelayedRootComparisonExceptionAt.comparison_mem
    {source : PrivateWitnessSnapshotOutput} {ordinal : Nat}
    {target : Position} {rightRoot : Digest}
    (hexception : DelayedRootComparisonExceptionAt source ordinal target rightRoot) :
    rightRoot ∈ snapshotPrefixCandidateDigests ordinal source := by
  have hmem := not_candidatesAvoidRoot_mem_candidate_map hexception.2.2
  unfold snapshotPrefixCandidateDigests
  simpa [List.map_take, Function.comp_def] using hmem

theorem probEvent_delayedRootFiber_comparisonException_le
    (run : ProbComp PrivateWitnessSnapshotOutput) (ordinal : Nat) (target : Position) :
    Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
        DelayedRootComparisonExceptionAt result.1 ordinal target result.2 | do
      let source ← run
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (source, rightRoot)] ≤
      Pr[fun source =>
          WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal source ∧
            delayedSnapshotLayerRootPosition? ordinal source = some target | run] *
        ((ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  let gate := fun source : PrivateWitnessSnapshotOutput =>
    WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal source ∧
      delayedSnapshotLayerRootPosition? ordinal source = some target
  let values := snapshotPrefixCandidateDigests ordinal
  calc
    _ ≤ Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
          gate result.1 ∧ result.2 ∈ values result.1 | do
        let source ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot)] := by
      apply probEvent_mono
      intro result _hresult hexception
      exact ⟨⟨hexception.1, hexception.2.1⟩, hexception.comparison_mem⟩
    _ ≤ Pr[gate | run] *
          ((ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
      apply probEvent_gate_and_uniformDigest_mem_list_le run gate values ordinal
      intro source _hsource _hgate
      unfold values snapshotPrefixCandidateDigests
      simp
    _ = _ := rfl

theorem probEvent_delayedRootFiber_le_goodComparison_add_weightedException
    (run : ProbComp PrivateWitnessSnapshotOutput) (ordinal : Nat) (target : Position) :
    Pr[fun source =>
        WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal source ∧
          delayedSnapshotLayerRootPosition? ordinal source = some target | run] ≤
      Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
          DelayedRootGoodForComparisonAt result.1 ordinal target result.2 | do
        let source ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot)] +
      Pr[fun source =>
          WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal source ∧
            delayedSnapshotLayerRootPosition? ordinal source = some target | run] *
        ((ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  let paired : ProbComp (PrivateWitnessSnapshotOutput × Digest) := do
    let source ← run
    let rightRoot ← ($ᵗ Digest : ProbComp Digest)
    pure (source, rightRoot)
  calc
    _ ≤ Pr[fun result =>
          (WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal result.1 ∧
            delayedSnapshotLayerRootPosition? ordinal result.1 = some target) | paired] := by
      apply probEvent_le_of_relTriple (relTriple_pair_uniform_right run)
      intro source result hrelation hevent
      rwa [← hrelation]
    _ ≤ Pr[fun result =>
          DelayedRootGoodForComparisonAt result.1 ordinal target result.2 ∨
            DelayedRootComparisonExceptionAt result.1 ordinal target result.2 | paired] := by
      apply probEvent_mono
      intro result _hresult hevent
      exact delayedRootFiber_split_comparison hevent.1 hevent.2
    _ ≤ Pr[fun result => DelayedRootGoodForComparisonAt result.1 ordinal target result.2 |
          paired] +
        Pr[fun result => DelayedRootComparisonExceptionAt result.1 ordinal target result.2 |
          paired] := probEvent_or_le _ _ _
    _ ≤ _ := add_le_add_right
      (probEvent_delayedRootFiber_comparisonException_le run ordinal target) _

theorem DelayedRootGoodForComparisonAt.goodForRoots
    {source : PrivateWitnessSnapshotOutput} {ordinal : Nat}
    {target : Position} {rightRoot : Digest}
    (hgood : DelayedRootGoodForComparisonAt source ordinal target rightRoot) :
    ∃ selected : Fin source.2.length, ∃ output,
      selectedPrivateSnapshotOrdinal? ordinal source.2 =
        some (privateOrdinalSelectionOfSnapshot selected) ∧
      (privateOrdinalSelectionOfSnapshot selected).GoodForRoots
        target output rightRoot ordinal := by
  obtain ⟨witness, selected, _hwitness, hordinal, _hfirst, hselection, hactual, _hroot⟩ :=
    delayedOrdinal_goodForActualRoot hgood.1 hgood.2.1
  exact ⟨selected, witness.output, hselection, hactual.goodForRoots (by
    rw [← hordinal, privateOrdinalSelectionOfSnapshot_candidates_take]
    simpa [hordinal] using hgood.2.2)⟩

theorem probEvent_delayedGoodComparison_le_privateOrdinalSelection
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position) :
    Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
        DelayedRootGoodForComparisonAt result.1 ordinal target result.2 | do
      let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
        ftsSecret fuel
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (source, rightRoot)] ≤
      Pr[fun result : Option PrivateOrdinalSelection × Digest =>
          privateOrdinalSelectionGoodForSomeOutput target result.2 ordinal result.1 | do
        let selection ← granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter
          table ftsSecret fuel
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (selection, rightRoot)] := by
  apply probEvent_le_of_relTriple
    (relTriple_snapshotComparison_privateOrdinalSelectionComparison ordinal adversary parameter
      table ftsSecret fuel)
  intro source selection hrelation hgood
  obtain ⟨selected, output, hselected, hroots⟩ := hgood.goodForRoots
  have hselection : selection.1 = some (privateOrdinalSelectionOfSnapshot selected) :=
    hrelation.1.symm.trans hselected
  rw [hselection]
  exact ⟨output, by simpa [hrelation.2] using hroots⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
