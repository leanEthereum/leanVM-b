import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceNonRootProbability
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedSelector

/-!
# Delayed source position fibers

A delayed layer-root witness selects one concrete root position. The target-independent permissive
production experiment supplies the comparison weights used to sum those fibers without enumerating
structural positions.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option linter.constructorNameAsVariable false

noncomputable def delayedSnapshotLayerRootPosition?
    (ordinal : Nat) (source : PrivateWitnessSnapshotOutput) : Option Position :=
  if hselected : ordinal < source.2.length then
    candidateLayerRootPosition? (source.2.get ⟨ordinal, hselected⟩).probe
  else none

theorem delayedSnapshotLayerRootPosition?_eq_some_of_delayed
    {ordinal : Nat} {source : PrivateWitnessSnapshotOutput}
    (hdelayed : WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal source) :
    ∃ target, delayedSnapshotLayerRootPosition? ordinal source = some target := by
  obtain ⟨witness, sourceOrdinal, _hwitness, hordinal, _hfirst, hroot,
    _hstate, _hrevealed, _hvalue⟩ := hdelayed
  have hlt : ordinal < source.2.length := by
    rw [← hordinal]
    exact sourceOrdinal.isLt
  have hselected : (⟨ordinal, hlt⟩ : Fin source.2.length) = sourceOrdinal :=
    Fin.ext hordinal.symm
  obtain ⟨target, hcoordinate, htargetRoot⟩ := hroot
  refine ⟨target, ?_⟩
  unfold delayedSnapshotLayerRootPosition?
  rw [dif_pos hlt, candidateLayerRootPosition?_eq_some_iff, hselected]
  exact ⟨hcoordinate, htargetRoot⟩

theorem not_delayed_of_delayedSnapshotLayerRootPosition?_eq_none
    {ordinal : Nat} {source : PrivateWitnessSnapshotOutput}
    (hposition : delayedSnapshotLayerRootPosition? ordinal source = none) :
    ¬WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal source := by
  intro hdelayed
  obtain ⟨target, htarget⟩ :=
    delayedSnapshotLayerRootPosition?_eq_some_of_delayed hdelayed
  rw [hposition] at htarget
  simp at htarget

theorem delayedOrdinal_goodForActualRoot
    {ordinal : Nat} {source : PrivateWitnessSnapshotOutput} {target : Position}
    (hdelayed : WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal source)
    (hposition : delayedSnapshotLayerRootPosition? ordinal source = some target) :
    ∃ witness sourceOrdinal,
      source.1 = some witness ∧ sourceOrdinal.val = ordinal ∧
      firstPrivateWitnessOrdinal? witness
          (source.2.map PlannedProbeSnapshot.toProbe) =
        some (snapshotProbeOrdinal sourceOrdinal) ∧
      selectedPrivateSnapshotOrdinal? ordinal source.2 =
        some (privateOrdinalSelectionOfSnapshot sourceOrdinal) ∧
      (privateOrdinalSelectionOfSnapshot sourceOrdinal).GoodForActualRoot
        target witness.output ordinal ∧
      IsLayerRoot target := by
  obtain ⟨witness, sourceOrdinal, hwitness, hordinal, hfirst, hroot,
    hstate, hrevealed, hvalue⟩ := hdelayed
  have hlt : ordinal < source.2.length := by
    rw [← hordinal]
    exact sourceOrdinal.isLt
  have hindex : (⟨ordinal, hlt⟩ : Fin source.2.length) = sourceOrdinal :=
    Fin.ext hordinal.symm
  obtain ⟨sourceTarget, hcoordinate, hsourceRoot⟩ := hroot
  have hsourcePosition : delayedSnapshotLayerRootPosition? ordinal source = some sourceTarget := by
    unfold delayedSnapshotLayerRootPosition?
    rw [dif_pos hlt, candidateLayerRootPosition?_eq_some_iff, hindex]
    exact ⟨hcoordinate, hsourceRoot⟩
  have htarget : target = sourceTarget := by
    rw [hposition] at hsourcePosition
    exact Option.some.inj hsourcePosition
  subst sourceTarget
  have hmatch := privateWitnessAtOrdinal_of_firstPrivateWitnessOrdinal?_eq_some hfirst
  unfold PrivateWitnessAtOrdinal at hmatch
  have hmatchCoordinate : (source.2.get sourceOrdinal).probe.coordinate =
      .position witness.position := by
    simpa [snapshotProbeOrdinal] using hmatch.1
  have hwitnessTarget : witness.position = target := by
    simpa using hmatchCoordinate.symm.trans hcoordinate
  subst target
  have hcandidate : (privateOrdinalSelectionOfSnapshot sourceOrdinal).candidate =
      ⟨.position witness.position, truncateHash witness.output⟩ := by
    rw [privateOrdinalSelectionOfSnapshot_candidate]
    exact congrArg₂ Probe.mk hmatch.1 hmatch.2.symm
  have huses : WitnessFirstUsesOrdinal ordinal
      (erasePrivateWitnessSnapshotOutput source) := by
    unfold erasePrivateWitnessSnapshotOutput
    exact ⟨witness, snapshotProbeOrdinal sourceOrdinal, hwitness, hordinal, hfirst⟩
  have havoid := candidatesTake_avoid_witnessRoot_of_first huses hwitness
  have hselection : selectedPrivateSnapshotOrdinal? ordinal source.2 =
      some (privateOrdinalSelectionOfSnapshot sourceOrdinal) := by
    rw [selectedPrivateSnapshotOrdinal?_eq_some hlt]
    congr
  have hactual : (privateOrdinalSelectionOfSnapshot sourceOrdinal).GoodForActualRoot
      witness.position witness.output ordinal :=
    ⟨hcandidate, by simpa using hstate, by simpa using hrevealed, by simpa using hvalue, by
      rw [← hordinal, privateOrdinalSelectionOfSnapshot_candidates_take]
      simpa [erasePrivateWitnessSnapshotOutput, hordinal] using havoid⟩
  exact ⟨witness, sourceOrdinal, hwitness, hordinal, hfirst, hselection, hactual, hsourceRoot⟩

theorem probEvent_delayedOrdinal_le_of_common_position_fibers
    (source : ProbComp PrivateWitnessSnapshotOutput)
    (common : ProbComp (Option PermissivePrivateOrdinalSelection))
    (ordinal : Nat)
    (hfiber : ∀ target,
      Pr[fun output =>
          WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal output ∧
            delayedSnapshotLayerRootPosition? ordinal output = some target | source] ≤
        Pr[fun selection =>
            permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
          common] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal | source] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply probEvent_le_of_common_position_fibers source
    (WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal)
    (delayedSnapshotLayerRootPosition? ordinal) common
    permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?
    (((2 ^ digestBits : Nat) : ENNReal)⁻¹)
  · intro output hdelayed
    obtain ⟨target, htarget⟩ :=
      delayedSnapshotLayerRootPosition?_eq_some_of_delayed hdelayed
    rw [htarget]
    simp
  · exact hfiber

theorem probEvent_granularAllCanonical_delayedOrdinal_le_of_common_position_fibers
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (hfiber : ∀ target,
      Pr[fun output =>
          WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal output ∧
            delayedSnapshotLayerRootPosition? ordinal output = some target |
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret fuel table] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal |
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
  probEvent_delayedOrdinal_le_of_common_position_fibers _ _ ordinal hfiber

theorem probEvent_sampledCanonical_delayedOrdinal_le_of_table_position_fibers
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (hfiber : ∀ table target,
      Pr[fun output =>
          WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal output ∧
            delayedSnapshotLayerRootPosition? ordinal output = some target |
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret fuel table] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret fuel] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot
  apply probEvent_bind_le_of_forall_le
  intro table _htable
  exact probEvent_granularAllCanonical_delayedOrdinal_le_of_common_position_fibers ordinal
    adversary parameter table ftsSecret fuel (hfiber table)

end SphincsSecurity.Concrete.OtsProbeSimulation
