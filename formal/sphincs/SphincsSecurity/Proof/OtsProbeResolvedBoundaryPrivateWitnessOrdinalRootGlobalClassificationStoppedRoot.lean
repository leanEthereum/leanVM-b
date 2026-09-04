import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedAlignedProjection
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionBoundary

/-!
# Clean stopped layer-root projection

The successful first-root diagnostic retains the exact source selector together with the intrinsic
fact that no earlier source snapshot is an already-materialized hidden structural hit. This is the
source event consumed by the joint root-selection bound.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

def SelectedPrivateSnapshotCleanRootHitAt
    (table : OtsSecretIndex → HashOutput)
    (source : PrivateWitnessSnapshotOutput) (ordinal : Nat) : Prop :=
  ∃ selected : Fin source.2.length, ∃ target output,
    selected.val = ordinal ∧
    selectedPrivateSnapshotOrdinal? ordinal source.2 =
      some (privateOrdinalSelectionOfSnapshot selected) ∧
    (privateOrdinalSelectionOfSnapshot selected).GoodForActualRoot target output ordinal ∧
    IsLayerRoot target ∧
    SnapshotsAvoidExistingHiddenPositionHits table (source.2.take ordinal)

noncomputable def selectedPrivateSnapshotLayerRootPosition?
    (ordinal : Nat) (source : PrivateWitnessSnapshotOutput) : Option Position :=
  if hselected : ordinal < source.2.length then
    candidateLayerRootPosition? (source.2.get ⟨ordinal, hselected⟩).probe
  else none

theorem selectedPrivateSnapshotLayerRootPosition?_eq_some_of_cleanRootHitAt
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput} {ordinal : Nat}
    (hhit : SelectedPrivateSnapshotCleanRootHitAt table source ordinal) :
    ∃ target, selectedPrivateSnapshotLayerRootPosition? ordinal source = some target := by
  obtain ⟨selected, target, output, hordinal, _hselection, hgood, hroot, _hclean⟩ := hhit
  have hlt : ordinal < source.2.length := by
    rw [← hordinal]
    exact selected.isLt
  refine ⟨target, ?_⟩
  unfold selectedPrivateSnapshotLayerRootPosition?
  rw [dif_pos hlt, candidateLayerRootPosition?_eq_some_iff]
  have hindex : (⟨ordinal, hlt⟩ : Fin source.2.length) = selected := Fin.ext hordinal.symm
  rw [hindex]
  have hcandidate := hgood.1
  rw [privateOrdinalSelectionOfSnapshot_candidate] at hcandidate
  have hcandidate' : (source.2.get selected).probe =
      ⟨.position target, truncateHash output⟩ := by
    simpa [snapshotProbeOrdinal] using hcandidate
  exact ⟨congrArg Probe.coordinate hcandidate', hroot⟩

theorem not_selectedPrivateSnapshotCleanRootHitAt_of_position_eq_none
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput} {ordinal : Nat}
    (hposition : selectedPrivateSnapshotLayerRootPosition? ordinal source = none) :
    ¬SelectedPrivateSnapshotCleanRootHitAt table source ordinal := by
  intro hhit
  obtain ⟨target, htarget⟩ :=
    selectedPrivateSnapshotLayerRootPosition?_eq_some_of_cleanRootHitAt hhit
  rw [hposition] at htarget
  simp at htarget

theorem probEvent_selectedPrivateSnapshotCleanRootHitAt_le_of_position_fibers
    (table : OtsSecretIndex → HashOutput)
    (run : ProbComp PrivateWitnessSnapshotOutput) (ordinal : Nat)
    (hfiber : ∀ target,
      Pr[fun source => SelectedPrivateSnapshotCleanRootHitAt table source ordinal ∧
          selectedPrivateSnapshotLayerRootPosition? ordinal source = some target | run] ≤
        Pr[fun source =>
          selectedPrivateSnapshotLayerRootPosition? ordinal source = some target | run] *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[fun source => SelectedPrivateSnapshotCleanRootHitAt table source ordinal | run] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply probEvent_le_of_uniform_weighted_fibers run
    (SelectedPrivateSnapshotCleanRootHitAt table · ordinal)
    (selectedPrivateSnapshotLayerRootPosition? ordinal)
    (((2 ^ digestBits : Nat) : ENNReal)⁻¹)
  intro position?
  cases position? with
  | none =>
      have hzero : Pr[fun source =>
          SelectedPrivateSnapshotCleanRootHitAt table source ordinal ∧
            selectedPrivateSnapshotLayerRootPosition? ordinal source = none | run] = 0 := by
        apply probEvent_eq_zero
        intro source _hsource hevent
        exact not_selectedPrivateSnapshotCleanRootHitAt_of_position_eq_none hevent.2 hevent.1
      rw [hzero]
      exact zero_le
  | some target => exact hfiber target

theorem SnapshotObservedFirstStoppedRel.selectedCleanRoot_of_successful_firstRoot
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput}
    {result : ObservedCleanRunResult (α × SplitHashCache)}
    (hrelation : SnapshotObservedFirstStoppedRel table source (some result))
    (finalResult : ObservedCleanRunResult (α × SplitHashCache))
    (hfinish : some finalResult ∈ support
      (finishObservedCleanRunFromTable (some result)))
    (ordinal : Nat)
    (selected : Fin result.observations.length)
    (hselected : selected.val = ordinal)
    (hfirst : FirstExistingHiddenHitAt result ordinal)
    (hroot : (result.observations.get selected).toProbe.IsLayerRoot) :
    SelectedPrivateSnapshotCleanRootHitAt table source ordinal := by
  rcases hrelation.selectedAligned_or_chain_of_successful_firstHit finalResult hfinish ordinal
      hfirst with ⟨hhit, haligned⟩ | hchain
  · rcases selectedPrivateSnapshotHitAt_root_or_nonRoot' hhit with hsourceRoot | hsourceNonRoot
    · obtain ⟨sourceSelected, target, output, hsourceOrdinal, hselection, hgood,
        htargetRoot⟩ := hsourceRoot
      exact ⟨sourceSelected, target, output, hsourceOrdinal, hselection, hgood, htargetRoot,
        haligned.avoidExistingHiddenPositionHits hfirst⟩
    · obtain ⟨sourceSelected, target, output, hsourceOrdinal, _hselection, hgood,
        htargetNotRoot⟩ := hsourceNonRoot
      obtain ⟨alignedSource, alignedObserved, halignedSource, halignedObserved,
        hcandidates, _hprefix, _hsnapshots⟩ := haligned
      have hsourceEq : sourceSelected = alignedSource :=
        Fin.ext (hsourceOrdinal.trans halignedSource.symm)
      have hobservedEq : alignedObserved = selected :=
        Fin.ext (halignedObserved.trans hselected.symm)
      have hsourceRoot : (source.2.get alignedSource).probe.IsLayerRoot := by
        rw [hcandidates, hobservedEq]
        exact hroot
      have htargetRoot : IsLayerRoot target := by
        rw [← hsourceEq] at hsourceRoot
        have hcandidate := hgood.1
        rw [privateOrdinalSelectionOfSnapshot_candidate] at hcandidate
        have hcandidate' : (source.2.get sourceSelected).probe =
            ⟨.position target, truncateHash output⟩ := by
          simpa [snapshotProbeOrdinal] using hcandidate
        obtain ⟨rootTarget, hcoordinate, hrootTarget⟩ := hsourceRoot
        have htarget : target = rootTarget := by
          exact Coordinate.position.inj
            ((congrArg Probe.coordinate hcandidate').symm.trans hcoordinate)
        simpa [htarget] using hrootTarget
      exact (htargetNotRoot htargetRoot).elim
  · exact (not_firstExistingHiddenRootHitAt_of_firstChainStart hchain hfirst selected hselected
      hroot).elim

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_observedMaterialized_successfulDoomed_firstRoot_le_selectedCleanRoot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hbound : ∀ root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
        (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt table ordinal |
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun source => SelectedPrivateSnapshotCleanRootHitAt table source ordinal |
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q] := by
  apply probEvent_le_of_relTriple
    (relTriple_symm
      (relTriple_granularAllSnapshot_observedMaterializedRetained_firstStopped adversary
        parameter ftsSecret q table hbound hq))
  intro observed source hrelation hevent
  cases observed with
  | none =>
      simp [ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hevent
  | some result =>
      obtain ⟨⟨finalResult, hfinish⟩, _hdoomed, selected, hselected, hfirst, hroot⟩ := hevent
      exact hrelation.selectedCleanRoot_of_successful_firstRoot finalResult hfinish ordinal
        selected hselected hfirst hroot

end SphincsSecurity.Concrete.OtsProbeSimulation
