import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedNonRoot

/-!
# Aligned stopped diagnostic projection

The stopped relation retains the equality between the source candidate and the comparison
observation at the selected ordinal. Consequently the comparison-side root classification can be
transported to the exact source selector without enlarging to the unclassified source event.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

def PlannedProbeSnapshot.ExistingHiddenPositionHit
    (table : OtsSecretIndex → HashOutput) (snapshot : PlannedProbeSnapshot) : Prop :=
  ∃ observation position,
    snapshot.ObservedAt table observation ∧
      observation.coordinate = .position position ∧ observation.ExistingHiddenHit

def SnapshotsAvoidExistingHiddenPositionHits
    (table : OtsSecretIndex → HashOutput)
    (snapshots : List PlannedProbeSnapshot) : Prop :=
  ∀ snapshot ∈ snapshots, ¬snapshot.ExistingHiddenPositionHit table

theorem PlannedProbeSnapshot.ObservedAt.existingHiddenPositionHit_iff
    {table : OtsSecretIndex → HashOutput}
    {snapshot : PlannedProbeSnapshot} {observation : CleanProbeObservation}
    (haligned : snapshot.ObservedAt table observation) :
    snapshot.ExistingHiddenPositionHit table ↔
      ∃ position, observation.coordinate = .position position ∧
        observation.ExistingHiddenHit := by
  constructor
  · rintro ⟨other, position, hother, hposition, hhit⟩
    have hprobe : other.toProbe = observation.toProbe := hother.1.trans haligned.1.symm
    have hcoordinate : other.coordinate = observation.coordinate :=
      congrArg Probe.coordinate hprobe
    have hcandidate : other.candidate = observation.candidate :=
      congrArg Probe.candidate hprobe
    refine ⟨position, hcoordinate.symm.trans hposition, ?_⟩
    obtain ⟨hhidden, output, hvalue, hcandidateHit⟩ := hhit
    refine ⟨?_, output, ?_, ?_⟩
    · calc
        observation.revealedAtProbe =
            decide (observation.coordinate ∈ snapshot.context.state.revealed) :=
          haligned.2.2.1
        _ = decide (other.coordinate ∈ snapshot.context.state.revealed) := by
          rw [hcoordinate]
        _ = other.revealedAtProbe := hother.2.2.1.symm
        _ = false := hhidden
    · have hotherValue := hother.2.1 position hposition
      have halignedValue := haligned.2.1 position (hcoordinate.symm.trans hposition)
      rw [hotherValue] at hvalue
      rw [halignedValue]
      exact hvalue
    · exact hcandidateHit.trans hcandidate
  · rintro ⟨position, hposition, hhit⟩
    exact ⟨observation, position, haligned, hposition, hhit⟩

theorem SnapshotsObservedAt.avoidExistingHiddenPositionHits
    {table : OtsSecretIndex → HashOutput}
    {snapshots : List PlannedProbeSnapshot}
    {observations : List CleanProbeObservation}
    (haligned : SnapshotsObservedAt table snapshots observations)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit) :
    SnapshotsAvoidExistingHiddenPositionHits table snapshots := by
  induction haligned with
  | nil => simp [SnapshotsAvoidExistingHiddenPositionHits]
  | cons hhead htail ih =>
      intro snapshot hsnapshot
      simp only [List.mem_cons] at hsnapshot
      rcases hsnapshot with rfl | hrest
      · intro hhit
        obtain ⟨_position, _hposition, hobservation⟩ :=
          hhead.existingHiddenPositionHit_iff.mp hhit
        exact hnoHit _ (by simp) hobservation
      · apply ih
        · intro observation hobservation
          exact hnoHit observation (by simp [hobservation])
        · exact hrest

theorem SelectedSnapshotObservationAlignedAt.avoidExistingHiddenPositionHits
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput}
    {result : ObservedCleanRunResult α} {ordinal : Nat}
    (haligned : SelectedSnapshotObservationAlignedAt table source result ordinal)
    (hfirst : FirstExistingHiddenHitAt result ordinal) :
    SnapshotsAvoidExistingHiddenPositionHits table (source.2.take ordinal) := by
  obtain ⟨_selectedSource, selectedObserved, _hsource, hobserved, _hcandidate,
    _hprefix, hsnapshots⟩ := haligned
  apply hsnapshots.avoidExistingHiddenPositionHits
  intro observation hobservation
  obtain ⟨index, hget⟩ := List.mem_iff_get.mp hobservation
  obtain ⟨_first, _hfirstOrdinal, _hfirstHit, hbefore⟩ := hfirst
  have hindexLt : index.val < ordinal := by
    have hlt := index.isLt
    simp only [List.length_take] at hlt
    omega
  have hresultLt : index.val < result.observations.length := by
    have hordinalLt : ordinal < result.observations.length := by
      rw [← hobserved]
      exact selectedObserved.isLt
    exact hindexLt.trans hordinalLt
  let resultIndex : Fin result.observations.length := ⟨index.val, hresultLt⟩
  have hgetResult : result.observations.get resultIndex = observation := by
    obtain ⟨tail, htail⟩ := List.take_prefix ordinal result.observations
    have htakeGet : (result.observations.take ordinal).get index =
        result.observations.get resultIndex := by
      simp [resultIndex]
    exact htakeGet.symm.trans hget
  rw [← hgetResult]
  exact hbefore resultIndex hindexLt

theorem SnapshotObservedFirstStoppedRel.selectedNonRoot_of_successful_firstNonRoot
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
    (hnonRoot : ¬(result.observations.get selected).toProbe.IsLayerRoot)
    (hnotChain : ¬FirstExistingHiddenChainStartHitAt result.observations ordinal) :
    SelectedPrivateSnapshotNonRootHitAt source ordinal := by
  rcases hrelation.selectedAligned_or_chain_of_successful_firstHit finalResult hfinish ordinal
      hfirst with ⟨hhit, haligned⟩ | hchain
  · rcases selectedPrivateSnapshotHitAt_root_or_nonRoot' hhit with hroot | hnonRootSource
    · obtain ⟨sourceSelected, target, output, hsourceSelected, _hselection, hgood,
        htargetRoot⟩ := hroot
      obtain ⟨alignedSource, alignedObserved, halignedSource, halignedObserved,
        hcandidates, _hprefix, _hsnapshots⟩ := haligned
      have hsourceEq : sourceSelected = alignedSource :=
        Fin.ext (hsourceSelected.trans halignedSource.symm)
      have hobservedEq : alignedObserved = selected :=
        Fin.ext (halignedObserved.trans hselected.symm)
      have hsourceRoot : (source.2.get alignedSource).probe.IsLayerRoot := by
        rw [← hsourceEq]
        refine ⟨target, ?_, htargetRoot⟩
        exact congrArg Probe.coordinate hgood.1
      have hobservedRoot :
          (result.observations.get alignedObserved).toProbe.IsLayerRoot := by
        rw [← hcandidates]
        exact hsourceRoot
      rw [hobservedEq] at hobservedRoot
      exact (hnonRoot hobservedRoot).elim
    · exact hnonRootSource
  · exact (hnotChain (hchain.at_of_firstExistingHiddenHitAt hfirst)).elim

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_observedMaterialized_successfulDoomed_firstNonRoot_le_selectedNonRoot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenNonRootHitAt table ordinal |
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun source => SelectedPrivateSnapshotNonRootHitAt source ordinal |
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q] := by
  let source := granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q
  let observed := observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
    (2 * q) table
  calc
    _ ≤ Pr[fun source => SelectedPrivateSnapshotNonRootHitAt source ordinal | source] +
        Pr[ObservedMaterializedOutput.FirstExistingHiddenChainStartHitAt ordinal | observed] := by
      apply probEvent_le_failure_add_residual_of_relTriple observed source
        (fun observed source => SnapshotObservedFirstStoppedRel table source observed)
        (ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenNonRootHitAt table ordinal)
        (ObservedMaterializedOutput.FirstExistingHiddenChainStartHitAt ordinal)
        (fun source => SelectedPrivateSnapshotNonRootHitAt source ordinal)
        (relTriple_symm
          (relTriple_granularAllSnapshot_observedMaterializedRetained_firstStopped adversary
            parameter ftsSecret q table hbound hq))
      intro right left hrelation hevent hnotChain
      cases right with
      | none =>
          simp [ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenNonRootHitAt] at hevent
      | some result =>
          obtain ⟨⟨finalResult, hfinish⟩, _hdoomed, selected, hselected, hfirst,
            hnonRoot⟩ := hevent
          exact hrelation.selectedNonRoot_of_successful_firstNonRoot finalResult hfinish ordinal
            selected hselected hfirst hnonRoot hnotChain
    _ = _ := by
      rw [probEvent_firstExistingHiddenChainStartHitAt_eq_zero adversary parameter ftsSecret
        (2 * q) ordinal table]
      simp [source]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
theorem probEvent_sampledDiagnostic_successfulDoomed_firstNonRoot_le
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[fun outcome => outcome.SuccessfulDoomed ∧
          outcome.FirstExistingHiddenNonRootHitAt ordinal |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply probEvent_sampledDiagnostic_successfulDoomed_firstExistingHiddenNonRootHitAt_le_of_forall
  intro table
  calc
    _ ≤ Pr[fun source => SelectedPrivateSnapshotNonRootHitAt source ordinal |
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q] :=
      probEvent_observedMaterialized_successfulDoomed_firstNonRoot_le_selectedNonRoot adversary
        parameter ftsSecret q ordinal table hbound hq
    _ ≤ _ := probEvent_granularAllCanonical_selectedNonRoot_le ordinal adversary parameter
      table ftsSecret q

end SphincsSecurity.Concrete.OtsProbeSimulation
