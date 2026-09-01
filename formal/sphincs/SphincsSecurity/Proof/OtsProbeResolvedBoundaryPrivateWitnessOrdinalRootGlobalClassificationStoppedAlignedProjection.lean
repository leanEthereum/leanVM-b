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
        hcandidates, _hprefix⟩ := haligned
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
