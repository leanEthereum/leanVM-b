import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedTop

/-!
# Stopped diagnostic projection

The stopped coupling turns a successful already-materialized hidden hit into the exact source
snapshot that selected it. A non-root hit may instead be the separately charged hidden one-time
chain start.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_observedMaterialized_successfulDoomed_firstRoot_le_selectedSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt table ordinal |
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun source => SelectedPrivateSnapshotHitAt source ordinal |
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q] := by
  apply probEvent_le_of_relTriple
    (relTriple_symm
      (relTriple_granularAllSnapshot_observedMaterializedRetained_firstStopped adversary
        parameter ftsSecret q table hbound hq))
  intro observed source hrelation hevent
  cases observed with
  | none => simp [ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hevent
  | some result =>
      obtain ⟨⟨finalResult, hfinish⟩, _hdoomed, selected, hselected, hfirst, hroot⟩ := hevent
      apply hrelation.selected_of_successful_firstRoot finalResult hfinish ordinal hfirst
      intro other hother
      have heq : other = selected := Fin.ext (hother.trans hselected.symm)
      subst other
      exact hroot

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_observedMaterialized_successfulDoomed_firstNonRoot_le_selectedSnapshot_add_chainStart
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenNonRootHitAt table ordinal |
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun source => SelectedPrivateSnapshotHitAt source ordinal |
          granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q] +
        Pr[fun observed => (match observed with
          | none => False
          | some result => FirstExistingHiddenChainStartHit result.observations) |
          observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] := by
  let source := granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q
  let observed := observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
    (2 * q) table
  apply probEvent_le_failure_add_residual_of_relTriple observed source
    (fun observed source => SnapshotObservedFirstStoppedRel table source observed)
    (ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenNonRootHitAt table ordinal)
    (fun observed => match observed with
      | none => False
      | some result => FirstExistingHiddenChainStartHit result.observations)
    (fun source => SelectedPrivateSnapshotHitAt source ordinal)
    (relTriple_symm
      (relTriple_granularAllSnapshot_observedMaterializedRetained_firstStopped adversary
        parameter ftsSecret q table hbound hq))
  intro right left hrelation hevent hnotChain
  cases right with
  | none => simp [ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenNonRootHitAt] at hevent
  | some result =>
      obtain ⟨⟨finalResult, hfinish⟩, _hdoomed, _selected, _hselected, hfirst,
        _hnonRoot⟩ := hevent
      rcases hrelation.selected_or_chain_of_successful_firstNonRoot finalResult hfinish ordinal
        hfirst with hselected | hchain
      · exact hselected
      · exact (hnotChain hchain).elim

end SphincsSecurity.Concrete.OtsProbeSimulation
