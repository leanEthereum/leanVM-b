import SphincsSecurity.Proof.OtsProbeNonRootSelectionMass125
import SphincsSecurity.Proof.OtsProbeStopped125

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] granularAllCanonicalPrivateOrdinalSelection
  granularAllCanonicalPrivateWitnessSnapshot observedMaterializedRetainedRunFromTable

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem PrivateOrdinalSelectionFresh.not_goodForActualRoot_nonRoot
    {selection : PrivateOrdinalSelection}
    (hfresh : PrivateOrdinalSelectionFresh (some selection))
    (target : Position) (output : HashOutput) (ordinal : Nat)
    (hnonRoot : ¬IsLayerRoot target) :
    ¬selection.GoodForActualRoot target output ordinal := by
  intro hgood
  obtain ⟨parent, hparent⟩ : ∃ parent, Position.parentOf target = some parent := by
    simpa [Probe.HasStructuralParent, hgood.1] using hfresh.1
  rcases hfresh.2 target parent hparent hgood.2.2.1 with hmissing | hroot
  · have hvalue := hmissing.2
    rw [hgood.2.2.2.1] at hvalue
    contradiction
  · exact hnonRoot hroot

theorem probEvent_granularAllCanonical_selectedNonRoot_eq_zero
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun source => SelectedPrivateSnapshotNonRootHitAt source ordinal |
      granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel] = 0 := by
  apply le_antisymm _ bot_le
  calc
    _ ≤ Pr[fun _ => False |
        granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret fuel] := by
      apply probEvent_le_of_relTriple
        (relTriple_granularAllCanonicalSnapshot_privateOrdinalSelection_supported ordinal adversary
          parameter table ftsSecret fuel)
      intro source selection hrelation hhit
      have hfresh := privateOrdinalSelectionFresh_of_mem_granularAllCanonical ordinal adversary
        parameter table ftsSecret fuel selection hrelation.2
      obtain ⟨selected, target, output, _hordinal, hselected, hgood, hnonRoot⟩ := hhit
      have heq : selection = some (privateOrdinalSelectionOfSnapshot selected) :=
        hrelation.1.symm.trans hselected
      rw [heq] at hfresh
      exact hfresh.not_goodForActualRoot_nonRoot target output ordinal hnonRoot hgood
    _ = 0 := by simp

theorem probEvent_observedMaterialized_successfulFirstNonRoot_eq_zero126
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hbound : ∀ root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 126) :
    Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenNonRootHitAt table ordinal |
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] = 0 := by
  apply le_antisymm _ bot_le
  exact (Range125.probEvent_observedMaterialized_successfulDoomed_firstNonRoot_le_selectedNonRoot
    adversary parameter ftsSecret q ordinal table hbound hq).trans_eq
      (probEvent_granularAllCanonical_selectedNonRoot_eq_zero ordinal adversary parameter table ftsSecret q)

end SphincsSecurity.Concrete.OtsProbeSimulation
