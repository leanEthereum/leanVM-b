import SphincsSecurity.Proof.OtsProbeSelectionTransport125
import SphincsSecurity.Proof.OtsProbeJointCostCoupling
import SphincsSecurity.Proof.OtsProbeSuccessfulHiddenCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

def FreshExistingHiddenSelection (ordinal : Nat) : Option PermissivePrivateOrdinalSelection → Prop
  | none => False
  | some selection =>
      (cleanProbeObservation selection.state selection.candidate.coordinate
        selection.candidate.candidate).ExistingHiddenHit ∧
      selection.candidate ∉ selection.candidates.take ordinal

theorem PrivateOrdinalSelection.GoodForActualRoot.candidate_not_mem_prefix
    {selection : PrivateOrdinalSelection} {target : Position} {output : HashOutput} {ordinal : Nat}
    (hgood : selection.GoodForActualRoot target output ordinal) :
    selection.candidate ∉ selection.candidates.take ordinal := by
  intro hmem
  exact hgood.2.2.2.2 selection.candidate hmem hgood.1

theorem canonicalSelectionPreserved_goodForActualRoot
    {left : PrivateOrdinalSelection} {right : Option PermissivePrivateOrdinalSelection}
    {target : Position} {output : HashOutput} {ordinal : Nat}
    (hrel : CanonicalSelectionPreserved (some left) right)
    (hgood : left.GoodForActualRoot target output ordinal) :
    FreshExistingHiddenSelection ordinal right := by
  cases right with
  | none => exact False.elim hrel
  | some right =>
      have hcandidate : right.candidate = ⟨.position target, truncateHash output⟩ :=
        hrel.1.symm.trans hgood.1
      have hhidden : Coordinate.position target ∉ right.state.revealed := by
        rw [← hrel.2.1.revealed]
        exact hgood.2.2.1
      have hvalue : right.state.values (.position target) = some output := by
        rw [← hrel.2.1.values]
        simp only [materializedDeferredState, DeferredContext.positionValue,
          hgood.2.1, hgood.2.2.2.1]
      refine ⟨?_, ?_⟩
      · simp only [hcandidate]
        exact ⟨by simpa [cleanProbeObservation] using hhidden, output, hvalue, rfl⟩
      · rw [← hrel.2.2, ← hrel.1]
        exact hgood.candidate_not_mem_prefix

theorem freshExistingHiddenSelection_materializedCharge_eq_one
    {selection : PermissivePrivateOrdinalSelection} {ordinal : Nat}
    (hfresh : FreshExistingHiddenSelection ordinal (some selection))
    (hcovered : ∀ coordinate candidate, (coordinate, candidate) ∈ selection.state.pending →
      (⟨coordinate, candidate⟩ : Probe) ∈ selection.candidates.take ordinal) :
    materializedCandidateCharge selection.state (some selection.candidate) = 1 := by
  apply materializedCandidateCharge_eq_one_of_existingHiddenHit selection.state selection.candidate hfresh.1
  intro hpending
  exact hfresh.2 (hcovered _ _ hpending)

theorem probEvent_canonical_actualRoot_le_delayed_freshHiddenSelection
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun source => ∃ selection target output, source = some selection ∧
      selection.GoodForActualRoot target output ordinal |
      granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret fuel] ≤
    Pr[FreshExistingHiddenSelection ordinal |
      delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret fuel table] := by
  apply probEvent_le_of_relTriple
    (relTriple_granularAllCanonicalPrivateOrdinalSelection_preserved ordinal adversary parameter table ftsSecret fuel)
  intro left right hrel hevent
  obtain ⟨selection, target, output, rfl, hgood⟩ := hevent
  exact canonicalSelectionPreserved_goodForActualRoot hrel hgood

theorem probEvent_canonical_snapshot_hit_le_delayed_freshHiddenSelection
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun source => SelectedPrivateSnapshotHitAt source ordinal |
      granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel] ≤
    Pr[FreshExistingHiddenSelection ordinal |
      delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret fuel table] := by
  apply le_trans _ (probEvent_canonical_actualRoot_le_delayed_freshHiddenSelection
    ordinal adversary parameter table ftsSecret fuel)
  apply probEvent_le_of_relTriple
    (relTriple_granularAllCanonicalSnapshot_privateOrdinalSelection_supported ordinal adversary
      parameter table ftsSecret fuel)
  intro source selection hrelation hhit
  obtain ⟨selected, target, output, _hordinal, hselected, hgood⟩ :=
    selectedPrivateSnapshotOrdinal?_goodForActualRoot hhit
  exact ⟨privateOrdinalSelectionOfSnapshot selected, target, output,
    hrelation.1.symm.trans hselected, hgood⟩

theorem probEvent_sampledSuccessfulFirstHit_le_delayed_freshHiddenSelection126
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 126) :
    Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenHitAt ordinal | do
      let table ← sampleOtsHashTable
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
    ∑' table, Pr[= table | sampleOtsHashTable] *
      Pr[FreshExistingHiddenSelection ordinal |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret q table] := by
  apply (Range125.probEvent_sampledSuccessfulFirstHit_le_selectedSnapshot
    adversary parameter ftsSecret q ordinal hbound hq).trans
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot
  rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro table
  exact mul_le_mul' le_rfl
    (probEvent_canonical_snapshot_hit_le_delayed_freshHiddenSelection
      ordinal adversary parameter table ftsSecret q)

noncomputable def sampledFreshHiddenRisk (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) : ℝ≥0∞ :=
  ∑ ordinal : Fin q, ∑' table, Pr[= table | sampleOtsHashTable] *
    Pr[FreshExistingHiddenSelection ordinal.val |
      delayedPermissiveDetailedSelectionExperimentAfterTable ordinal.val adversary parameter ftsSecret q table]

theorem probEvent_sampledDiagnostic_successfulHidden_le_freshHiddenRisk126
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 126) :
    Pr[ObservedMaterializedDiagnostic.SuccessfulHiddenHit |
      sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
    sampledFreshHiddenRisk adversary parameter ftsSecret q := by
  apply (probEvent_sampledDiagnostic_successfulHidden_le_sum_firstHits126
    adversary parameter ftsSecret q hbound hq).trans
  apply Finset.sum_le_sum
  intro ordinal _
  exact (probEvent_sampledDiagnostic_successfulHidden_firstHit_le_raw
    adversary parameter ftsSecret (2 * q) ordinal.val).trans
      (probEvent_sampledSuccessfulFirstHit_le_delayed_freshHiddenSelection126
        adversary parameter ftsSecret q ordinal.val hbound hq)

theorem probEvent_sampledActualRetained_verifyProbe_le_charge_add_freshHiddenRisk126
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 126) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
    materializedRetainedCharge adversary parameter ftsSecret (2 * q) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
      sampledFreshHiddenRisk adversary parameter ftsSecret q :=
  (probEvent_sampledActualRetained_verifyProbe_le_charge_add_successfulHiddenHit126
    adversary parameter ftsSecret q hbound hq).trans
      (add_le_add le_rfl
        (probEvent_sampledDiagnostic_successfulHidden_le_freshHiddenRisk126
          adversary parameter ftsSecret q hbound hq))

theorem probEvent_sampledActualRetained_verifyProbe_le_charge_add_freshHiddenRisk126_of_hashQueryBound
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
    materializedRetainedCharge adversary parameter ftsSecret (2 * q) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
      sampledFreshHiddenRisk adversary parameter ftsSecret q :=
  probEvent_sampledActualRetained_verifyProbe_le_charge_add_freshHiddenRisk126 adversary parameter ftsSecret q
    (fun table root => isQueryBoundP_expandedRetained_all_tables_roots
      adversary q hq parameter hparameter table ftsSecret hfts root) hqMax

end SphincsSecurity.Concrete.OtsProbeSimulation
