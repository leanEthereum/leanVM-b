import SphincsSecurity.Proof.OtsProbeHiddenRootCharge
import SphincsSecurity.Proof.OtsProbeNonRootExclusion

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

noncomputable def hiddenSelectionCharge (common : ProbComp (Option PermissivePrivateOrdinalSelection)) : ℝ≥0∞ :=
  Pr[fun selection => (permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection).isSome = true | common] *
      (4 / 3)

theorem hiddenSelectionCharge_le_residualSelectionCharge
    (common : ProbComp (Option PermissivePrivateOrdinalSelection)) :
    hiddenSelectionCharge common ≤ residualSelectionCharge common := by
  exact le_self_add

theorem probEvent_diagnosticOrdinal_pair_le_selectedCharge126
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) (hordinal : ordinal < q)
    (hfuel : 2 * q < Fintype.card Digest)
    (hbound : ∀ root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 126) :
    Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenRootHitAt table ordinal |
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] +
      Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenNonRootHitAt table ordinal |
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      hiddenSelectionCharge
        (permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret (2 * q) table) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [probEvent_observedMaterialized_successfulFirstNonRoot_eq_zero126
    adversary parameter ftsSecret q ordinal table hbound hq, add_zero]
  simpa only [hiddenSelectionCharge, mul_assoc] using
    probEvent_successfulDoomedFirstRoot_le_selectedCharge126 ordinal adversary parameter table
      ftsSecret q hordinal hfuel hbound hq

noncomputable def sampledHiddenSelectionCharge (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) : ℝ≥0∞ :=
  ∑ ordinal : Fin q, ∑' table, Pr[= table | sampleOtsHashTable] *
    hiddenSelectionCharge
      (permissiveDetailedSelectionExperimentAfterTable ordinal.val adversary parameter ftsSecret (2 * q) table)

theorem probEvent_sampledDiagnosticOrdinal_pair_le_selectedCharge126
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) (hordinal : ordinal < q)
    (hfuel : 2 * q < Fintype.card Digest)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 126) :
    Pr[fun outcome => outcome.SuccessfulDoomed ∧ outcome.FirstExistingHiddenRootHitAt ordinal |
      sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] +
      Pr[fun outcome => outcome.SuccessfulDoomed ∧ outcome.FirstExistingHiddenNonRootHitAt ordinal |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      (∑' table, Pr[= table | sampleOtsHashTable] * hiddenSelectionCharge
        (permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret (2 * q) table)) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold sampledObservedMaterializedDiagnostic
  simp only [probEvent_bind_eq_tsum sampleOtsHashTable, ← ENNReal.tsum_add, ← mul_add]
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro table
  rw [mul_assoc]
  apply mul_le_mul' le_rfl
  apply (add_le_add
    (probEvent_finishDiagnostic_successfulDoomed_firstExistingHiddenRootHitAt_le table _ ordinal)
    (probEvent_finishDiagnostic_successfulDoomed_firstExistingHiddenNonRootHitAt_le table _ ordinal)).trans
  exact probEvent_diagnosticOrdinal_pair_le_selectedCharge126 ordinal adversary parameter table ftsSecret q hordinal hfuel (hbound table) hq

theorem probEvent_sampledDiagnostic_successfulDoomed_le_selectionCharge126
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 126) :
    Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed |
      sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      sampledHiddenSelectionCharge adversary parameter ftsSecret q * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  have hfuel : 2 * q < Fintype.card Digest := by
    norm_num [digestBits] at hq ⊢
    omega
  let p := fun ordinal =>
    Pr[fun outcome => outcome.SuccessfulDoomed ∧ outcome.FirstExistingHiddenRootHitAt ordinal |
      sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] +
    Pr[fun outcome => outcome.SuccessfulDoomed ∧ outcome.FirstExistingHiddenNonRootHitAt ordinal |
      sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)]
  have hsplit : (∑ ordinal : Fin (2 * q), p ordinal.val) = ∑ ordinal : Fin q, p ordinal.val := by
    rw [show 2 * q = q + q by omega, Fin.sum_univ_add]
    change (∑ ordinal : Fin q, p ordinal.val) + (∑ ordinal : Fin q, p (q + ordinal.val)) = _
    have hzero : (∑ ordinal : Fin q, p (q + ordinal.val)) = 0 := by
      apply Finset.sum_eq_zero
      intro ordinal _
      unfold p
      rw [Range125.probEvent_sampledDiagnostic_successfulDoomed_firstRoot_eq_zero_of_q_le_ordinal
        adversary parameter ftsSecret q (q + ordinal.val) hbound hq (by omega),
        Range125.probEvent_sampledDiagnostic_successfulDoomed_firstNonRoot_eq_zero_of_q_le_ordinal
        adversary parameter ftsSecret q (q + ordinal.val) hbound hq (by omega), add_zero]
    rw [hzero, add_zero]
  apply (Range125.probEvent_sampledDiagnostic_successfulDoomed_le_sum_successfulFirstOrdinals
    adversary parameter ftsSecret q hq).trans
  change (∑ ordinal : Fin (2 * q), p ordinal.val) ≤ _
  rw [hsplit, sampledHiddenSelectionCharge, Finset.sum_mul]
  exact Finset.sum_le_sum fun ordinal _ => probEvent_sampledDiagnosticOrdinal_pair_le_selectedCharge126
    ordinal.val adversary parameter ftsSecret q ordinal.isLt hfuel hbound hq

end SphincsSecurity.Concrete.OtsProbeSimulation
