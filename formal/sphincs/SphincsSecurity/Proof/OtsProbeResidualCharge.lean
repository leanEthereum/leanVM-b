import SphincsSecurity.Proof.OtsProbeDiagnosticCharge
import SphincsSecurity.Proof.OtsProbeResidual125
import SphincsSecurity.Proof.OtsProbeRootBudget

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

noncomputable def residualSelectionCharge (common : ProbComp (Option PermissivePrivateOrdinalSelection)) : ℝ≥0∞ :=
  Pr[fun selection => (permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection).isSome = true | common] *
      (4 / 3) + Pr[PermissiveSelectionNonRoot | common]

theorem residualSelectionCharge_le_four_thirds (common : ProbComp (Option PermissivePrivateOrdinalSelection)) :
    residualSelectionCharge common ≤ 4 / 3 := by
  have hfactor : (1 : ℝ≥0∞) ≤ 4 / 3 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num
  unfold residualSelectionCharge
  calc
    _ ≤ Pr[fun selection => (permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection).isSome = true | common] *
          (4 / 3) + Pr[PermissiveSelectionNonRoot | common] * (4 / 3) :=
      add_le_add le_rfl (by simpa only [mul_one] using mul_le_mul' le_rfl hfactor)
    _ ≤ _ := by
      rw [← add_mul]
      exact mul_le_of_le_one_left (by positivity) (rootSelection_nonRootSelection_mass_le_one common)

theorem probEvent_canonical_delayedRoot_le_selectedCharge126
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) (hordinal : ordinal < q) (hq : q ≤ 2 ^ 126) :
    Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal |
      granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q] ≤
      Pr[fun selection => (permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection).isSome = true |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret q table] *
        ((4 / 3) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by
  apply Range125.probEvent_le_common_selected_mass
    (leftPosition := delayedSnapshotLayerRootPosition? ordinal)
    (common := delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret q table)
    (commonPosition := permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?)
  · intro output hdelayed
    obtain ⟨target, htarget⟩ := delayedSnapshotLayerRootPosition?_eq_some_of_delayed hdelayed
    rw [htarget]
    simp
  · intro target
    exact probEvent_canonical_delayedRootFiber_le_four_thirds_common ordinal adversary parameter table ftsSecret q target hordinal hq

theorem probEvent_residualOrdinal_pair_le_selectedCharge126
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) (hordinal : ordinal < q) (hq : q ≤ 2 ^ 126) :
    Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal |
      granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q] +
      Pr[fun output => WitnessFirstUsesNonLayerRootOrdinal ordinal (erasePrivateWitnessSnapshotOutput output) |
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q] ≤
      residualSelectionCharge
        (delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret q table) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply (add_le_add (probEvent_canonical_delayedRoot_le_selectedCharge126 ordinal adversary parameter table ftsSecret q hordinal hq)
    (probEvent_granularNonRootOrdinal_le_common_mass ordinal adversary parameter table ftsSecret q)).trans_eq
  unfold residualSelectionCharge
  rw [add_mul, mul_assoc]

noncomputable def sampledResidualSelectionCharge (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) : ℝ≥0∞ :=
  ∑ ordinal : Fin q, ∑' table, Pr[= table | sampleOtsHashTable] *
    residualSelectionCharge
      (delayedPermissiveDetailedSelectionExperimentAfterTable ordinal.val adversary parameter ftsSecret q table)

theorem probEvent_sampledResidualOrdinal_pair_le_selectedCharge126
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) (hordinal : ordinal < q) (hq : q ≤ 2 ^ 126) :
    Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal |
      sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] +
      Pr[fun output => WitnessFirstUsesNonLayerRootOrdinal ordinal (erasePrivateWitnessSnapshotOutput output) |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
      (∑' table, Pr[= table | sampleOtsHashTable] * residualSelectionCharge
        (delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret q table)) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot
  simp only [probEvent_bind_eq_tsum, ← ENNReal.tsum_add, ← mul_add]
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro table
  rw [mul_assoc]
  exact mul_le_mul' le_rfl
    (probEvent_residualOrdinal_pair_le_selectedCharge126 ordinal adversary parameter table ftsSecret q hordinal hq)

theorem probEvent_jointResidual_le_selectionCharge126
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 126) :
    Pr[JointSnapshotResidual | sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q] ≤
      sampledResidualSelectionCharge adversary parameter ftsSecret q * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [Range125.probEvent_jointResidual_eq_snapshot]
  apply (probEvent_or_le _ _ _).trans
  apply (add_le_add
    (probEvent_sampledCanonical_delayed_le_sum_ordinals adversary parameter ftsSecret q hbound)
    (probEvent_sampledCanonical_nonRoot_le_sum_ordinals adversary parameter ftsSecret q hbound)).trans
  rw [← Finset.sum_add_distrib, sampledResidualSelectionCharge, Finset.sum_mul]
  exact Finset.sum_le_sum fun ordinal _ =>
    probEvent_sampledResidualOrdinal_pair_le_selectedCharge126 ordinal.val adversary parameter ftsSecret q ordinal.isLt hq

theorem sampledResidualSelectionCharge_le_four_thirds_mul
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) :
    sampledResidualSelectionCharge adversary parameter ftsSecret q ≤ (4 / 3 : ℝ≥0∞) * q := by
  unfold sampledResidualSelectionCharge
  calc
    _ ≤ ∑ _ordinal : Fin q, (4 / 3 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro ordinal _
      apply (ENNReal.tsum_le_tsum fun table => mul_le_mul' le_rfl (residualSelectionCharge_le_four_thirds _)).trans
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one
    _ = _ := by simp [mul_comm]

end SphincsSecurity.Concrete.OtsProbeSimulation
