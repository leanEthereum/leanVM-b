import SphincsSecurity.Proof.OtsProbeDelayedRoot125

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

theorem le_mul_of_le_add_self_mul
    (probability epsilon fraction multiplier : ℝ≥0∞)
    (hprobability : probability ≤ 1) (hepsilon : epsilon ≠ ∞)
    (hfraction : fraction ≠ ∞) (hmultiplier : multiplier ≠ ∞)
    (hcoefficient : fraction * multiplier + 1 ≤ multiplier)
    (hbound : probability ≤ epsilon + probability * fraction) :
    probability ≤ multiplier * epsilon := by
  have hp : probability ≠ ∞ := ne_top_of_le_ne_top (by norm_num) hprobability
  have hb := (ENNReal.toReal_le_toReal hp (by finiteness)).mpr hbound
  have hc := (ENNReal.toReal_le_toReal (by finiteness) hmultiplier).mpr hcoefficient
  rw [ENNReal.toReal_add hepsilon (by finiteness), ENNReal.toReal_mul] at hb
  rw [ENNReal.toReal_add (by finiteness) (by norm_num), ENNReal.toReal_mul,
    ENNReal.toReal_one] at hc
  have hscaled := mul_le_mul_of_nonneg_right hb multiplier.toReal_nonneg
  have hcancel := mul_le_mul_of_nonneg_left hc probability.toReal_nonneg
  apply (ENNReal.toReal_le_toReal hp (by finiteness)).mp
  rw [ENNReal.toReal_mul]
  nlinarith

theorem probEvent_delayedRootFiber_le_mul_common
    (run : ProbComp PrivateWitnessSnapshotOutput)
    (common : ProbComp (Option PermissivePrivateOrdinalSelection))
    (ordinal q : Nat) (target : Position) (multiplier : ℝ≥0∞)
    (hordinal : ordinal < q) (hmultiplier : multiplier ≠ ∞)
    (hbudget : ((q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) * multiplier + 1 ≤
      multiplier)
    (hgood :
      Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
          DelayedRootGoodForComparisonAt result.1 ordinal target result.2 | do
        let source ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot)] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        common] * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    Pr[fun source => WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal source ∧
        delayedSnapshotLayerRootPosition? ordinal source = some target | run] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        common] * (multiplier * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by
  let probability := Pr[fun source =>
    WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal source ∧
      delayedSnapshotLayerRootPosition? ordinal source = some target | run]
  let weight := Pr[fun selection =>
    permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target | common]
  let epsilon := ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
  have hsplit := probEvent_delayedRootFiber_le_goodComparison_add_weightedException
    run ordinal target
  have hcoefficient : ((ordinal : ℝ≥0∞) * epsilon) * multiplier + 1 ≤ multiplier := by
    apply le_trans _ hbudget
    gcongr
  have hweightFinite : weight ≠ ∞ := ne_top_of_le_ne_top (by norm_num) probEvent_le_one
  have hepsilonFinite : epsilon ≠ ∞ := by dsimp [epsilon]; norm_num [digestBits]
  have hbound : probability ≤ multiplier * (weight * epsilon) := by
    apply le_mul_of_le_add_self_mul probability (weight * epsilon)
      ((ordinal : ℝ≥0∞) * epsilon) multiplier probEvent_le_one
      (by finiteness) (by finiteness) hmultiplier hcoefficient
    exact hsplit.trans (add_le_add hgood le_rfl)
  exact hbound.trans_eq (by dsimp [weight, epsilon]; ac_rfl)

theorem rootBudget_four_thirds {q : Nat} (hq : q ≤ 2 ^ 126) :
    ((q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) * (4 / 3 : ℝ≥0∞) + 1 ≤
      (4 / 3 : ℝ≥0∞) := by
  calc
    _ ≤ (((2 ^ 126 : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) *
        (4 / 3 : ℝ≥0∞) + 1 := by gcongr
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
      norm_num [digestBits]


theorem probEvent_canonical_delayedRootFiber_le_four_thirds_common
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) (target : Position)
    (hordinal : ordinal < q) (hq : q ≤ 2 ^ 126) :
    Pr[fun source => WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal source ∧
        delayedSnapshotLayerRootPosition? ordinal source = some target |
      granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret q table] * ((4 / 3) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by
  apply probEvent_delayedRootFiber_le_mul_common _ _ ordinal q target (4 / 3)
    hordinal (by finiteness) (rootBudget_four_thirds hq)
  exact probEvent_delayedGoodComparison_le_common_mul_allTargets ordinal adversary parameter
    table ftsSecret q target

end SphincsSecurity.Concrete.OtsProbeSimulation
