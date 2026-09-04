import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedRootClosed

namespace SphincsSecurity.Concrete.OtsProbeSimulation.Range125

open OracleComp OracleSpec ENNReal

set_option linter.constructorNameAsVariable false

attribute [local irreducible] WitnessFirstUsesDelayedLayerRootSnapshotOrdinal
  delayedSnapshotLayerRootPosition? DelayedRootGoodForComparisonAt
  permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?

theorem ordinal_mul_inv_digest_le_inv_eight
    (ordinal q : Nat) (hordinal : ordinal < q) (hq : q ≤ 2 ^ 125) :
    (ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ ≤
      (8 : ENNReal)⁻¹ := by
  calc
    (ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ ≤
        ((2 ^ 125 : Nat) : ENNReal) *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      gcongr
      exact_mod_cast (Nat.le_of_lt (hordinal.trans_le hq))
    _ ≤ (8 : ENNReal)⁻¹ := by
      rw [ENNReal.mul_inv_le_iff (by norm_num) (by norm_num)]
      apply (ENNReal.toReal_le_toReal (by norm_num) (by finiteness)).mp
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
      norm_num [digestBits]

theorem le_eight_sevenths_mul_of_le_add_mul_inv_eight
    (probability epsilon : ℝ≥0∞)
    (hprobability : probability ≤ 1) (hepsilon : epsilon ≠ ∞)
    (hbound : probability ≤ epsilon + probability * (8 : ℝ≥0∞)⁻¹) :
    probability ≤ (8 / 7) * epsilon := by
  have hprobabilityFinite : probability ≠ ∞ := by
    exact ne_top_of_le_ne_top (by norm_num) hprobability
  have hfractionFinite : probability * (8 : ℝ≥0∞)⁻¹ ≠ ∞ := by finiteness
  have hsumFinite : epsilon + probability * (8 : ℝ≥0∞)⁻¹ ≠ ∞ := by finiteness
  have hrightFinite : (8 / 7 : ℝ≥0∞) * epsilon ≠ ∞ := by finiteness
  have hreal : probability.toReal ≤
      epsilon.toReal + probability.toReal * (8 : ℝ)⁻¹ := by
    have := (ENNReal.toReal_le_toReal hprobabilityFinite hsumFinite).mpr hbound
    simpa [ENNReal.toReal_add hepsilon hfractionFinite, ENNReal.toReal_mul,
      ENNReal.toReal_inv] using this
  apply (ENNReal.toReal_le_toReal hprobabilityFinite hrightFinite).mp
  rw [ENNReal.toReal_mul]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
  linarith


set_option maxRecDepth 100000 in
theorem probEvent_delayedRootFiber_le_eight_sevenths_mul_common
    (run : ProbComp PrivateWitnessSnapshotOutput)
    (common : ProbComp (Option PermissivePrivateOrdinalSelection))
    (ordinal q : Nat) (target : Position)
    (hordinal : ordinal < q) (hq : q ≤ 2 ^ 125)
    (hgood :
      Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
          DelayedRootGoodForComparisonAt result.1 ordinal target result.2 | do
        let source ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot)] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        common] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[fun source =>
        WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal source ∧
          delayedSnapshotLayerRootPosition? ordinal source = some target | run] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        common] * ((8 / 7) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  let probability := Pr[fun source =>
      WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal source ∧
        delayedSnapshotLayerRootPosition? ordinal source = some target | run]
  let weight := Pr[fun selection =>
      permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
    common]
  let epsilon := ((2 ^ digestBits : Nat) : ENNReal)⁻¹
  have hsplit : probability ≤
      Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
          DelayedRootGoodForComparisonAt result.1 ordinal target result.2 | do
        let source ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot)] +
      probability * ((ordinal : ENNReal) * epsilon) := by
    exact probEvent_delayedRootFiber_le_goodComparison_add_weightedException
      run ordinal target
  have hfraction : (ordinal : ENNReal) * epsilon ≤ (8 : ENNReal)⁻¹ := by
    exact ordinal_mul_inv_digest_le_inv_eight ordinal q hordinal hq
  have habsorb : probability ≤ (8 / 7) * (weight * epsilon) := by
    apply le_eight_sevenths_mul_of_le_add_mul_inv_eight probability (weight * epsilon)
    · exact probEvent_le_one
    · apply ne_top_of_le_ne_top (by norm_num : (1 : ENNReal) ≠ ∞)
      calc
        weight * epsilon ≤ 1 * 1 := by
          apply mul_le_mul probEvent_le_one
          · simp [epsilon, digestBits]
          · exact bot_le
          · exact bot_le
        _ = 1 := one_mul 1
    · have hweighted : probability * ((ordinal : ENNReal) * epsilon) ≤
          probability * (8 : ENNReal)⁻¹ := mul_le_mul' le_rfl hfraction
      exact hsplit.trans (add_le_add hgood hweighted)
  change probability ≤ weight * ((8 / 7) * epsilon)
  calc
    probability ≤ (8 / 7) * (weight * epsilon) := habsorb
    _ = weight * ((8 / 7) * epsilon) := by ac_rfl

theorem probEvent_granularAllCanonical_delayedOrdinal_le_eight_sevenths_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hordinal : ordinal < q) (hq : q ≤ 2 ^ 125)
    (hgood : ∀ target,
      Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
          DelayedRootGoodForComparisonAt result.1 ordinal target result.2 | do
        let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
          ftsSecret q
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot)] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret q table] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal |
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q] ≤
      (8 / 7) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply probEvent_le_of_common_position_fibers
    (leftPosition := delayedSnapshotLayerRootPosition? ordinal)
    (common := delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
      ftsSecret q table)
    (commonPosition := permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?)
  · intro output hdelayed
    obtain ⟨target, htarget⟩ :=
      delayedSnapshotLayerRootPosition?_eq_some_of_delayed hdelayed
    rw [htarget]
    simp
  · intro target
    exact probEvent_delayedRootFiber_le_eight_sevenths_mul_common
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q)
      (delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
        ftsSecret q table)
      ordinal q target hordinal hq (hgood target)

theorem probEvent_sampledCanonical_delayedOrdinal_le_eight_sevenths_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hordinal : ordinal < q) (hq : q ≤ 2 ^ 125)
    (hgood : ∀ table target,
      Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
          DelayedRootGoodForComparisonAt result.1 ordinal target result.2 | do
        let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
          ftsSecret q
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot)] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret q table] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
      (8 / 7) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot
  apply probEvent_bind_le_of_forall_le
  intro table _htable
  exact probEvent_granularAllCanonical_delayedOrdinal_le_eight_sevenths_mul ordinal adversary parameter table
    ftsSecret q hordinal hq (hgood table)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledCanonical_delayed_le_eight_sevenths_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125)
    (hgood : ∀ (ordinal : Fin q) table target,
      Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
          DelayedRootGoodForComparisonAt result.1 ordinal.val target result.2 | do
        let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
          ftsSecret q
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot)] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal.val adversary parameter
          ftsSecret q table] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[WitnessFirstUsesSomeDelayedLayerRootSnapshot |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
      ((8 / 7) * q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ ∑ ordinal : Fin q,
        Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal.val |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] :=
      probEvent_sampledCanonical_delayed_le_sum_ordinals adversary parameter ftsSecret q hbound
    _ ≤ ∑ _ordinal : Fin q, (8 / 7) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      exact Finset.sum_le_sum fun ordinal _ =>
        probEvent_sampledCanonical_delayedOrdinal_le_eight_sevenths_mul ordinal.val adversary parameter
          ftsSecret q ordinal.isLt hq (hgood ordinal)
    _ = _ := by
      simp
      ring

theorem probEvent_sampledCanonical_delayed_le_eight_sevenths_mul_closed
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[WitnessFirstUsesSomeDelayedLayerRootSnapshot |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
      ((8 / 7) * q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply probEvent_sampledCanonical_delayed_le_eight_sevenths_mul adversary parameter ftsSecret q hbound hq
  intro ordinal table target
  exact probEvent_delayedGoodComparison_le_common_mul_allTargets ordinal.val adversary parameter
    table ftsSecret q target


end SphincsSecurity.Concrete.OtsProbeSimulation.Range125
