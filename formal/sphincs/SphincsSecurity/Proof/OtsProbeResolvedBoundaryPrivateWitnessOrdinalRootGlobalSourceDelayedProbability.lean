import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedComparison
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedRootProduction
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedRootSwapEncoding

/-!
# Delayed source probability assembly

The comparison-root exception is absorbed before target fibers are summed. This file packages the
position, table and ordinal arithmetic around the remaining weight-preserving selector coupling.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_delayedRootFiber_le_two_mul_common
    (run : ProbComp PrivateWitnessSnapshotOutput)
    (common : ProbComp (Option PermissivePrivateOrdinalSelection))
    (ordinal q : Nat) (target : Position)
    (hordinal : ordinal < q) (hq : q ≤ 2 ^ securityBits)
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
        common] * (2 * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
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
  have hhalf : (ordinal : ENNReal) * epsilon ≤ (2 : ENNReal)⁻¹ := by
    exact ordinal_mul_inv_digest_le_inv_two ordinal q hordinal hq
  have habsorb : probability ≤ 2 * (weight * epsilon) := by
    apply le_two_mul_of_le_add_mul_inv_two probability (weight * epsilon)
    · exact probEvent_le_one
    · apply ne_top_of_le_ne_top (by norm_num : (1 : ENNReal) ≠ ∞)
      calc
        weight * epsilon ≤ 1 * 1 := by
          apply mul_le_mul probEvent_le_one
          · simp [epsilon, digestBits]
          · exact bot_le
          · exact bot_le
        _ = 1 := one_mul 1
    · calc
        probability ≤
            Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
                DelayedRootGoodForComparisonAt result.1 ordinal target result.2 | do
              let source ← run
              let rightRoot ← ($ᵗ Digest : ProbComp Digest)
              pure (source, rightRoot)] +
              probability * ((ordinal : ENNReal) * epsilon) := hsplit
        _ ≤ weight * epsilon + probability * (2 : ENNReal)⁻¹ := by
          exact add_le_add hgood (mul_le_mul_right hhalf probability)
  change probability ≤ weight * (2 * epsilon)
  calc
    probability ≤ 2 * (weight * epsilon) := habsorb
    _ = weight * (2 * epsilon) := by ac_rfl

theorem probEvent_granularAllCanonical_delayedOrdinal_le_two_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hordinal : ordinal < q) (hq : q ≤ 2 ^ securityBits)
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
      2 * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
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
    exact probEvent_delayedRootFiber_le_two_mul_common
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q)
      (delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
        ftsSecret q table)
      ordinal q target hordinal hq (hgood target)

theorem probEvent_sampledCanonical_delayedOrdinal_le_two_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hordinal : ordinal < q) (hq : q ≤ 2 ^ securityBits)
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
      2 * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot
  apply probEvent_bind_le_of_forall_le
  intro table _htable
  exact probEvent_granularAllCanonical_delayedOrdinal_le_two_mul ordinal adversary parameter table
    ftsSecret q hordinal hq (hgood table)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledCanonical_delayed_le_two_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (hq : q ≤ 2 ^ securityBits)
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
      (2 * q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ ∑ ordinal : Fin q,
        Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal.val |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] :=
      probEvent_sampledCanonical_delayed_le_sum_ordinals adversary parameter ftsSecret q hbound
    _ ≤ ∑ _ordinal : Fin q, 2 * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      exact Finset.sum_le_sum fun ordinal _ =>
        probEvent_sampledCanonical_delayedOrdinal_le_two_mul ordinal.val adversary parameter
          ftsSecret q ordinal.isLt hq (hgood ordinal)
    _ = _ := by
      simp
      ring

end SphincsSecurity.Concrete.OtsProbeSimulation
