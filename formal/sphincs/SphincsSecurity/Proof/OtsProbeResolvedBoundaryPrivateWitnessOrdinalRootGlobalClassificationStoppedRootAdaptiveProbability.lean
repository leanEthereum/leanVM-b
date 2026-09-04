import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveEndpoint
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootJoint

/-!
# Absorbed fixed-root probability

The independent comparison root can coincide with one of the earlier candidates. For a source
ordinal below the query bound this exception has coefficient at most one half, so it is absorbed
without discarding the target-specific production weight.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

theorem ordinal_mul_inv_digest_le_inv_two
    (ordinal q : Nat) (hordinal : ordinal < q) (hq : q ≤ 2 ^ securityBits) :
    (ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ ≤
      (2 : ENNReal)⁻¹ := by
  calc
    (ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ ≤
        ((2 ^ securityBits : Nat) : ENNReal) *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      gcongr
      exact_mod_cast (Nat.le_of_lt (hordinal.trans_le hq))
    _ ≤ (2 : ENNReal)⁻¹ := by
      rw [ENNReal.mul_inv_le_iff (by norm_num) (by norm_num)]
      apply (ENNReal.toReal_le_toReal (by norm_num) (by finiteness)).mp
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
      norm_num [securityBits, digestBits]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_successfulDoomedFirstRootFiber_le_two_mul_production
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (hordinal : ordinal < q)
    (hfuel : 2 * q < Fintype.card Digest)
    (hbound : ∀ root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[fun observed =>
        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
          table ordinal target observed |
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
          materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target (2 * q) table] *
        (2 * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  let run := observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table
  let probability := Pr[fun observed =>
      ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
        table ordinal target observed | run]
  let weight := Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
      materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
        ftsSecret target (2 * q) table]
  let epsilon := ((2 ^ digestBits : Nat) : ENNReal)⁻¹
  have hgood :
      Pr[fun result : Option
            (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest ↦
          ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
            table ordinal target result.2 result.1 | do
        let observed ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot)] ≤ weight * epsilon := by
    exact probEvent_observedRootComparison_le_production_mul ordinal adversary parameter table
      ftsSecret q target hroot hparent hfuel hbound hq
  have hsplit : probability ≤
      Pr[fun result : Option
            (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest =>
          ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
            table ordinal target result.2 result.1 | do
        let observed ← run
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot)] +
      probability *
        ((ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
    exact probEvent_successfulDoomedFirstRootFiber_le_goodComparison_add_weightedException
      table run ordinal target
  have hhalf :
      (ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ ≤
        (2 : ENNReal)⁻¹ :=
    ordinal_mul_inv_digest_le_inv_two ordinal q hordinal hq
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
            Pr[fun result : Option
                  (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest =>
                ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
                  table ordinal target result.2 result.1 | do
              let observed ← run
              let rightRoot ← ($ᵗ Digest : ProbComp Digest)
              pure (observed, rightRoot)] +
            probability *
              ((ordinal : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := hsplit
        _ ≤ weight * epsilon + probability * (2 : ENNReal)⁻¹ := by
          exact add_le_add hgood (mul_le_mul_right hhalf probability)
  change probability ≤ weight * (2 * epsilon)
  calc
    probability ≤ 2 * (weight * epsilon) := habsorb
    _ = weight * (2 * epsilon) := by ac_rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
