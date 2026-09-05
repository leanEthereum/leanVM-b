import SphincsSecurity.Proof.OtsProbeInitializedChargedRootReserve

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem initializedNativeDirectRisk_le_nativeProbeCharge
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    initializedNativeDirectRisk targets adversary parameter ftsSecret fuel q ≤
      (∑' table, Pr[= table | sampleOtsHashTable] *
        expectedLiveResolvedQueryCharge nativeProbeQueryCharge (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
          (ensuredInitialContext targets) fuel table) * ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  let computation := nativeChronologicalRetainedComputation adversary parameter ftsSecret
  have hstart := sum_sampledEnsuredNativeProbeCut_unresolvedStart_le_expectedChainStartCharge targets computation fuel q hq
  have hstruct : (∑' table, Pr[= table | sampleOtsHashTable] *
      ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
          runPrivateResolvedView target table (ensuredInitialContext targets) fuel (privatePositionProbeCutAt target computation ordinal)]) ≤
      (∑' table, Pr[= table | sampleOtsHashTable] *
        expectedLiveResolvedQueryCharge structuralProbeQueryCharge computation (ensuredInitialContext targets) fuel table) *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
    rw [← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro table
    rw [mul_assoc]
    exact mul_le_mul' le_rfl (sum_targets_privateHits_ensuredInitial_le_structuralCharge targets computation q fuel table hq)
  apply (add_le_add hstart hstruct).trans_eq
  rw [← add_mul, ← ENNReal.tsum_add]
  simp only [← mul_add, expectedLiveChainStart_add_structural_eq_probeCharge]
  rfl

noncomputable def initializedChargedRootRisk
    (targets roots : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat) : ENNReal :=
  ∑' table, Pr[= table | sampleOtsHashTable] *
    ∑ target ∈ roots, ∑ ordinal ∈ Finset.range q,
      Pr[fun b => b = false | initializedChargedRootCutObservation targets adversary parameter target table ftsSecret fuel ordinal
        (fun pair => pair.2 = some (truncateHash pair.1))]

theorem initializedChargedRootRisk_le_charge
    (targets roots : Finset Position) (hsubset : roots ⊆ targets)
    (hroot : ∀ target ∈ roots, IsLayerRoot target) (hne : ∀ target ∈ roots, target ≠ layerRootPosition topLayer rootTree)
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    initializedChargedRootRisk targets roots adversary parameter ftsSecret fuel q ≤
      (∑' table, Pr[= table | sampleOtsHashTable] * initializedChargedRootChargeAfterTable targets adversary parameter table ftsSecret fuel) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  unfold initializedChargedRootRisk
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro table
  rw [mul_assoc]
  exact mul_le_mul' le_rfl (sum_roots_initializedChargedRootCut_hits_le_charge targets roots hsubset hroot hne
    adversary parameter table ftsSecret fuel q hq)

theorem initializedNativeDirectRisk_add_chargedRootRisk_le_gameReserve
    (targets roots : Finset Position) (hsubset : roots ⊆ targets)
    (hroot : ∀ target ∈ roots, IsLayerRoot target) (hne : ∀ target ∈ roots, target ≠ layerRootPosition topLayer rootTree)
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    initializedNativeDirectRisk targets adversary parameter ftsSecret fuel q +
      initializedChargedRootRisk targets roots adversary parameter ftsSecret fuel q ≤
      (∑' table, Pr[= table | sampleOtsHashTable] *
        expectedQueryCharge (otsOpeningRefinedQueryReserve
          (primitiveAccountingKey parameter (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret))
          (gameAfterSecrets adversary parameter
            (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply (add_le_add (initializedNativeDirectRisk_le_nativeProbeCharge targets adversary parameter ftsSecret fuel q hq)
    (initializedChargedRootRisk_le_charge targets roots hsubset hroot hne adversary parameter ftsSecret fuel q hq)).trans
  rw [← mul_assoc, ← add_mul, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply mul_le_mul' _ le_rfl
  apply ENNReal.tsum_le_tsum
  intro table
  rw [mul_assoc, ← mul_add]
  exact mul_le_mul' le_rfl (initializedNativeProbe_add_chargedRootCharge_le_gameReserve targets adversary parameter table ftsSecret fuel)

end SphincsSecurity.Concrete.OtsProbeSimulation
