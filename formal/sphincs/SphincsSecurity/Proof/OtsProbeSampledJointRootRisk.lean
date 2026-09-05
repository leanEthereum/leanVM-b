import SphincsSecurity.Proof.OtsProbeInitializedJointRootRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem uniformTable_gameRefinedReserve_le_sampledSecrets
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (∑' table, Pr[= table | sampleOtsHashTable] *
      expectedQueryCharge (otsOpeningRefinedQueryReserve
        (primitiveAccountingKey parameter (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret))
        (gameAfterSecrets adversary parameter
          (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅) ≤
      ∑' otsSecret, Pr[= otsSecret | sampleOtsSecrets] *
        expectedQueryCharge (otsOpeningRefinedQueryReserve (primitiveAccountingKey parameter otsSecret ftsSecret))
          (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ := by
  have hbound := expected_cost_le_of_relTriple relTriple_uniformOtsHashTable_sampleOtsSecrets
    (fun table => expectedQueryCharge (otsOpeningRefinedQueryReserve
      (primitiveAccountingKey parameter (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret))
      (gameAfterSecrets adversary parameter
        (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅)
    (fun otsSecret => expectedQueryCharge (otsOpeningRefinedQueryReserve (primitiveAccountingKey parameter otsSecret ftsSecret))
      (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅)
    (fun _ => 0) (by
      intro table otsSecret hsecrets
      rw [← hsecrets, add_zero]
      exact le_rfl)
  simpa only [sampleOtsHashTable, mul_zero, tsum_zero, add_zero] using hbound

noncomputable def sampledInitializedChargedRootRisk
    (targets roots : Finset Position) (adversary : Adversary) (fuel q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] * initializedChargedRootRisk targets roots adversary parameter ftsSecret fuel q

theorem sampledInitializedNativeDirectRisk_add_chargedRootRisk_le_refinedReserve
    (targets roots : Finset Position) (hsubset : roots ⊆ targets)
    (hroot : ∀ target ∈ roots, IsLayerRoot target) (hne : ∀ target ∈ roots, target ≠ layerRootPosition topLayer rootTree)
    (adversary : Adversary) (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    sampledInitializedNativeDirectRisk targets adversary fuel q +
      sampledInitializedChargedRootRisk targets roots adversary fuel q ≤
      sampledQueryCharge otsOpeningRefinedQueryReserve adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ = ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          (initializedNativeDirectRisk targets adversary parameter ftsSecret fuel q +
            initializedChargedRootRisk targets roots adversary parameter ftsSecret fuel q) := by
      simp only [sampledInitializedNativeDirectRisk, sampledInitializedChargedRootRisk, mul_add, ENNReal.tsum_add]
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ((∑' otsSecret, Pr[= otsSecret | sampleOtsSecrets] *
            expectedQueryCharge (otsOpeningRefinedQueryReserve (primitiveAccountingKey parameter otsSecret ftsSecret))
              (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
      apply ENNReal.tsum_le_tsum
      intro parameter
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      apply mul_le_mul' le_rfl
      exact (initializedNativeDirectRisk_add_chargedRootRisk_le_gameReserve targets roots hsubset hroot hne
        adversary parameter ftsSecret fuel q hq).trans
          (mul_le_mul' (uniformTable_gameRefinedReserve_le_sampledSecrets adversary parameter ftsSecret) le_rfl)
    _ = _ := by
      unfold sampledQueryCharge
      simp only [sampleSecrets, tsum_probOutput_bind_mul, tsum_probOutput_pure_mul, primitiveAccountingKey]
      simp only [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right, mul_assoc]
      apply tsum_congr
      intro parameter
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro otsSecret
      apply tsum_congr
      intro ftsSecret
      ring

end SphincsSecurity.Concrete.OtsProbeSimulation
