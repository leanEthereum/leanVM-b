import SphincsSecurity.Proof.OtsProbePrivateWeightedRisk
import SphincsSecurity.Proof.OtsProbeInitializedGameCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem initializedNative_joint_probe_count_le_actual_ots_count
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    expectedLiveResolvedQueryCharge chainStartProbeQueryCharge (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
        (ensuredInitialContext targets) fuel table +
      expectedLiveResolvedQueryCharge structuralProbeQueryCharge (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
        (ensuredInitialContext targets) fuel table ≤
      expectedQueryCharge (fun _ input => otsHashInputCharge parameter input)
        (gameAfterSecrets adversary parameter
          (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅ := by
  have hbound := initializedNative_joint_charge_le_gameDirectCharge targets adversary parameter table ftsSecret fuel
  unfold directOtsQueryCharge at hbound
  rw [expectedQueryCharge_mul] at hbound
  have hcancel : (4 / 3 : ENNReal) * (3 / 4) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  simpa only [mul_assoc, hcancel, mul_one] using mul_le_mul' hbound (le_refl (3 / 4 : ENNReal))

theorem sum_targets_privateHits_ensuredInitial_le_historyRate
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q fuel : Nat) (table : OtsSecretIndex → HashOutput) (hq : q < Fintype.card Digest) :
    (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table (ensuredInitialContext targets) fuel (privatePositionProbeCutAt target computation ordinal)]) ≤
      expectedLiveResolvedQueryCharge structuralProbeQueryCharge computation (ensuredInitialContext targets) fuel table *
        privateHistoryGuessRate q := by
  apply sum_targets_privateHits_le_live_structural_rate targets computation q (ensuredInitialContext targets) fuel table q
    (ensuredInitialContext_valid targets) (ensuredInitialContext_completable targets table)
    (ensuredInitialContext_mem_ensured targets)
  · intro target _
    rfl
  · intro target _
    rfl
  · intro target _
    simp [ensuredInitialContext, LazyRevealProbe.State.empty]
  · intro target _
    simp [ensuredInitialContext, LazyRevealProbe.State.empty, LazyRevealProbe.State.pendingAt]
  · exact hq

noncomputable def sampledInitializedPrivateHitRisk
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | sampleOtsHashTable] *
        ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
          Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
            runPrivateResolvedView target table (ensuredInitialContext targets) fuel
              (privatePositionProbeCutAt target (nativeChronologicalRetainedComputation adversary parameter ftsSecret) ordinal)]

theorem uniformTable_actualOtsCount_le_sampledSecrets
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (∑' table, Pr[= table | sampleOtsHashTable] *
      expectedQueryCharge (fun _ input => otsHashInputCharge parameter input)
        (gameAfterSecrets adversary parameter
          (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅) ≤
      ∑' otsSecret, Pr[= otsSecret | sampleOtsSecrets] *
        expectedQueryCharge (fun _ input => otsHashInputCharge parameter input)
          (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ := by
  have hbound := expected_cost_le_of_relTriple relTriple_uniformOtsHashTable_sampleOtsSecrets
    (fun table => expectedQueryCharge (fun _ input => otsHashInputCharge parameter input)
      (gameAfterSecrets adversary parameter
        (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅)
    (fun otsSecret => expectedQueryCharge (fun _ input => otsHashInputCharge parameter input)
      (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅)
    (fun _ => 0) (by
      intro table otsSecret hsecrets
      rw [← hsecrets, add_zero]
      exact le_rfl)
  simpa only [sampleOtsHashTable, mul_zero, tsum_zero, add_zero] using hbound

theorem sampledInitializedPrivateHitRisk_le_actualOtsCount
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : q < Fintype.card Digest) :
    sampledInitializedPrivateHitRisk targets adversary fuel q ≤
      sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary *
        privateHistoryGuessRate q := by
  calc
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ((∑' otsSecret, Pr[= otsSecret | sampleOtsSecrets] *
            expectedQueryCharge (fun _ input => otsHashInputCharge parameter input)
              (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅) * privateHistoryGuessRate q) := by
      apply ENNReal.tsum_le_tsum
      intro parameter
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      apply mul_le_mul' le_rfl
      apply le_trans _ (mul_le_mul' (uniformTable_actualOtsCount_le_sampledSecrets adversary parameter ftsSecret) le_rfl)
      rw [← ENNReal.tsum_mul_right]
      apply ENNReal.tsum_le_tsum
      intro table
      rw [mul_assoc]
      apply mul_le_mul' le_rfl
      apply (sum_targets_privateHits_ensuredInitial_le_historyRate targets
        (nativeChronologicalRetainedComputation adversary parameter ftsSecret) q fuel table hq).trans
      apply mul_le_mul' _ le_rfl
      exact (le_add_self : _ ≤ _ + _).trans
        (initializedNative_joint_probe_count_le_actual_ots_count targets adversary parameter table ftsSecret fuel)
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

theorem sampledInitializedPrivateHitRisk_le_actualOtsCount127
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : q ≤ 2 ^ 127) :
    sampledInitializedPrivateHitRisk targets adversary fuel q ≤
      sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary *
        ((2 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  apply (sampledInitializedPrivateHitRisk_le_actualOtsCount targets adversary fuel q
    (hq.trans_lt (by norm_num [digestBits]))).trans
  exact mul_le_mul' le_rfl (privateHistoryGuessRate_le_two hq)

theorem sampledInitializedPrivateHitRisk_le_queryBudget
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat)
    (hq : HasHashQueryBound scheme adversary q) (hqSpace : q < Fintype.card Digest) :
    sampledInitializedPrivateHitRisk targets adversary fuel q ≤ (q : ENNReal) * privateHistoryGuessRate q := by
  apply (sampledInitializedPrivateHitRisk_le_actualOtsCount targets adversary fuel q hqSpace).trans
  apply mul_le_mul' _ le_rfl
  simpa only [one_mul] using sampledQueryCharge_le_const
    (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) 1 (by
      intro secretKey cache input
      unfold otsHashInputCharge
      split_ifs <;> simp) adversary q hq

theorem sampledInitializedNativeDirectRisk_eq_start_add_private
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) :
    sampledInitializedNativeDirectRisk targets adversary fuel q =
      (∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ∑ ordinal ∈ Finset.range q, Pr[LiveUnresolvedStartHit nativeCutCandidate |
            sampledEnsuredNativeProbeCut targets (nativeChronologicalRetainedComputation adversary parameter ftsSecret) fuel ordinal]) +
      sampledInitializedPrivateHitRisk targets adversary fuel q := by
  unfold sampledInitializedNativeDirectRisk initializedNativeDirectRisk sampledInitializedPrivateHitRisk
  simp_rw [mul_add, ENNReal.tsum_add]
  simp only [mul_add, ENNReal.tsum_add]

theorem sampledInitializedNativeDirectRisk_le_start_add_historyRate
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : q < Fintype.card Digest) :
    sampledInitializedNativeDirectRisk targets adversary fuel q ≤
      (∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ∑ ordinal ∈ Finset.range q, Pr[LiveUnresolvedStartHit nativeCutCandidate |
            sampledEnsuredNativeProbeCut targets (nativeChronologicalRetainedComputation adversary parameter ftsSecret) fuel ordinal]) +
      sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary *
        privateHistoryGuessRate q := by
  rw [sampledInitializedNativeDirectRisk_eq_start_add_private]
  exact add_le_add le_rfl (sampledInitializedPrivateHitRisk_le_actualOtsCount targets adversary fuel q hq)

end SphincsSecurity.Concrete.OtsProbeSimulation
