import SphincsSecurity.Proof.OtsProbeLiveGameCharge
import SphincsSecurity.Proof.OtsProbeEnsuredInitialization

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem initializedNative_joint_charge_le_gameDirectCharge
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    (expectedLiveResolvedQueryCharge chainStartProbeQueryCharge (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
        (ensuredInitialContext targets) fuel table +
      expectedLiveResolvedQueryCharge structuralProbeQueryCharge (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
        (ensuredInitialContext targets) fuel table) * (4 / 3 : ENNReal) ≤
      expectedQueryCharge (directOtsQueryCharge parameter)
        (gameAfterSecrets adversary parameter
          (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅ := by
  let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
  let actualCost := fun result : Digest × QueryCache HashSpec =>
    expectedQueryCharge (directOtsQueryCharge parameter)
      (gameRest scheme adversary ⟨result.1, parameter⟩ ⟨parameter, result.1, otsSecret, ftsSecret⟩) result.2
  have hroot := reachableResolvedCouples_maskedPublishedTreeRoot parameter table (ensuredInitialContext targets)
    fuel emptySplitHashCache ∅ (ensuredInitialContext_resolvedInvariant targets parameter table)
    (ensuredInitialContext_visible targets parameter table) (ensuredInitialContext_published targets)
  have hbound := expected_cost_le_of_relTriple hroot
    (fun left => liveResolvedContinuationCharge nativeProbeQueryCharge
      (fun rootCache : Digest × SplitHashCache =>
        (simulateQ (maskedChronologicalExpandedAdversaryImpl parameter rootCache.1 ftsSecret)
          (retainedGameRestComputation adversary ⟨rootCache.1, parameter⟩)).run rootCache.2) left * (4 / 3 : ENNReal))
    actualCost (fun _ => 0) (by
      intro left right hrelation
      simp only [add_zero]
      cases left with
      | none => simp [liveResolvedContinuationCharge]
      | some result =>
          dsimp only [liveResolvedContinuationCharge]
          rcases hrelation with hclean | hdoomed
          · rw [hclean.1]
            have hinvariant := hclean.2.2.1
            have hlocal := chronological_liveChainStart_add_structural_le_liveOuterCharge parameter result.value.1 ftsSecret
              (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩) result.context result.remaining table result.value.2
              hinvariant.2.1.valuesConsistent hinvariant.2.2.1
            rw [expectedLiveChainStart_add_structural_eq_probeCharge] at hlocal
            have hactual := expectedLiveChronologicalOtsCount_mul_le_directCharge parameter result.value.1 table ftsSecret
              (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩) result.context result.remaining result.value.2 right.2
              hinvariant hclean.2.2.2.1 hclean.2.2.2.2
            rw [expectedQueryCharge_retained_eq_gameRest] at hactual
            have htotal := (mul_le_mul' hlocal (le_refl (4 / 3 : ENNReal))).trans hactual
            simpa only [actualCost, ← hclean.2.1] using htotal
          · rw [hdoomed.1, expectedLiveResolvedQueryCharge_eq_zero_of_not_completable nativeProbeQueryCharge _
              result.context result.remaining table hdoomed.2.2.2, zero_mul]
            exact bot_le)
  rw [expectedLiveChainStart_add_structural_eq_probeCharge]
  unfold nativeChronologicalRetainedComputation
  rw [expectedLiveResolvedQueryCharge_bind _ _ _ _ fuel table (ensuredInitialContext_valid targets).valuesConsistent
      (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)),
    expectedLiveNativeProbeCharge_root_eq_zero, zero_add, ← ENNReal.tsum_mul_right]
  have hcost : (∑' result, Pr[= result | runResolvedFromTable (ensuredInitialContext targets) fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache)] *
        liveResolvedContinuationCharge nativeProbeQueryCharge
          (fun rootCache => (simulateQ (maskedChronologicalExpandedAdversaryImpl parameter rootCache.1 ftsSecret)
            (retainedGameRestComputation adversary ⟨rootCache.1, parameter⟩)).run rootCache.2) result * (4 / 3 : ENNReal)) ≤
      ∑' result, Pr[= result | (simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅] * actualCost result := by
    simpa only [liveResolvedContinuationCharge, treeRoot, otsSecret, mul_zero, tsum_zero, add_zero, mul_assoc] using hbound
  apply hcost.trans
  change _ ≤ expectedQueryCharge (directOtsQueryCharge parameter) (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅
  rw [gameAfterSecrets, expectedQueryCharge_bind, simulateQ_romImpl_liftM]
  exact le_add_self

noncomputable def initializedNativeDirectRisk
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat) : ENNReal :=
  (∑ ordinal ∈ Finset.range q, Pr[LiveUnresolvedStartHit nativeCutCandidate |
    sampledEnsuredNativeProbeCut targets (nativeChronologicalRetainedComputation adversary parameter ftsSecret) fuel ordinal]) +
  ∑' table, Pr[= table | sampleOtsHashTable] *
    ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table (ensuredInitialContext targets) fuel
          (privatePositionProbeCutAt target (nativeChronologicalRetainedComputation adversary parameter ftsSecret) ordinal)]

theorem initializedNativeDirectRisk_le_gameDirectCharge
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    initializedNativeDirectRisk targets adversary parameter ftsSecret fuel q ≤
      (∑' table, Pr[= table | sampleOtsHashTable] *
        expectedQueryCharge (directOtsQueryCharge parameter)
          (gameAfterSecrets adversary parameter
            (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
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
  apply (add_le_add hstart hstruct).trans
  rw [← add_mul, ← ENNReal.tsum_add]
  simp only [← mul_add]
  rw [← mul_assoc]
  apply mul_le_mul' _ le_rfl
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro table
  rw [mul_assoc]
  exact mul_le_mul' le_rfl (initializedNative_joint_charge_le_gameDirectCharge targets adversary parameter table ftsSecret fuel)

theorem uniformTable_gameDirectCharge_le_sampledSecrets
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (∑' table, Pr[= table | sampleOtsHashTable] *
      expectedQueryCharge (directOtsQueryCharge parameter)
        (gameAfterSecrets adversary parameter
          (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅) ≤
      ∑' otsSecret, Pr[= otsSecret | sampleOtsSecrets] *
        expectedQueryCharge (directOtsQueryCharge parameter) (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ := by
  have hbound := expected_cost_le_of_relTriple relTriple_uniformOtsHashTable_sampleOtsSecrets
    (fun table => expectedQueryCharge (directOtsQueryCharge parameter)
      (gameAfterSecrets adversary parameter
        (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅)
    (fun otsSecret => expectedQueryCharge (directOtsQueryCharge parameter)
      (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅)
    (fun _ => 0) (by
      intro table otsSecret hsecrets
      rw [← hsecrets, add_zero]
      exact le_rfl)
  simpa only [sampleOtsHashTable, mul_zero, tsum_zero, add_zero] using hbound

noncomputable def sampledInitializedNativeDirectRisk
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] * initializedNativeDirectRisk targets adversary parameter ftsSecret fuel q

theorem sampledInitializedNativeDirectRisk_le_directCharge
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    sampledInitializedNativeDirectRisk targets adversary fuel q ≤
      sampledQueryCharge (fun secretKey => directOtsQueryCharge secretKey.parameter) adversary *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ((∑' otsSecret, Pr[= otsSecret | sampleOtsSecrets] *
            expectedQueryCharge (directOtsQueryCharge parameter) (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅) *
            ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
      apply ENNReal.tsum_le_tsum
      intro parameter
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      apply mul_le_mul' le_rfl
      exact (initializedNativeDirectRisk_le_gameDirectCharge targets adversary parameter ftsSecret fuel q hq).trans
        (mul_le_mul' (uniformTable_gameDirectCharge_le_sampledSecrets adversary parameter ftsSecret) le_rfl)
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

theorem sampledInitializedNativeDirectRisk_add_remaining_le_refinedReserve
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    sampledInitializedNativeDirectRisk targets adversary fuel q +
      sampledQueryCharge remainingOtsQueryReserve adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ ≤
      sampledQueryCharge otsOpeningRefinedQueryReserve adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply (add_le_add (sampledInitializedNativeDirectRisk_le_directCharge targets adversary fuel q hq) le_rfl).trans_eq
  rw [← add_mul, sampled_direct_add_remaining_otsQueryReserve]

end SphincsSecurity.Concrete.OtsProbeSimulation
