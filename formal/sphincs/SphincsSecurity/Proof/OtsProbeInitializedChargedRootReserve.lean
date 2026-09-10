import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeCanonicalChargeGame
import SphincsSecurity.Proof.OtsProbeInitializedChargedRootGlobalRisk
import SphincsSecurity.Proof.OtsProbeLiveGameCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem initializedNativeProbe_add_chargedRootCharge_le_gameReserve
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    expectedLiveResolvedQueryCharge nativeProbeQueryCharge (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
        (ensuredInitialContext targets) fuel table * (4 / 3 : ENNReal) +
      initializedChargedRootChargeAfterTable targets adversary parameter table ftsSecret fuel ≤
      expectedQueryCharge (otsOpeningRefinedQueryReserve
        (primitiveAccountingKey parameter (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret))
        (gameAfterSecrets adversary parameter
          (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅ := by
  let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
  let accountingKey := primitiveAccountingKey parameter otsSecret ftsSecret
  let continuation := fun rootCache : Digest × SplitHashCache =>
    (simulateQ (maskedChronologicalExpandedAdversaryImpl parameter rootCache.1 ftsSecret)
      (retainedGameRestComputation adversary ⟨rootCache.1, parameter⟩)).run rootCache.2
  let rootCharge := fun result : Option (ResolvedRunResult (Digest × SplitHashCache)) =>
    match result with
    | none => 0
    | some result => expectedLiveNativeContextCharge
        (maskedChronologicalExpandedAdversaryImpl parameter result.value.1 ftsSecret) (chargedRootOuterCharge parameter)
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩) result.context result.remaining table result.value.2
  let actualCost := fun result : Digest × QueryCache HashSpec =>
    expectedQueryCharge (otsOpeningRefinedQueryReserve accountingKey)
      (gameRest scheme adversary ⟨result.1, parameter⟩ ⟨parameter, result.1, otsSecret, ftsSecret⟩) result.2
  have hroot := reachableResolvedCouples_maskedPublishedTreeRoot parameter table (ensuredInitialContext targets)
    fuel emptySplitHashCache ∅ (ensuredInitialContext_resolvedInvariant targets parameter table)
    (ensuredInitialContext_visible targets parameter table) (ensuredInitialContext_published targets)
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hroot
    (fun left => ∀ result, left = some result → DeferredComputationsClosed result.context ∧ LayerRootsMaterialized result.context) (by
      intro left hleft result heq
      subst left
      exact ⟨(ensuredInitialContext_computed targets).of_mem_runResolved _ _ fuel table result hleft,
        rootMaterializationPreserving_maskedPublishedTreeRoot (ensuredInitialContext targets) fuel table emptySplitHashCache result
          (layerRootsMaterialized_ensuredInitialContext targets) (ensuredInitialContext_computed targets) hleft⟩)
  have hbound := expected_cost_le_of_relTriple hsupported
    (fun left => liveResolvedContinuationCharge nativeProbeQueryCharge continuation left * (4 / 3 : ENNReal) + rootCharge left)
    actualCost (fun _ => 0) (by
      intro left right hrelation
      simp only [add_zero]
      cases left with
      | none => simp [liveResolvedContinuationCharge, rootCharge]
      | some result =>
          dsimp only [liveResolvedContinuationCharge, rootCharge]
          rcases hrelation.1 with hclean | hdoomed
          · rw [hclean.1]
            have hfacts := hrelation.2 result rfl
            have hlocal := chronological_liveProbe_add_chargedRoots_le_refinedReserve parameter result.value.1 table ftsSecret
              (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩) result.context result.remaining result.value.2 right.2
              hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2 hfacts.1 hfacts.2
            have hreserve : otsOpeningRefinedQueryReserve (⟨parameter, result.value.1, otsSecret, ftsSecret⟩ : SecretKey) =
                otsOpeningRefinedQueryReserve accountingKey := otsOpeningRefinedQueryReserve_set_root accountingKey result.value.1
            dsimp only at hlocal
            dsimp only [otsSecret] at hreserve
            rw [hreserve, expectedQueryCharge_retained_eq_gameRest] at hlocal
            simpa only [continuation, actualCost, ← hclean.2.1] using hlocal
          · rw [hdoomed.1, expectedLiveResolvedQueryCharge_eq_zero_of_not_completable nativeProbeQueryCharge _
              result.context result.remaining table hdoomed.2.2.2,
              expectedLiveNativeContextCharge_eq_zero_of_not_completable _ _ _ _ _ _ _ hdoomed.2.2.2]
            simp)
  unfold nativeChronologicalRetainedComputation initializedChargedRootChargeAfterTable
  rw [expectedLiveResolvedQueryCharge_bind _ _ _ _ fuel table (ensuredInitialContext_valid targets).valuesConsistent
      (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)),
    expectedLiveNativeProbeCharge_root_eq_zero, zero_add, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  have hcost : (∑' result, Pr[= result | runResolvedFromTable (ensuredInitialContext targets) fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache)] *
        (liveResolvedContinuationCharge nativeProbeQueryCharge continuation result * (4 / 3 : ENNReal) + rootCharge result)) ≤
      ∑' result, Pr[= result | (simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅] * actualCost result := by
    simpa only [treeRoot, otsSecret, mul_zero, tsum_zero, add_zero] using hbound
  calc
    _ = ∑' result, Pr[= result | runResolvedFromTable (ensuredInitialContext targets) fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache)] *
          (liveResolvedContinuationCharge nativeProbeQueryCharge continuation result * (4 / 3 : ENNReal) + rootCharge result) := by
      apply tsum_congr
      intro result
      simp only [continuation, rootCharge, mul_add, mul_assoc]
      rfl
    _ ≤ ∑' result, Pr[= result | (simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅] * actualCost result := hcost
    _ ≤ _ := by
      change _ ≤ expectedQueryCharge (otsOpeningRefinedQueryReserve accountingKey) (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅
      rw [gameAfterSecrets, expectedQueryCharge_bind, simulateQ_romImpl_liftM]
      exact le_add_self

end SphincsSecurity.Concrete.OtsProbeSimulation
