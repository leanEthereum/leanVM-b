import SphincsSecurity.Proof.OtsProbeRootMaterializationChronological
import SphincsSecurity.Proof.OtsProbeNativeQueryTraceProjection
import SphincsSecurity.Proof.OtsProbeNativeRootJointReserve

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem canonicalTraceCharge_materialized_eq_known
    (parameter : PublicParameter) (history : List CanonicalQuerySelection)
    (hmat : ∀ selection ∈ history, LayerRootsMaterialized selection.context) :
    canonicalTraceCharge (materializedEncodingRootOuterCharge parameter) history =
      canonicalTraceCharge (knownEncodingRootOuterCharge parameter) history := by
  unfold canonicalTraceCharge
  apply congrArg List.sum
  apply List.map_congr_left
  intro selection hselection
  exact materializedEncodingRootOuterCharge_eq_known parameter selection.input selection.context selection.fuel selection.cache
    (hmat selection hselection)

theorem expectedLiveMaterializedRootCharge_eq_known
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hmat : LayerRootsMaterialized context) (hclosed : DeferredComputationsClosed context) :
    expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
      (materializedEncodingRootOuterCharge parameter) computation context fuel table cache =
    expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
      (knownEncodingRootOuterCharge parameter) computation context fuel table cache := by
  rw [← expectedNativeTraceCharge_eq, ← expectedNativeTraceCharge_eq]
  apply tsum_congr
  intro trace
  by_cases htrace : trace ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)
  · rw [canonicalTraceCharge_materialized_eq_known parameter trace.2
      (layerRootsMaterialized_runNativeQueryTrace parameter root ftsSecret computation context fuel table cache trace hmat hclosed htrace).2]
  · rw [probOutput_eq_zero_of_not_mem_support htrace]
    simp

theorem chronological_liveProbe_add_materializedRoots_le_refinedReserve
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context)
    (hmat : LayerRootsMaterialized context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    (expectedLiveResolvedQueryCharge nativeProbeQueryCharge
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) context fuel table +
      expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (knownStructuralRootOuterCharge parameter) computation context fuel table cache) * (4 / 3 : ENNReal) +
      expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (materializedEncodingRootOuterCharge parameter) computation context fuel table cache ≤
      expectedQueryCharge (otsOpeningRefinedQueryReserve secretKey)
        (simulateQ (expandedAdversaryImpl secretKey) computation) actualCache := by
  dsimp only
  rw [expectedLiveMaterializedRootCharge_eq_known parameter root ftsSecret computation context fuel table cache hmat hcomputed]
  exact chronological_liveProbe_add_knownRoots_le_refinedReserve parameter root table ftsSecret computation context fuel cache actualCache
    hinvariant hvisible hpublished hcomputed

noncomputable def initializedMaterializedRootChargeAfterTable
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ENNReal :=
  ∑' result, Pr[= result | runResolvedFromTable (ensuredInitialContext targets) fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)] *
    match result with
    | none => 0
    | some result => expectedLiveNativeContextCharge
        (maskedChronologicalExpandedAdversaryImpl parameter result.value.1 ftsSecret) (materializedEncodingRootOuterCharge parameter)
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
        result.context result.remaining table result.value.2

theorem initializedMaterializedRootChargeAfterTable_eq_known
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    initializedMaterializedRootChargeAfterTable targets adversary parameter table ftsSecret fuel =
      initializedKnownRootChargeAfterTable targets adversary parameter table ftsSecret fuel := by
  unfold initializedMaterializedRootChargeAfterTable initializedKnownRootChargeAfterTable
  apply tsum_congr
  intro result
  cases result with
  | none => rfl
  | some result =>
      simp only
      by_cases hresult : some result ∈ support
          (runResolvedFromTable (ensuredInitialContext targets) fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))
      · have hmat := rootMaterializationPreserving_maskedPublishedTreeRoot (ensuredInitialContext targets) fuel table emptySplitHashCache result
          (layerRootsMaterialized_ensuredInitialContext targets) (ensuredInitialContext_computed targets) hresult
        have hclosed := (ensuredInitialContext_computed targets).of_mem_runResolved _ _ fuel table result hresult
        rw [expectedLiveMaterializedRootCharge_eq_known parameter result.value.1 ftsSecret _ _ _ _ _ hmat hclosed]
      · rw [probOutput_eq_zero_of_not_mem_support hresult]
        simp

end SphincsSecurity.Concrete.OtsProbeSimulation
