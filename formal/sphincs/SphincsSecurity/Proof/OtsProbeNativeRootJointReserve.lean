import SphincsSecurity.Proof.OtsProbeNativeStoredRootStructuralCharge
import SphincsSecurity.Proof.OtsProbeLiveKnownRootCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

theorem chronological_liveProbe_add_knownStructural_mul_le_directCharge
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) :
    (expectedLiveResolvedQueryCharge nativeProbeQueryCharge
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) context fuel table +
      expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (knownStructuralRootOuterCharge parameter) computation context fuel table cache) * (4 / 3 : ENNReal) ≤
      expectedQueryCharge (directOtsQueryCharge parameter)
        (simulateQ (expandedAdversaryImpl
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey))
          computation) actualCache := by
  exact (mul_le_mul'
    (chronological_liveProbe_add_knownStructural_le_liveOuterCharge parameter root ftsSecret computation context fuel table cache
      hinvariant.2.1.valuesConsistent hinvariant.2.2.1) le_rfl).trans
    (expectedLiveChronologicalOtsCount_mul_le_directCharge parameter root table ftsSecret computation context fuel cache actualCache
      hinvariant hvisible hpublished)

theorem chronological_liveProbe_add_knownRoots_le_refinedReserve
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    (expectedLiveResolvedQueryCharge nativeProbeQueryCharge
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) context fuel table +
      expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (knownStructuralRootOuterCharge parameter) computation context fuel table cache) * (4 / 3 : ENNReal) +
      expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (knownEncodingRootOuterCharge parameter) computation context fuel table cache ≤
      expectedQueryCharge (otsOpeningRefinedQueryReserve secretKey)
        (simulateQ (expandedAdversaryImpl secretKey) computation) actualCache := by
  dsimp only
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  apply (add_le_add
    (chronological_liveProbe_add_knownStructural_mul_le_directCharge parameter root table ftsSecret
      computation context fuel cache actualCache hinvariant hvisible hpublished)
    (expectedLiveKnownRootCharge_le_actualRootCharge parameter root table ftsSecret computation context fuel cache actualCache
      hinvariant hvisible hpublished hcomputed)).trans
  rw [← expectedQueryCharge_add]
  exact expectedQueryCharge_mono _ _ (direct_add_rootEncodingQueryCharge_le_refinedReserve secretKey) _ actualCache

end SphincsSecurity.Concrete.OtsProbeSimulation
