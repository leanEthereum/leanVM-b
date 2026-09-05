import SphincsSecurity.Proof.OtsProbeNativeQueryTraceCoupling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

theorem probEvent_nativeUnknownSourceRootMatch_le_prehit
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (state : ViewedFullTraceState × Bool)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) state.1.cache)
    (hvisible : VisibleResolvedComputationsCached parameter table context state.1.cache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    Pr[fun result => UnknownSourceStoredRootMatch parameter result.2 ∨ UnknownSourceFinalRootMatch parameter result |
      runNativeQueryTrace parameter root ftsSecret computation context fuel table cache] ≤
      Pr[fun result => result.2.2 = true |
        (simulateQ (encodingPrehitViewedAdversaryImpl secretKey secretKey) computation).run state] := by
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  dsimp only
  exact probEvent_unknownSourceRootMatch_le_prehit_of_trace_coupling secretKey secretKey table _ computation state rfl
    (relTriple_nativeQueryTrace_prehitQueryTrace parameter root table ftsSecret secretKey computation context fuel cache state
      hinvariant hvisible hpublished hcomputed)

end SphincsSecurity.Concrete.OtsProbeSimulation
