import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeChainBound
import SphincsSecurity.Proof.OtsProbeNativeQueryTraceCoupling
import SphincsSecurity.Proof.OtsProbeNativeQueryTraceSelection
import SphincsSecurity.Proof.OtsProbePrivateInactive

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem canonicalTraceHashCount_eq_nativeHashLength (history : List CanonicalQuerySelection) :
    canonicalTraceHashCount history = (nativeHashQueryHistory history).length := by
  induction history with
  | nil => rfl
  | cons head tail ih =>
      simp only [canonicalTraceHashCount, List.map_cons, List.sum_cons] at ih ⊢
      cases hinput : head.input with
      | inl input =>
          cases input <;> simp [nativeHashQueryHistory, hinput, IsOuterHash, outerHashQueryCount] at ih ⊢ <;> omega
      | inr message => simpa [nativeHashQueryHistory, hinput, IsOuterHash, outerHashQueryCount] using ih

theorem nativeTrace_hashCount_le_of_expanded
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel q : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context)
    (hbound : (simulateQ (expandedAdversaryImpl
      (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey))
      computation).IsQueryBoundP (· matches Sum.inr _) q)
    (trace : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (htrace : trace ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    canonicalTraceHashCount trace.2 ≤ q := by
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  let state : ViewedFullTraceState × Bool := (⟨actualCache, ⟨[], [], []⟩, [], none⟩, false)
  obtain ⟨actual, hactual, hrel⟩ := exists_right_of_relTriple_of_mem_support
    (relTriple_nativeQueryTrace_prehitQueryTrace parameter root table ftsSecret secretKey computation context fuel cache state
      hinvariant hvisible hpublished hcomputed) htrace
  exact hrel.hashCount_le.trans (prehitTraceHashCount_le_of_expanded secretKey secretKey computation q hbound state actual hactual)

theorem nativeChainTraceAfterRoot_hashCount_le_of_expanded
    (targets : Finset Position) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α)
    (hbound : ∀ root, (simulateQ (expandedAdversaryImpl
      (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey))
      (continuation root)).IsQueryBoundP (· matches Sum.inr _) q)
    (trace : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (htrace : trace ∈ support (nativeChainTraceAfterRoot targets parameter table ftsSecret fuel continuation)) :
    canonicalTraceHashCount trace.2 ≤ q := by
  rw [nativeChainTraceAfterRoot, mem_support_bind_iff] at htrace
  obtain ⟨root, hroot, htrace⟩ := htrace
  cases root with
  | none =>
      simp only [mem_support_pure_iff] at htrace
      subst trace
      simp [canonicalTraceHashCount]
  | some root =>
      have hrel := reachableResolvedCouples_maskedPublishedTreeRoot parameter table (ensuredInitialContext targets)
        fuel emptySplitHashCache ∅ (ensuredInitialContext_resolvedInvariant targets parameter table)
        (ensuredInitialContext_visible targets parameter table) (ensuredInitialContext_published targets)
      obtain ⟨actual, _, hrel⟩ := exists_right_of_relTriple_of_mem_support hrel hroot
      rcases hrel with hclean | hdoomed
      · dsimp only at htrace
        rw [hclean.1] at htrace
        exact nativeTrace_hashCount_le_of_expanded parameter root.value.1 table ftsSecret (continuation root.value.1)
          root.context root.remaining q root.value.2 actual.2 hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2
          ((ensuredInitialContext_computed targets).of_mem_runResolved _ _ fuel table root hroot)
          (hbound root.value.1) trace htrace
      · dsimp only at htrace
        rw [runNativeQueryTrace_of_not_completable parameter root.value.1 ftsSecret (continuation root.value.1)
          root.context root.remaining root.table root.value.2 (by rw [hdoomed.1]; exact hdoomed.2.2.2)] at htrace
        simp only [mem_support_pure_iff] at htrace
        subst trace
        simp [canonicalTraceHashCount]

theorem nativeRetainedTraceAfterRoot_hashCount_le
    (targets : Finset Position) (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat)
    (trace : Option (ResolvedRunResult (RetainedRestResult × SplitHashCache)) × List CanonicalQuerySelection)
    (htrace : trace ∈ support (nativeChainTraceAfterRoot targets parameter table ftsSecret fuel
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩))) :
    canonicalTraceHashCount trace.2 ≤ q := by
  apply nativeChainTraceAfterRoot_hashCount_le_of_expanded targets parameter table ftsSecret fuel q _ _ trace htrace
  intro root
  exact isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hparameter table ftsSecret hfts root

end SphincsSecurity.Concrete.OtsProbeSimulation
