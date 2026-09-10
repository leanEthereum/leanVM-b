import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeChronologicalTerminal
import SphincsSecurity.Proof.OtsProbeEnsuredInitialization
import SphincsSecurity.Proof.OtsProbeLiveGameCharge
import SphincsSecurity.Proof.OtsProbeLiveResolvedBudget

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem expandedQuery_hashBudget
    (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (q : Nat) (hbound : (simulateQ (expandedAdversaryImpl secretKey) (OracleSpec.query input >>= next)).IsQueryBoundP
      (· matches Sum.inr _) q) :
    outerHashQueryCount input ≤ q ∧ ∀ reply ∈ support (expandedAdversaryImpl secretKey input),
      (simulateQ (expandedAdversaryImpl secretKey) (next reply)).IsQueryBoundP (· matches Sum.inr _)
        (q - outerHashQueryCount input) := by
  cases input with
  | inl input =>
      rw [simulateQ_expandedAdversaryImpl_query_bind_inl, OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | inl n => exact ⟨Nat.zero_le _, fun reply _ => hbound.2 reply⟩
      | inr input =>
          exact ⟨hbound.1.resolve_left (by simp), fun reply _ => hbound.2 reply⟩
  | inr message =>
      rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
      exact ⟨Nat.zero_le _, fun reply hreply => isQueryBoundP_of_bind hbound reply hreply⟩

theorem liveResolvedProbeBound_nativeExpanded_of_gameBudget
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl
      (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey))
      computation).IsQueryBoundP (· matches Sum.inr _) q)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) :
    LiveResolvedQueryBound LazyRevealProbe.IsProbe
      ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache)
      q context fuel table := by
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  induction computation using OracleComp.inductionOn generalizing q context fuel cache actualCache with
  | pure value => trivial
  | query_bind input next ih =>
      have hbudget := expandedQuery_hashBudget secretKey input next q hbound
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have hnext : ∀ result, some result ∈ support (runResolvedFromTable context fuel table
          ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)) →
          LiveResolvedQueryBound LazyRevealProbe.IsProbe
            ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) (next result.value.1)).run result.value.2)
            (q - outerHashQueryCount input) result.context result.remaining result.table := by
        intro result hresult
        obtain ⟨actual, hactual, hrel⟩ := exists_right_of_relTriple_of_mem_support
          (reachableResolvedCouples_maskedChronologicalExpandedAdversaryImpl parameter root table ftsSecret input
            context fuel cache actualCache hinvariant hvisible hpublished) hresult
        rcases hrel with hclean | hdoomed
        · rw [hclean.1]
          have hreply := unloggedMappedAdversaryImpl_output_mem_support_expanded secretKey input actualCache actual.2 actual.1 hactual
          apply ih result.value.1 (q - outerHashQueryCount input) _ result.context result.remaining result.value.2 actual.2
            hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2
          rw [hclean.2.1]
          exact hbudget.2 actual.1 hreply
        · apply liveResolvedQueryBound_of_not_completable
          rw [hdoomed.1]
          exact hdoomed.2.2.2
      have hcombined := liveResolvedQueryBound_bind_of_syntactic_prefix LazyRevealProbe.IsProbe
        ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
        (fun result => (simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) (next result.1)).run result.2)
        (outerHashQueryCount input) (q - outerHashQueryCount input)
        (maskedChronologicalExpandedAdversaryImpl_probeBound parameter root ftsSecret input cache) context fuel table hnext
      simpa only [Nat.add_sub_of_le hbudget.1] using hcombined

theorem liveResolvedProbeBound_nativeRetained_of_gameBudget
    (targets : Finset Position) (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat) :
    LiveResolvedQueryBound LazyRevealProbe.IsProbe (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
      q (ensuredInitialContext targets) fuel table := by
  unfold nativeChronologicalRetainedComputation
  simpa only [Nat.zero_add] using
    (liveResolvedQueryBound_bind_of_syntactic_prefix LazyRevealProbe.IsProbe
      (maskedPublishedTreeRoot.run emptySplitHashCache) _ 0 q (maskedPublishedTreeRoot_probeFree emptySplitHashCache)
      (ensuredInitialContext targets) fuel table (by
        intro result hresult
        obtain ⟨actual, _, hrel⟩ := exists_right_of_relTriple_of_mem_support
          (reachableResolvedCouples_maskedPublishedTreeRoot parameter table (ensuredInitialContext targets)
            fuel emptySplitHashCache ∅ (ensuredInitialContext_resolvedInvariant targets parameter table)
            (ensuredInitialContext_visible targets parameter table) (ensuredInitialContext_published targets)) hresult
        rcases hrel with hclean | hdoomed
        · rw [hclean.1]
          exact liveResolvedProbeBound_nativeExpanded_of_gameBudget parameter result.value.1 table ftsSecret
            (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩) q
            (isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hparameter table ftsSecret hfts result.value.1)
            result.context result.remaining result.value.2 actual.2 hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2
        · apply liveResolvedQueryBound_of_not_completable
          rw [hdoomed.1]
          exact hdoomed.2.2.2))

end SphincsSecurity.Concrete.OtsProbeSimulation
