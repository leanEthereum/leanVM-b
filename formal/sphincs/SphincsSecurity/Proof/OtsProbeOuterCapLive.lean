import SphincsSecurity.Proof.OuterHashQueryCapBudget
import SphincsSecurity.Proof.OtsProbePrivateValueErasedComparison

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def liftOuterCapResult : Option (Nat × (α × SplitHashCache)) → Option (Nat × (Option α × SplitHashCache)) :=
  Option.map (fun result => (result.1, (some result.2.1, result.2.2)))

theorem evalDist_native_outerCap_live
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
    evalDist (runResolvedLiveValue table context fuel
      ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (capOuterHashQueries computation q)).run cache)) =
      evalDist (liftOuterCapResult <$> runResolvedLiveValue table context fuel
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache)) := by
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  induction computation using OracleComp.inductionOn generalizing q context fuel cache actualCache with
  | pure value =>
      simp [capOuterHashQueries, outerHashQueryCutAt, OuterQueryCut.value?, runResolvedLiveValue,
        runResolvedFromTable, liftOuterCapResult, hinvariant.2.2.2.1]
  | query_bind input next ih =>
      have hbudget := expandedQuery_hashBudget secretKey input next q hbound
      rw [capOuterHashQueries_query_bind_of_budget input next q hbudget.1,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [evalDist_runResolvedLiveValue_bind table context fuel _ _ hinvariant.2.1.valuesConsistent hinvariant.2.2.1]
      have hm := evalDist_map_eq_of_evalDist_eq
        (evalDist_runResolvedLiveValue_bind table context fuel
          ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
          (fun result => (simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) (next result.1)).run result.2)
          hinvariant.2.1.valuesConsistent hinvariant.2.2.1) liftOuterCapResult
      rw [hm, map_bind]
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => rfl
      | some result =>
          have hcore := resolvedCore_of_mem_runResolvedFromTable
            ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
            context fuel table result hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hresult
          obtain ⟨actual, hactual, hrelation⟩ := exists_right_of_relTriple_of_mem_support
            (reachableResolvedCouples_maskedChronologicalExpandedAdversaryImpl parameter root table ftsSecret input
              context fuel cache actualCache hinvariant hvisible hpublished) hresult
          dsimp only
          rcases hrelation with hclean | hdoomed
          · rw [hclean.1]
            have hreply := unloggedMappedAdversaryImpl_output_mem_support_expanded secretKey input actualCache actual.2 actual.1 hactual
            apply ih result.value.1 (q - outerHashQueryCount input) _ result.context result.remaining result.value.2 actual.2
              hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2
            rw [hclean.2.1]
            exact hbudget.2 actual.1 hreply
          · have hnot : ¬DeferredCompletable result.table result.context := by
              rw [hdoomed.1]
              exact hdoomed.2.2.2
            have hleft := evalDist_runResolvedLiveValue_eq_none_of_not_completable result.table result.context result.remaining
              ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
                (capOuterHashQueries (next result.value.1) (q - outerHashQueryCount input))).run result.value.2)
              hcore.2.1 (by rw [hcore.1]; exact hcore.2.2) hnot
            have hright := evalDist_map_eq_of_evalDist_eq
              (evalDist_runResolvedLiveValue_eq_none_of_not_completable result.table result.context result.remaining
                ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) (next result.value.1)).run result.value.2)
                hcore.2.1 (by rw [hcore.1]; exact hcore.2.2) hnot) liftOuterCapResult
            rw [hleft, hright]
            rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
