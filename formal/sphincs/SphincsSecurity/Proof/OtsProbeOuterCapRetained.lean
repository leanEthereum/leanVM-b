import SphincsSecurity.Proof.OtsProbeLiveValueMap

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def outerCappedRetainedComputation
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) :
    OracleComp (LazyRevealProbe.World Coordinate) (Option (RetainedGameResult × SplitHashCache)) := do
  let root ← maskedPublishedTreeRoot.run emptySplitHashCache
  let result ← (simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root.1 ftsSecret)
    (capOuterHashQueries (retainedGameRestComputation adversary ⟨root.1, parameter⟩) q)).run root.2
  pure (result.1.map (fun rest => ((root.1, rest), result.2)))

theorem evalDist_outerCappedRetained_live
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat) :
    evalDist (runResolvedLiveValue table (ensuredInitialContext ∅) fuel
      (outerCappedRetainedComputation adversary parameter ftsSecret q)) =
      evalDist (someLiveValue <$> runResolvedLiveValue table (ensuredInitialContext ∅) fuel
        ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run emptySplitHashCache)) := by
  rw [outerCappedRetainedComputation, maskedChronologicalRetainedGame_eq_root_rest]
  rw [evalDist_runResolvedLiveValue_bind table (ensuredInitialContext ∅) fuel _ _
    (ensuredInitialContext_valid ∅).valuesConsistent
    (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable ∅ table))]
  have hm := evalDist_map_eq_of_evalDist_eq
    (evalDist_runResolvedLiveValue_bind table (ensuredInitialContext ∅) fuel
      (maskedPublishedTreeRoot.run emptySplitHashCache)
      (fun root => do
        let rest ← (simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root.1 ftsSecret)
          (retainedGameRestComputation adversary ⟨root.1, parameter⟩)).run root.2
        pure ((root.1, rest.1), rest.2))
      (ensuredInitialContext_valid ∅).valuesConsistent
      (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable ∅ table))) someLiveValue
  rw [hm, map_bind]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      have hcore := resolvedCore_of_mem_runResolvedFromTable (maskedPublishedTreeRoot.run emptySplitHashCache)
        (ensuredInitialContext ∅) fuel table result (ensuredInitialContext_valid ∅).valuesConsistent
        (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable ∅ table)) hresult
      obtain ⟨actual, _, hrelation⟩ := exists_right_of_relTriple_of_mem_support
        (reachableResolvedCouples_maskedPublishedTreeRoot parameter table (ensuredInitialContext ∅)
          fuel emptySplitHashCache ∅ (ensuredInitialContext_resolvedInvariant ∅ parameter table)
          (ensuredInitialContext_visible ∅ parameter table) (ensuredInitialContext_published ∅)) hresult
      dsimp only
      rcases hrelation with hclean | hdoomed
      · rw [hclean.1]
        simp only [bind_pure_comp, runResolvedLiveValue_map, Functor.map_map]
        have hcap := evalDist_native_outerCap_live parameter result.value.1 table ftsSecret
          (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩) q
          (isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hparameter table ftsSecret hfts result.value.1)
          result.context result.remaining result.value.2 actual.2 hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2
        have hm := evalDist_map_eq_of_evalDist_eq hcap
          (Option.map (fun entry => (entry.1, entry.2.1.map (fun rest => ((result.value.1, rest), entry.2.2)))))
        simp only [Functor.map_map] at hm
        simpa only [liftOuterCapResult, someLiveValue, Option.map_map, Option.map_some, Function.comp_def] using hm
      · have hnot : ¬DeferredCompletable result.table result.context := by
          rw [hdoomed.1]
          exact hdoomed.2.2.2
        rw [evalDist_runResolvedLiveValue_eq_none_of_not_completable result.table result.context result.remaining _
          hcore.2.1 (by rw [hcore.1]; exact hcore.2.2) hnot]
        have hm := evalDist_map_eq_of_evalDist_eq
          (evalDist_runResolvedLiveValue_eq_none_of_not_completable result.table result.context result.remaining
            (do
              let rest ← (simulateQ (maskedChronologicalExpandedAdversaryImpl parameter result.value.1 ftsSecret)
                (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)).run result.value.2
              pure ((result.value.1, rest.1), rest.2))
            hcore.2.1 (by rw [hcore.1]; exact hcore.2.2) hnot) someLiveValue
        rw [hm]
        rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
