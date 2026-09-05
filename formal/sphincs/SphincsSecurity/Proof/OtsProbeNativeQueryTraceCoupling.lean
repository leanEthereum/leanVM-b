import SphincsSecurity.Proof.OtsProbeNativeQueryTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem relTriple_nativeChronologicalQuery_prehit
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (accountingKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (state : ViewedFullTraceState × Bool)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) state.1.cache)
    (hvisible : VisibleResolvedComputationsCached parameter table context state.1.cache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    RelTriple (runResolvedFromTable context fuel table
      ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache))
      ((encodingPrehitViewedAdversaryImpl accountingKey secretKey input).run state)
      (fun left right => ReachableResolvedRunRel parameter table left (right.1, right.2.1.cache) ∧
        ∀ result, left = some result → DeferredComputationsClosed result.context) := by
  have h := relTriple_nativeChronological_computed_prehit parameter root table ftsSecret accountingKey
    ((OracleWorld + SigningSpec).query input) context fuel cache state hinvariant hvisible hpublished hcomputed
  simpa only [simulateQ_spec_query] using
    relTriple_post_mono h (fun _ _ hrel => ⟨hrel.1, hrel.2.1⟩)

set_option maxRecDepth 100000 in
theorem relTriple_nativeQueryTrace_prehitQueryTrace
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (accountingKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (state : ViewedFullTraceState × Bool)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) state.1.cache)
    (hvisible : VisibleResolvedComputationsCached parameter table context state.1.cache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    RelTriple (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)
      (runPrehitQueryTrace accountingKey secretKey computation state) (CanonicalQueryTraceRel parameter table) := by
  dsimp only
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  induction computation using OracleComp.inductionOn generalizing context fuel cache state with
  | pure value =>
      rw [runNativeQueryTrace, OracleComp.construct_pure, if_pos hinvariant.2.2.2.1]
      exact relTriple_pure_pure ⟨⟨rfl, rfl, hinvariant, hvisible, hpublished, hcomputed⟩, List.Forall₂.nil⟩
  | query_bind input next ih =>
      rw [runNativeQueryTrace_query_bind, if_pos hinvariant.2.2.2.1, runPrehitQueryTrace_query_bind]
      apply relTriple_bind (relTriple_nativeChronologicalQuery_prehit parameter root table ftsSecret accountingKey
        input context fuel cache state hinvariant hvisible hpublished hcomputed)
      intro left right hrelation
      have htail : RelTriple
          (match left with
            | none => pure (none, [])
            | some result => runNativeQueryTrace parameter root ftsSecret (next result.value.1)
                result.context result.remaining result.table result.value.2)
          (runPrehitQueryTrace accountingKey secretKey (next right.1) right.2)
          (CanonicalQueryTraceRel parameter table) := by
        cases left with
        | none => exact relTriple_empty_canonicalTrace_any parameter table _
        | some result =>
            dsimp only
            rcases hrelation.1 with hclean | hdoomed
            · rw [hclean.1, ← hclean.2.1]
              exact ih result.value.1 result.context result.remaining result.value.2 right.2
                hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2 (hrelation.2 result rfl)
            · rw [runNativeQueryTrace_of_not_completable parameter root ftsSecret
                (next result.value.1) result.context result.remaining result.table result.value.2 (by
                  rw [hdoomed.1]
                  exact hdoomed.2.2.2)]
              exact relTriple_empty_canonicalTrace_any parameter table _
      have hmap := relTriple_map
        (f := fun tail : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection =>
          (tail.1, (⟨input, context, fuel, table, cache⟩ : CanonicalQuerySelection) :: tail.2))
        (g := fun tail : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot =>
          (tail.1, (⟨input, state⟩ : PrehitQuerySnapshot) :: tail.2))
        (relTriple_post_mono htail (fun leftTail rightTail htailRelation =>
          htailRelation.prepend ⟨input, context, fuel, table, cache⟩ ⟨input, state⟩
            ⟨rfl, rfl, hinvariant, hvisible, hpublished, hcomputed⟩))
      cases left <;> simpa only [map_eq_bind_pure_comp, Function.comp_def] using hmap

end SphincsSecurity.Concrete.OtsProbeSimulation
