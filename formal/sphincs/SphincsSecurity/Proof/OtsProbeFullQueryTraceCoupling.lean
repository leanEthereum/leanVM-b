import SphincsSecurity.Proof.OtsProbeNativeQueryTraceCoupling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

def FullCanonicalQueryTraceRel (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (left : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) : Prop :=
  CanonicalQueryTraceRel parameter table left right ∧
    (left.1 ≠ none → List.Forall₂ (fun a b =>
      CanonicalQuerySelectionRel parameter table (some a) (some b.actual)) left.2 right.2)

theorem FullCanonicalQueryTraceRel.prepend
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection}
    {right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot}
    (h : FullCanonicalQueryTraceRel parameter table left right)
    (a : CanonicalQuerySelection) (b : PrehitQuerySnapshot)
    (hhead : CanonicalQuerySelectionRel parameter table (some a) (some b.actual)) :
    FullCanonicalQueryTraceRel parameter table (left.1, a :: left.2) (right.1, b :: right.2) :=
  ⟨h.1.prepend a b hhead, fun hsome => List.Forall₂.cons hhead (h.2 hsome)⟩

theorem relTriple_empty_fullCanonicalTrace_any
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (right : ProbComp ((α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)) :
    RelTriple (pure (none, []) : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection))
      right (FullCanonicalQueryTraceRel parameter table) := by
  have hbase := relTriple_empty_canonicalTrace_any parameter table right
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hbase
    (fun result => result.1 = none) (by
      intro result hresult
      simpa only [support_pure, Set.mem_singleton_iff] using congrArg Prod.fst
        (show result = (none, []) by simpa using hresult))
  exact relTriple_post_mono hsupported (fun left right hrel =>
    ⟨hrel.1, fun hsome => False.elim (hsome hrel.2)⟩)

set_option maxRecDepth 100000 in
theorem relTriple_nativeQueryTrace_full_prehitQueryTrace
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
      (runPrehitQueryTrace accountingKey secretKey computation state) (FullCanonicalQueryTraceRel parameter table) := by
  dsimp only
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  induction computation using OracleComp.inductionOn generalizing context fuel cache state with
  | pure value =>
      rw [runNativeQueryTrace, OracleComp.construct_pure, if_pos hinvariant.2.2.2.1]
      exact relTriple_pure_pure ⟨⟨⟨rfl, rfl, hinvariant, hvisible, hpublished, hcomputed⟩, List.Forall₂.nil⟩, fun _ => .nil⟩
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
          (FullCanonicalQueryTraceRel parameter table) := by
        cases left with
        | none => exact relTriple_empty_fullCanonicalTrace_any parameter table _
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
              exact relTriple_empty_fullCanonicalTrace_any parameter table _
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
