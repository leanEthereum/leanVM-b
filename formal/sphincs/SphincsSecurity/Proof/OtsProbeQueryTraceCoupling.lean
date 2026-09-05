import SphincsSecurity.Proof.OtsProbeCanonicalQueryTrace
import SphincsSecurity.Proof.OtsProbePrehitQueryTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option maxRecDepth 100000 in
theorem relTriple_canonicalChronologicalQuery_prehit
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (accountingKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (state : ViewedFullTraceState × Bool)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) state.1.cache)
    (hvisible : VisibleResolvedComputationsCached parameter table context state.1.cache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    RelTriple (canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache)
      ((encodingPrehitViewedAdversaryImpl accountingKey secretKey input).run state)
      (fun left right => ReachableResolvedRunRel parameter table left (right.1, right.2.1.cache) ∧
        ∀ result, left = some result → DeferredComputationsClosed result.context) := by
  classical
  dsimp only
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  have hstep := canonicalReachableResolvedImplCouples_chronologicalAdversaryImpl parameter root table ftsSecret
    input context fuel cache state.1.cache hinvariant hvisible hpublished
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hstep
    (fun left => ∀ result, left = some result → DeferredComputationsClosed result.context) (by
      intro left hleft result heq
      subst left
      exact hcomputed.of_mem_canonicalChronologicalQuery parameter root table ftsSecret input context fuel cache
        result hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hleft)
  have hprojection := encodingPrehitViewedAdversaryImpl_cache_projection accountingKey secretKey
    ((OracleWorld + SigningSpec).query input) state
  simp only [simulateQ_spec_query] at hprojection
  have hmonitor := relTriple_of_evalDist_map_eq_general
    ((unloggedMappedAdversaryImpl secretKey input).run state.1.cache)
    ((encodingPrehitViewedAdversaryImpl accountingKey secretKey input).run state)
    id (fun result => (result.1, result.2.1.cache)) (by
      simpa only [id_map] using congrArg evalDist hprojection.symm)
  apply relTriple_post_mono (relTriple_trans_exists hsupported hmonitor)
  rintro left right ⟨actual, hrelation, heq⟩
  exact ⟨heq ▸ hrelation.1, hrelation.2⟩

def CanonicalQueryTraceRel (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (left : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) : Prop :=
  (match left.1 with
    | none => True
    | some result => result.table = table ∧ result.value.1 = right.1.1 ∧
        ResolvedContextInvariant parameter table result.context (ordinaryQueryCache result.value.2) right.1.2.1.cache ∧
        VisibleResolvedComputationsCached parameter table result.context right.1.2.1.cache ∧
        PublishedValues result.context.state ∧ DeferredComputationsClosed result.context) ∧
    List.Forall₂ (fun a b => CanonicalQuerySelectionRel parameter table (some a) (some b.actual))
      left.2 (right.2.take left.2.length)

theorem CanonicalQueryTraceRel.prepend
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection}
    {right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot}
    (hrelation : CanonicalQueryTraceRel parameter table left right)
    (a : CanonicalQuerySelection) (b : PrehitQuerySnapshot)
    (hhead : CanonicalQuerySelectionRel parameter table (some a) (some b.actual)) :
    CanonicalQueryTraceRel parameter table (left.1, a :: left.2) (right.1, b :: right.2) := by
  refine ⟨hrelation.1, ?_⟩
  simpa only [List.length_cons, List.take_succ_cons] using List.Forall₂.cons
    (R := fun (a : CanonicalQuerySelection) (b : PrehitQuerySnapshot) =>
      CanonicalQuerySelectionRel parameter table (some a) (some b.actual)) hhead hrelation.2

theorem relTriple_empty_canonicalTrace_any
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (right : ProbComp ((α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)) :
    RelTriple (pure (none, []) : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection))
      right (CanonicalQueryTraceRel parameter table) := by
  have hbase := relTriple_true
    (pure (none, []) : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)) right
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hbase
    (fun result => result = (none, [])) (by intro result hresult; simpa using hresult)
  apply relTriple_post_mono hsupported
  intro left right hrelation
  rw [hrelation.2]
  exact ⟨trivial, List.Forall₂.nil⟩

set_option maxRecDepth 100000 in
theorem relTriple_canonicalQueryTrace_prehitQueryTrace
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (accountingKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (state : ViewedFullTraceState × Bool)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) state.1.cache)
    (hvisible : VisibleResolvedComputationsCached parameter table context state.1.cache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    RelTriple (runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache)
      (runPrehitQueryTrace accountingKey secretKey computation state) (CanonicalQueryTraceRel parameter table) := by
  dsimp only
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  induction computation using OracleComp.inductionOn generalizing context fuel cache state with
  | pure value =>
      rw [runCanonicalQueryTrace, OracleComp.construct_pure, if_pos hinvariant.2.2.2.1]
      exact relTriple_pure_pure ⟨⟨rfl, rfl, hinvariant, hvisible, hpublished, hcomputed⟩, List.Forall₂.nil⟩
  | query_bind input next ih =>
      rw [runCanonicalQueryTrace_query_bind, if_pos hinvariant.2.2.2.1, runPrehitQueryTrace_query_bind]
      apply relTriple_bind (relTriple_canonicalChronologicalQuery_prehit parameter root table ftsSecret accountingKey
        input context fuel cache state hinvariant hvisible hpublished hcomputed)
      intro left right hrelation
      have htail : RelTriple
          (match left with
            | none => pure (none, [])
            | some result => runCanonicalQueryTrace parameter root ftsSecret (next result.value.1)
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
            · rw [runCanonicalQueryTrace_of_not_completable parameter root ftsSecret
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
