import SphincsSecurity.Proof.OtsProbeResolvedBoundaryOrdinarySigner
import SphincsSecurity.Proof.QueryBound

/-!
# Adaptive ordinary boundary refinement

This file lifts the one-query ordinary refinement through the complete adaptive computation and its
terminal verifier.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem FinalizationContextLE.canonicalize_left
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right) :
    FinalizationContextLE table (canonicalizeMaterializedValues table left) right where
  view := (FinalizationViewLE.of_eq
    (finalizationViewEq_canonicalize_left table left hcontext.leftValid
      hcontext.view.leftStarts hcontext.view.leftClean)).trans hcontext.view
  leftValid := canonicalizeMaterializedValues_valid table left hcontext.leftValid
    hcontext.view.leftClean
  rightValid := hcontext.rightValid
  rightCompletable := hcontext.rightCompletable

theorem valuesLE_canonicalizeMaterializedValues_left
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state) :
    LazyRevealProbe.ValuesLE
      (canonicalizeMaterializedValues table context).state context.state := by
  intro coordinate output hvalue
  unfold canonicalizeMaterializedValues publicMaterializedValues at hvalue
  by_cases hrevealed : coordinate ∈ context.state.revealed
  · simp only [hrevealed, ↓reduceIte] at hvalue
    have hknown := hpublished coordinate hrevealed
    cases horiginal : context.state.values coordinate with
    | none => exact False.elim (hknown horiginal)
    | some original =>
        have hresolved : resolvedCompletionValue table context coordinate = some original := by
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              have heq := hstarts ⟨lay, tree, leafIdx, chainIdx⟩ original horiginal
              simp [resolvedCompletionValue, heq]
          | position position =>
              simp [resolvedCompletionValue, DeferredContext.positionValue, horiginal]
        rw [hresolved] at hvalue
        have heq : original = output := Option.some.inj hvalue
        rwa [heq] at horiginal
  · simp [hrevealed] at hvalue

theorem OrdinaryMaterializedRunEq.canonicalize_left
    {table : OtsSecretIndex → HashOutput}
    {left right : ResolvedRunResult (α × SplitHashCache)}
    (hrelation : OrdinaryMaterializedRunEq table left right) :
    OrdinaryMaterializedRunEq table
      { left with
        context := canonicalizeMaterializedValues table left.context }
      right where
  value_eq := hrelation.value_eq
  context_le := hrelation.context_le.canonicalize_left
  remaining_le := hrelation.remaining_le
  left_table := hrelation.left_table
  right_table := hrelation.right_table
  cache_eq := hrelation.cache_eq
  revealed_eq := by
    rw [canonicalizeMaterializedValues_revealed]
    exact hrelation.revealed_eq
  values_le := (valuesLE_canonicalizeMaterializedValues_left table left.context
    hrelation.context_le.view.leftStarts hrelation.left_published).trans hrelation.values_le
  left_published := hrelation.left_published.to_canonicalizedMaterializedValues
  right_materialized := hrelation.right_materialized

theorem PrivateStructuralHit.canonicalizeMaterializedValues
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hprivate : PrivateStructuralHit context)
    (hpublished : PublishedValues context.state) :
    PrivateStructuralHit (canonicalizeMaterializedValues table context) := by
  rcases hprivate with ⟨position, output, hhidden, hvalue, hhit⟩
  have hnotRevealed : Coordinate.position position ∉ context.state.revealed := by
    intro hrevealed
    exact (hpublished (.position position) hrevealed) hhidden
  refine ⟨position, output, ?_, hvalue, ?_⟩
  · change publicMaterializedValues table context (.position position) = none
    simp [publicMaterializedValues, hnotRevealed]
  · change truncateHash output ∈ context.state.pendingAt (.position position)
    exact hhit

theorem publishedValues_of_done_runDirectResolvedDetailedFromTable
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hpreserves : PreservesPublishedValues computation)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache))
    (hpublished : PublishedValues context.state)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table (computation.run cache))) :
    PublishedValues result.context.state := by
  apply hpreserves context.state cache fuel result.context.state result.remaining
    result.value.1 result.value.2 hpublished
  apply raw_done_of_mem_runDirectResolvedFromTable
    (computation.run cache) context fuel table result
  exact mem_support_runDirectResolvedFromTable_of_done_detailed
    (computation.run cache) context fuel table result hresult

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_probingRomImpl
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (query : OracleWorld.Domain)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hpositive : 0 < leftFuel) (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        (((probingRomImpl parameter) query).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        (((probingRomImpl parameter) query).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  cases query with
  | inl n =>
      change RelTriple
        (runDirectResolvedDetailedFromTable left leftFuel table
          ((splitUniformImpl n).run leftCache))
        (runDirectResolvedDetailedFromTable right rightFuel table
          ((splitUniformImpl n).run rightCache))
        (DirectDetailedOrdinaryRunEq table)
      unfold splitUniformImpl
      rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.uniformQuery,
        runDirectResolvedDetailedFromTable_uniform_query_bind,
        runDirectResolvedDetailedFromTable_uniform_query_bind]
      apply relTriple_bind (relTriple_refl
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact relTriple_runDirectResolvedDetailed_pure_of_ordinaryMaterialized table leftOutput
        left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
          hvalues hpublished hrightMaterialized
  | inr input =>
      exact relTriple_runDirectResolvedDetailed_probingHashQuery parameter table input
        left right leftFuel rightFuel leftCache rightCache hcontext hpositive hfuel hcache
          hrevealed hvalues hpublished hrightMaterialized

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedDetailed_maskedExpandedAdversaryImpl
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hpositive : IsOuterHash query → 0 < leftFuel)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run rightCache))
      (DirectDetailedOrdinaryRunEq table) := by
  cases query with
  | inl worldQuery =>
      cases worldQuery with
      | inl n =>
          apply relTriple_stable_to_ordinary
          simpa [maskedExpandedAdversaryImpl, probingRomImpl] using
            ordinaryMaterializedStableCouples_splitUniformImpl table n left right leftFuel
              rightFuel leftCache rightCache hcontext hfuel hcache hrevealed hvalues hpublished
              hrightMaterialized
      | inr input =>
          simpa [maskedExpandedAdversaryImpl] using
            relTriple_runDirectResolvedDetailed_probingRomImpl parameter table (.inr input)
              left right leftFuel rightFuel leftCache rightCache hcontext
              (hpositive (by simp [IsOuterHash])) hfuel hcache hrevealed hvalues hpublished
              hrightMaterialized
  | inr message =>
      apply relTriple_stable_to_ordinary
      simpa [maskedExpandedAdversaryImpl, maskedSigningImpl] using
        ordinaryMaterializedStableCouples_maskedSigningImpl table parameter root ftsSecret
          message left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache
          hrevealed hvalues hpublished hrightMaterialized

set_option maxRecDepth 100000 in
theorem isQueryBoundP_expandedSigningTrace_all_tables_roots
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (root : Digest) :
    (simulateQ
      (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
      (signingTraceComputation
        (adversary.main ⟨root, parameter⟩))).IsQueryBoundP
          (· matches Sum.inr _) q := by
  have hfull := isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter
    hparameter table ftsSecret hfts root
  unfold retainedGameRestComputation at hfull
  rw [simulateQ_bind] at hfull
  exact IsQueryBoundP.of_bind_left hfull

theorem ordinaryMaterializedStableCouples_maskedPublishedTreeRoot
    (table : OtsSecretIndex → HashOutput) :
    OrdinaryMaterializedStableCouples table maskedPublishedTreeRoot := by
  unfold maskedPublishedTreeRoot
  apply (ordinaryMaterializedStableCouples_ensureTreeNode table topLayer rootTree
    (layerHeight topLayer) 0).bind
  intro _
  exact ordinaryMaterializedStableCouples_revealPublishedCoordinate table
    (.position (.node topLayer rootTree
      ⟨layerHeight topLayer - 1, by norm_num [layerHeight, topLayer, maxLayerHeight]⟩ 0))

theorem finalizationContextLE_empty
    (table : OtsSecretIndex → HashOutput) :
    FinalizationContextLE table
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues }
      (directDeferredContext
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)) := by
  have hright : directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) =
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues } := by
    rfl
  rw [hright]
  refine
    { view := FinalizationViewLE.refl table _ DeferredContext.valid_empty
        (startTableAgrees_empty table) ?_
      leftValid := DeferredContext.valid_empty
      rightValid := DeferredContext.valid_empty
      rightCompletable := deferredCompletable_empty table }
  intro coordinate output _hvalue
  simp [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt,
    LazyRevealProbe.State.empty]

def BoolImp (left right : Bool) : Prop := left = true → right = true

theorem relTriple_any_true_of_evalDist_eq_true
    (left right : ProbComp Bool)
    (hright : evalDist right = evalDist (pure true : ProbComp Bool)) :
    RelTriple left right BoolImp := by
  have hbase := relTriple_true left (pure true : ProbComp Bool)
  have hsupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  have himp : RelTriple left (pure true : ProbComp Bool) BoolImp := by
    apply relTriple_post_mono hsupport
    intro leftValue rightValue hrelation _hleft
    simpa using hrelation.2
  exact relTriple_of_evalDist_eq_right hright.symm himp

theorem relTriple_false_any (right : ProbComp Bool) :
    RelTriple (pure false : ProbComp Bool) right BoolImp := by
  have hbase := relTriple_true (pure false : ProbComp Bool) right
  have hsupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun value => value ∈ support (pure false : ProbComp Bool))
      (fun value hvalue => hvalue)
  apply relTriple_post_mono hsupport
  intro leftValue rightValue hrelation hleft
  have hfalse : leftValue = false := by
    simpa using hrelation.2
  rw [hfalse] at hleft
  contradiction

set_option maxRecDepth 100000 in
theorem relTriple_map_isNone_finalizeResolvedCoordinates_of_finalizationViewLE
    (table : OtsSecretIndex → HashOutput) (coordinates : List Coordinate)
    (left right : DeferredContext) (hview : FinalizationViewLE table left right) :
    RelTriple
      (Option.isNone <$> finalizeResolvedCoordinates coordinates left table)
      (Option.isNone <$> finalizeResolvedCoordinates coordinates right table)
      BoolImp := by
  induction coordinates generalizing left right with
  | nil =>
      simp [finalizeResolvedCoordinates, BoolImp]
  | cons coordinate remaining ih =>
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
          have hleftClean : ¬left.state.hitAt index.coordinate (table index) :=
            hview.leftClean index.coordinate (table index) (by
              simp [index, resolvedCompletionValue, OtsSecretIndex.coordinate])
          have hrightClean : ¬right.state.hitAt index.coordinate (table index) :=
            hview.rightClean index.coordinate (table index) (by
              simp [index, resolvedCompletionValue, OtsSecretIndex.coordinate])
          change RelTriple
            (Option.isNone <$>
              finalizeResolvedCoordinates (index.coordinate :: remaining) left table)
            (Option.isNone <$>
              finalizeResolvedCoordinates (index.coordinate :: remaining) right table)
            BoolImp
          rw [finalizeResolvedCoordinates_cons_chainStart_of_clean table index remaining left
              hview.leftStarts hleftClean,
            finalizeResolvedCoordinates_cons_chainStart_of_clean table index remaining right
              hview.rightStarts hrightClean]
          exact ih (left.completeResolved index.coordinate (table index))
            (right.completeResolved index.coordinate (table index))
            (hview.completeStart index)
      | position position =>
          cases hvalue : resolvedCompletionValue table left (.position position) with
          | some output =>
              have hrightValue :
                  resolvedCompletionValue table right (.position position) = some output := by
                rw [← hview.valueEq]
                exact hvalue
              have hleftClean := hview.leftClean (.position position) output hvalue
              have hrightClean := hview.rightClean (.position position) output hrightValue
              rw [finalizeResolvedCoordinates_cons_position_of_known_clean table position
                  remaining left hview.leftConsistent output
                  (by simpa [resolvedCompletionValue] using hvalue) hleftClean,
                finalizeResolvedCoordinates_cons_position_of_known_clean table position
                  remaining right hview.rightConsistent output
                  (by simpa [resolvedCompletionValue] using hrightValue) hrightClean]
              exact ih (left.completeResolved (.position position) output)
                (right.completeResolved (.position position) output)
                (hview.completePosition position output)
          | none =>
              have hrightValue :
                  resolvedCompletionValue table right (.position position) = none := by
                rw [← hview.valueEq]
                exact hvalue
              rw [finalizeResolvedCoordinates_cons_position_of_unknown table position remaining
                  left (by simpa [resolvedCompletionValue] using hvalue),
                finalizeResolvedCoordinates_cons_position_of_unknown table position remaining
                  right (by simpa [resolvedCompletionValue] using hrightValue)]
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
              intro leftOutput rightOutput houtput
              subst rightOutput
              by_cases hleftHit : left.state.hitAt (.position position) leftOutput
              · have hrightHit : right.state.hitAt (.position position) leftOutput := by
                  exact hview.pendingLE (.position position) hvalue hleftHit
                rw [if_pos hleftHit, if_pos hrightHit]
                exact relTriple_pure_pure (fun h => h)
              · by_cases hrightHit : right.state.hitAt (.position position) leftOutput
                · rw [if_neg hleftHit, if_pos hrightHit]
                  exact relTriple_any_true_of_evalDist_eq_true
                    (Option.isNone <$>
                      finalizeResolvedCoordinates remaining
                        (left.completeResolved (.position position) leftOutput) table)
                    (pure true) rfl
                · rw [if_neg hleftHit, if_neg hrightHit]
                  exact ih
                    (left.completeResolved (.position position) leftOutput)
                    (right.completeResolved (.position position) leftOutput)
                    (hview.completePosition position leftOutput)

set_option maxRecDepth 100000 in
theorem relTriple_map_isNone_finalizeResolvedCoordinates_of_finalizationViewLE_covered
    (table : OtsSecretIndex → HashOutput)
    (leftCoordinates rightCoordinates : List Coordinate)
    (left right : DeferredContext) (hview : FinalizationViewLE table left right)
    (hleftNodup : leftCoordinates.Nodup) (hrightNodup : rightCoordinates.Nodup)
    (hleftCovered : PendingCovered leftCoordinates left)
    (hrightCovered : PendingCovered rightCoordinates right) :
    RelTriple
      (Option.isNone <$> finalizeResolvedCoordinates leftCoordinates left table)
      (Option.isNone <$> finalizeResolvedCoordinates rightCoordinates right table)
      BoolImp := by
  classical
  let leftBase := leftCoordinates.toFinset.toList
  let rightBase := rightCoordinates.toFinset.toList
  let leftExtra := (rightCoordinates.toFinset \ leftCoordinates.toFinset).toList
  let rightExtra := (leftCoordinates.toFinset \ rightCoordinates.toFinset).toList
  have hleftBasePerm : leftBase.Perm leftCoordinates := by
    simpa [leftBase] using List.toFinset_toList hleftNodup
  have hrightBasePerm : rightBase.Perm rightCoordinates := by
    simpa [rightBase] using List.toFinset_toList hrightNodup
  have hleftBaseCovered : PendingCovered leftBase left := by
    intro entry hentry
    have hmem := hleftCovered entry hentry
    simpa [leftBase] using hmem
  have hrightBaseCovered : PendingCovered rightBase right := by
    intro entry hentry
    have hmem := hrightCovered entry hentry
    simpa [rightBase] using hmem
  have hleftDisjoint : leftExtra.Disjoint leftBase := by
    rw [List.disjoint_left]
    intro coordinate hleftExtra hleftBase
    simp only [leftExtra, Finset.mem_toList, Finset.mem_sdiff] at hleftExtra
    simp only [leftBase, Finset.mem_toList, List.mem_toFinset] at hleftBase
    exact hleftExtra.2 (by simpa using hleftBase)
  have hrightDisjoint : rightExtra.Disjoint rightBase := by
    rw [List.disjoint_left]
    intro coordinate hrightExtra hrightBase
    simp only [rightExtra, Finset.mem_toList, Finset.mem_sdiff] at hrightExtra
    simp only [rightBase, Finset.mem_toList, List.mem_toFinset] at hrightBase
    exact hrightExtra.2 (by simpa using hrightBase)
  have hleftAugNodup : (leftExtra ++ leftBase).Nodup :=
    List.Nodup.append (Finset.nodup_toList _) (Finset.nodup_toList _) hleftDisjoint
  have hrightAugNodup : (rightExtra ++ rightBase).Nodup :=
    List.Nodup.append (Finset.nodup_toList _) (Finset.nodup_toList _) hrightDisjoint
  have haugPerm : (leftExtra ++ leftBase).Perm (rightExtra ++ rightBase) := by
    apply List.perm_of_nodup_nodup_toFinset_eq hleftAugNodup hrightAugNodup
    ext coordinate
    simp only [List.toFinset_append, leftExtra, rightExtra, leftBase, rightBase,
      Finset.toList_toFinset, Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset]
    by_cases hleft : coordinate ∈ leftCoordinates <;>
      by_cases hright : coordinate ∈ rightCoordinates <;> simp [hleft, hright]
  have hleftPermDist :
      evalDist (Option.isNone <$>
          finalizeResolvedCoordinates leftBase left table) =
        evalDist (Option.isNone <$>
          finalizeResolvedCoordinates leftCoordinates left table) := by
    rw [evalDist_map, evalDist_map,
      evalDist_finalizeResolvedCoordinates_perm hleftBasePerm left table]
  have hrightPermDist :
      evalDist (Option.isNone <$>
          finalizeResolvedCoordinates rightBase right table) =
        evalDist (Option.isNone <$>
          finalizeResolvedCoordinates rightCoordinates right table) := by
    rw [evalDist_map, evalDist_map,
      evalDist_finalizeResolvedCoordinates_perm hrightBasePerm right table]
  have hleftAug := evalDist_map_isNone_finalizeResolvedCoordinates_append_irrelevant
    table leftExtra leftBase left (Finset.nodup_toList _)
    (by
      intro coordinate hleftExtra
      simp only [leftExtra, Finset.mem_toList, Finset.mem_sdiff] at hleftExtra
      simp only [leftBase, Finset.mem_toList, List.mem_toFinset]
      simpa using hleftExtra.2)
    hleftBaseCovered hview.leftConsistent hview.leftStarts hview.leftClean
  have hrightAug := evalDist_map_isNone_finalizeResolvedCoordinates_append_irrelevant
    table rightExtra rightBase right (Finset.nodup_toList _)
    (by
      intro coordinate hrightExtra
      simp only [rightExtra, Finset.mem_toList, Finset.mem_sdiff] at hrightExtra
      simp only [rightBase, Finset.mem_toList, List.mem_toFinset]
      simpa using hrightExtra.2)
    hrightBaseCovered hview.rightConsistent hview.rightStarts hview.rightClean
  have hsameAug :=
    relTriple_map_isNone_finalizeResolvedCoordinates_of_finalizationViewLE table
      (leftExtra ++ leftBase) left right hview
  have hpermAug :
      evalDist (Option.isNone <$> finalizeResolvedCoordinates
          (leftExtra ++ leftBase) right table) =
        evalDist (Option.isNone <$> finalizeResolvedCoordinates
          (rightExtra ++ rightBase) right table) := by
    rw [evalDist_map, evalDist_map,
      evalDist_finalizeResolvedCoordinates_perm haugPerm right table]
  have hleftToAug :
      evalDist (Option.isNone <$>
          finalizeResolvedCoordinates leftCoordinates left table) =
        evalDist (Option.isNone <$>
          finalizeResolvedCoordinates (leftExtra ++ leftBase) left table) :=
    hleftPermDist.symm.trans hleftAug.symm
  have hrightFromAug :
      evalDist (Option.isNone <$>
          finalizeResolvedCoordinates (leftExtra ++ leftBase) right table) =
        evalDist (Option.isNone <$>
          finalizeResolvedCoordinates rightCoordinates right table) :=
    hpermAug.trans (hrightAug.trans hrightPermDist)
  exact relTriple_of_evalDist_eq_right hrightFromAug
    (relTriple_of_evalDist_eq_left hleftToAug hsameAug)

set_option maxRecDepth 100000 in
theorem relTriple_finishResolvedRunIsNone_of_finalizationContextLE
    (table : OtsSecretIndex → HashOutput)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftValue rightValue : α)
    (hcontext : FinalizationContextLE table left right) :
    RelTriple
      (finishResolvedRunIsNone
        (some ⟨left, leftFuel, leftValue, table⟩))
      (finishResolvedRunIsNone
        (some ⟨right, rightFuel, rightValue, table⟩))
      BoolImp := by
  rw [finishResolvedRunIsNone_some_eq_finalize _ hcontext.leftCompletable,
    finishResolvedRunIsNone_some_eq_finalize _ hcontext.rightCompletable]
  exact relTriple_map_isNone_finalizeResolvedCoordinates_of_finalizationViewLE_covered
    table left.state.coordinates.toList right.state.coordinates.toList left right hcontext.view
      left.state.coordinates.nodup_toList right.state.coordinates.nodup_toList
      (pendingCovered_coordinates_toList left) (pendingCovered_coordinates_toList right)

set_option maxRecDepth 100000 in
theorem relTriple_classifyDirectOrdinaryObserve_resolvedFinalization_of_contextLE
    (table : OtsSecretIndex → HashOutput)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftValue rightValue : α)
    (hcontext : FinalizationContextLE table left right) :
    RelTriple
      (classifyDirectOrdinaryObserve table (resolvedFinalizationObserve table)
        left leftFuel leftValue)
      (classifyDirectOrdinaryObserve table (resolvedFinalizationObserve table)
        right rightFuel rightValue)
      BoolImp := by
  have hleftNotPrivate :=
    not_privateStructuralHit_of_deferredCompletable hcontext.leftCompletable
  have hrightNotPrivate :=
    not_privateStructuralHit_of_deferredCompletable hcontext.rightCompletable
  simp only [classifyDirectOrdinaryObserve, hleftNotPrivate, hrightNotPrivate,
    hcontext.leftCompletable, hcontext.rightCompletable, ↓reduceIte,
    resolvedFinalizationObserve]
  exact relTriple_finishResolvedRunIsNone_of_finalizationContextLE table left right leftFuel
    rightFuel leftValue rightValue hcontext

theorem relTriple_finishDirectDetailedOrdinaryObserve_of_stableRunEq
    (table : OtsSecretIndex → HashOutput)
    (leftRun rightRun : ProbComp
      (DirectDetailedResult (α × SplitHashCache)))
    (leftObserve rightObserve : DeferredContext → Nat →
      (α × SplitHashCache) → ProbComp Bool)
    (hrun : RelTriple leftRun rightRun
      (DirectDetailedOrdinaryStableRunEq table))
    (hclean : ∀ leftResult rightResult,
      DirectDetailedResult.done leftResult ∈ support leftRun →
      DirectDetailedResult.done rightResult ∈ support rightRun →
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        (leftObserve leftResult.context leftResult.remaining leftResult.value)
        (rightObserve rightResult.context rightResult.remaining rightResult.value)
        BoolImp)
    (hdoomed : ∀ result,
      DirectDetailedResult.done result ∈ support rightRun →
      OrdinaryMaterializedDoomedRun table result →
      evalDist (rightObserve result.context result.remaining result.value) =
        evalDist (pure true : ProbComp Bool)) :
    RelTriple
      (leftRun >>= finishDirectDetailedOrdinaryObserve leftObserve)
      (rightRun >>= finishDirectDetailedOrdinaryObserve rightObserve)
      BoolImp := by
  have hleftSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hrun
      (fun result => result ∈ support leftRun) (fun result hresult => hresult)
  have hbothSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupport
  apply relTriple_bind hbothSupport
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hrelation, hleftMem⟩, hrightMem⟩
  cases leftResult with
  | stopped leftReason =>
      cases leftReason with
      | privateStructuralHit =>
          exact relTriple_false_any
            (finishDirectDetailedOrdinaryObserve rightObserve rightResult)
      | ordinaryHit =>
          cases rightResult with
          | stopped rightReason =>
              cases rightReason with
              | privateStructuralHit => contradiction
              | ordinaryHit => exact relTriple_pure_pure (fun h => h)
              | fuelExhausted => exact relTriple_pure_pure (fun h => h)
          | done rightResult =>
              exact relTriple_any_true_of_evalDist_eq_true (pure true)
                (rightObserve rightResult.context rightResult.remaining rightResult.value)
                (hdoomed rightResult hrightMem hrelation)
      | fuelExhausted =>
          cases rightResult with
          | stopped rightReason =>
              cases rightReason with
              | privateStructuralHit => contradiction
              | ordinaryHit => exact relTriple_pure_pure (fun h => h)
              | fuelExhausted => exact relTriple_pure_pure (fun h => h)
          | done rightResult =>
              exact relTriple_any_true_of_evalDist_eq_true (pure true)
                (rightObserve rightResult.context rightResult.remaining rightResult.value)
                (hdoomed rightResult hrightMem hrelation)
  | done leftResult =>
      cases rightResult with
      | stopped rightReason =>
          cases rightReason with
          | privateStructuralHit => contradiction
          | ordinaryHit =>
              exact relTriple_any_true_of_evalDist_eq_true
                (leftObserve leftResult.context leftResult.remaining leftResult.value)
                (pure true) rfl
          | fuelExhausted =>
              exact relTriple_any_true_of_evalDist_eq_true
                (leftObserve leftResult.context leftResult.remaining leftResult.value)
                (pure true) rfl
      | done rightResult =>
          rcases hrelation with hcleanRelation | hdoomedRelation
          · exact hclean leftResult rightResult hleftMem hrightMem hcleanRelation
          · exact relTriple_any_true_of_evalDist_eq_true
              (leftObserve leftResult.context leftResult.remaining leftResult.value)
              (rightObserve rightResult.context rightResult.remaining rightResult.value)
              (hdoomed rightResult hrightMem hdoomedRelation)

set_option maxRecDepth 100000 in
theorem relTriple_runDirectDetailedOrdinaryObserve_maskedPublishedTreeRoot
    (table : OtsSecretIndex → HashOutput) (fuel : Nat)
    (leftObserve rightObserve : DeferredContext → Nat →
      (Digest × SplitHashCache) → ProbComp Bool)
    (hclean : ∀ leftResult rightResult,
      DirectDetailedResult.done leftResult ∈ support
        (runDirectResolvedDetailedFromTable
          { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
            values := emptyDeferredStructuralValues }
          fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)) →
      DirectDetailedResult.done rightResult ∈ support
        (runDirectResolvedDetailedFromTable
          (directDeferredContext
            (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
          fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)) →
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        (leftObserve leftResult.context leftResult.remaining leftResult.value)
        (rightObserve rightResult.context rightResult.remaining rightResult.value)
        BoolImp)
    (hdoomed : ∀ result,
      DirectDetailedResult.done result ∈ support
        (runDirectResolvedDetailedFromTable
          (directDeferredContext
            (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
          fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)) →
      OrdinaryMaterializedDoomedRun table result →
      evalDist (rightObserve result.context result.remaining result.value) =
        evalDist (pure true : ProbComp Bool)) :
    RelTriple
      (runDirectDetailedOrdinaryObserve leftObserve
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))
      (runDirectDetailedOrdinaryObserve rightObserve
        (directDeferredContext
          (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))
      BoolImp := by
  apply relTriple_finishDirectDetailedOrdinaryObserve_of_stableRunEq table
  · exact ordinaryMaterializedStableCouples_maskedPublishedTreeRoot table
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues }
      (directDeferredContext
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
      fuel fuel emptySplitHashCache emptySplitHashCache
      (finalizationContextLE_empty table) le_rfl rfl rfl
      (fun _ _ hvalue => hvalue) publishedValues_empty rfl
  · exact hclean
  · exact hdoomed

theorem evalDist_runDirectDetailedOrdinaryObserve_bind
    (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (observe : DeferredContext → Nat → β → ProbComp Bool)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist
      (runDirectDetailedOrdinaryObserve observe context fuel table (left >>= next)) =
    evalDist (runDirectResolvedDetailedFromTable context fuel table left >>=
        finishDirectDetailedOrdinaryObserve
          (fun nextContext remaining value =>
            runDirectDetailedOrdinaryObserve observe nextContext remaining table
              (next value))) := by
  unfold runDirectDetailedOrdinaryObserve
  rw [runDirectResolvedDetailedFromTable_bind, bind_assoc]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | stopped reason => cases reason <;> rfl
  | done result =>
      have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
        left context fuel table result hresult
      have hcore := resolvedCore_of_mem_runDirectResolvedFromTable
        left context fuel table result hconsistent hstarts hdirect
      simp [finishDirectDetailedOrdinaryObserve, hcore.1]

set_option maxRecDepth 100000 in
theorem relTriple_finishDirectDetailedOrdinaryObserve_of_runEq
    (table : OtsSecretIndex → HashOutput)
    (leftRun rightRun : ProbComp
      (DirectDetailedResult (α × SplitHashCache)))
    (leftObserve rightObserve : DeferredContext → Nat →
      (α × SplitHashCache) → ProbComp Bool)
    (hrun : RelTriple leftRun rightRun (DirectDetailedOrdinaryRunEq table))
    (hleftPublished : ∀ result,
      DirectDetailedResult.done result ∈ support leftRun →
        PublishedValues result.context.state)
    (hclean : ∀ leftResult rightResult,
      DirectDetailedResult.done leftResult ∈ support leftRun →
      DirectDetailedResult.done rightResult ∈ support rightRun →
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        (leftObserve (canonicalizeMaterializedValues table leftResult.context)
          leftResult.remaining leftResult.value)
        (rightObserve rightResult.context rightResult.remaining rightResult.value)
        BoolImp)
    (hdoomed : ∀ result,
      DirectDetailedResult.done result ∈ support rightRun →
      OrdinaryMaterializedDoomedRun table result →
      evalDist (rightObserve result.context result.remaining result.value) =
        evalDist (pure true : ProbComp Bool)) :
    RelTriple
      (leftRun >>= finishDirectDetailedOrdinaryObserve
        (canonicalizeDirectDetailedOrdinaryObserve table leftObserve))
      (rightRun >>= finishDirectDetailedOrdinaryObserve rightObserve)
      BoolImp := by
  have hleftSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hrun
      (fun result => result ∈ support leftRun) (fun result hresult => hresult)
  have hbothSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupport
  apply relTriple_bind hbothSupport
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hrelation, hleftMem⟩, hrightMem⟩
  cases leftResult with
  | stopped leftReason =>
      cases leftReason with
      | privateStructuralHit =>
          exact relTriple_false_any
            (finishDirectDetailedOrdinaryObserve rightObserve rightResult)
      | ordinaryHit =>
          cases rightResult with
          | stopped rightReason =>
              cases rightReason with
              | privateStructuralHit => contradiction
              | ordinaryHit => exact relTriple_pure_pure (fun h => h)
              | fuelExhausted => exact relTriple_pure_pure (fun h => h)
          | done rightResult =>
              exact relTriple_any_true_of_evalDist_eq_true (pure true)
                (rightObserve rightResult.context rightResult.remaining rightResult.value)
                (hdoomed rightResult hrightMem hrelation)
      | fuelExhausted =>
          cases rightResult with
          | stopped rightReason =>
              cases rightReason with
              | privateStructuralHit => contradiction
              | ordinaryHit => exact relTriple_pure_pure (fun h => h)
              | fuelExhausted => exact relTriple_pure_pure (fun h => h)
          | done rightResult =>
              exact relTriple_any_true_of_evalDist_eq_true (pure true)
                (rightObserve rightResult.context rightResult.remaining rightResult.value)
                (hdoomed rightResult hrightMem hrelation)
  | done leftResult =>
      cases rightResult with
      | stopped rightReason =>
          cases rightReason with
          | privateStructuralHit => contradiction
          | ordinaryHit =>
              exact relTriple_any_true_of_evalDist_eq_true
                (canonicalizeDirectDetailedOrdinaryObserve table leftObserve
                  leftResult.context leftResult.remaining leftResult.value)
                (pure true) rfl
          | fuelExhausted =>
              exact relTriple_any_true_of_evalDist_eq_true
                (canonicalizeDirectDetailedOrdinaryObserve table leftObserve
                  leftResult.context leftResult.remaining leftResult.value)
                (pure true) rfl
      | done rightResult =>
          rcases hrelation with hcleanRelation | hprivateRelation | hdoomedRelation
          · have hcanonicalCompletable :=
              hcleanRelation.canonicalize_left.context_le.leftCompletable
            have hnotPrivate := not_privateStructuralHit_of_deferredCompletable
              hcanonicalCompletable
            simpa [finishDirectDetailedOrdinaryObserve,
              canonicalizeDirectDetailedOrdinaryObserve,
              classifyDirectDetailedOrdinaryObserve, hnotPrivate,
              hcleanRelation.left_published, hcanonicalCompletable] using
                hclean leftResult rightResult hleftMem hrightMem hcleanRelation
          · have hpublished := hleftPublished leftResult hleftMem
            have hcanonicalPrivate :=
              hprivateRelation.canonicalizeMaterializedValues (table := table) hpublished
            simp only [finishDirectDetailedOrdinaryObserve,
              canonicalizeDirectDetailedOrdinaryObserve, hcanonicalPrivate, ↓reduceIte]
            exact relTriple_false_any
              (rightObserve rightResult.context rightResult.remaining rightResult.value)
          · exact relTriple_any_true_of_evalDist_eq_true
              (canonicalizeDirectDetailedOrdinaryObserve table leftObserve
                leftResult.context leftResult.remaining leftResult.value)
              (rightObserve rightResult.context rightResult.remaining rightResult.value)
              (hdoomed rightResult hrightMem hdoomedRelation)

set_option maxRecDepth 100000 in
theorem evalDist_runDirectDetailedOrdinaryObserve_eq_true_of_materializedDoomed
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (hdoomed : DoomedResolvedContext table context)
    (hmaterialized : context = directDeferredContext context.state)
    (hobserve : ∀ result,
      DirectDetailedResult.done result ∈ support
        (runDirectResolvedDetailedFromTable context fuel table computation) →
      FinalizationDoomedRun table (some result) →
      result.context = directDeferredContext result.context.state →
      evalDist (observe result.context result.remaining result.value) =
        evalDist (pure true : ProbComp Bool)) :
    evalDist (runDirectDetailedOrdinaryObserve observe context fuel table computation) =
      evalDist (pure true : ProbComp Bool) := by
  unfold runDirectDetailedOrdinaryObserve
  calc
    _ = evalDist
        (runDirectResolvedDetailedFromTable context fuel table computation >>= fun _ =>
          pure true) := by
      apply evalDist_bind_congr
      intro result hresult
      have hshape : DirectDetailedMaterialized result := by
        rw [hmaterialized] at hresult
        exact directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
          computation context.state fuel table result hresult
      cases result with
      | stopped reason =>
          cases reason with
          | privateStructuralHit => exact False.elim hshape
          | ordinaryHit => rfl
          | fuelExhausted => rfl
      | done result =>
          exact hobserve result hresult
            (finalizationDoomedRun_of_mem_runDirectResolvedDetailedFromTable table
              computation context fuel result hdoomed hresult)
            hshape
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (runDirectResolvedDetailedFromTable context fuel table computation)
      (by simp [runDirectResolvedDetailedFromTable]) (pure true)

set_option maxRecDepth 100000 in
theorem relTriple_directDetailedBoundaryOrdinaryObserve_maskedExpandedAdversaryImpl
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftObserve rightObserve : DeferredContext → Nat →
      (α × SplitHashCache) → ProbComp Bool)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey)) computation).IsQueryBoundP
              (fun query => query matches Sum.inr _) leftFuel)
    (hterminal : ∀ value nextLeft nextRight nextLeftFuel nextRightFuel
        nextLeftCache nextRightCache,
      FinalizationContextLE table nextLeft nextRight →
      nextLeftFuel ≤ nextRightFuel →
      ordinaryQueryCache nextLeftCache = ordinaryQueryCache nextRightCache →
      nextLeft.state.revealed = nextRight.state.revealed →
      LazyRevealProbe.ValuesLE nextLeft.state nextRight.state →
      PublishedValues nextLeft.state →
      nextRight = directDeferredContext nextRight.state →
      RelTriple
        (leftObserve nextLeft nextLeftFuel (value, nextLeftCache))
        (rightObserve nextRight nextRightFuel (value, nextRightCache)) BoolImp)
    (hdoomed : ∀ result : ResolvedRunResult (α × SplitHashCache),
      FinalizationDoomedRun table (some result) →
      result.context = directDeferredContext result.context.state →
      evalDist (rightObserve result.context result.remaining result.value) =
        evalDist (pure true : ProbComp Bool)) :
    RelTriple
      (directDetailedBoundaryOrdinaryObserve
        (maskedExpandedAdversaryImpl parameter root ftsSecret) computation leftObserve
        left leftFuel table leftCache)
      (runDirectDetailedOrdinaryObserve rightObserve right rightFuel table
        ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
          computation).run rightCache)) BoolImp := by
  induction computation using OracleComp.inductionOn generalizing
      left right leftFuel rightFuel leftCache rightCache with
  | pure value =>
      simp only [directDetailedBoundaryOrdinaryObserve, OracleComp.construct_pure,
        simulateQ_pure, StateT.run_pure]
      simpa [runDirectDetailedOrdinaryObserve, runDirectResolvedDetailedFromTable_pure,
        finishDirectDetailedOrdinaryObserve] using
          hterminal value left right leftFuel rightFuel leftCache rightCache hcontext hfuel
            hcache hrevealed hvalues hpublished hrightMaterialized
  | query_bind input next ih =>
      rw [directDetailedBoundaryOrdinaryObserve, OracleComp.construct_query_bind]
      let leftNextObserve : DeferredContext → Nat →
          ((OracleWorld + SigningSpec).Range input × SplitHashCache) → ProbComp Bool :=
        fun nextContext remaining value =>
          directDetailedBoundaryOrdinaryObserve
            (maskedExpandedAdversaryImpl parameter root ftsSecret) (next value.1)
            leftObserve nextContext remaining table value.2
      let rightNextObserve : DeferredContext → Nat →
          ((OracleWorld + SigningSpec).Range input × SplitHashCache) → ProbComp Bool :=
        fun nextContext remaining value =>
          runDirectDetailedOrdinaryObserve rightObserve nextContext remaining table
            ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
              (next value.1)).run value.2)
      have hrightFactor :
          evalDist
            (runDirectDetailedOrdinaryObserve rightObserve right rightFuel table
              ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
                (OracleSpec.query input >>= next)).run rightCache)) =
          evalDist
            (runDirectResolvedDetailedFromTable right rightFuel table
              ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run rightCache) >>=
                finishDirectDetailedOrdinaryObserve rightNextObserve) := by
        rw [simulateQ_query_bind, StateT.run_bind]
        exact evalDist_runDirectDetailedOrdinaryObserve_bind table right rightFuel
          ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run rightCache)
          (fun value =>
            (simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
              (next value.1)).run value.2)
          rightObserve hcontext.rightValid.valuesConsistent hcontext.view.rightStarts
      apply relTriple_of_evalDist_eq_right hrightFactor.symm
      apply relTriple_finishDirectDetailedOrdinaryObserve_of_runEq table
      · apply relTriple_runDirectResolvedDetailed_maskedExpandedAdversaryImpl
        · exact hcontext
        · intro houter
          cases input with
          | inl worldInput =>
              cases worldInput with
              | inl n => simp [IsOuterHash] at houter
              | inr hashInput =>
                  rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                    OracleComp.isQueryBoundP_query_bind_iff] at hbound
                  simpa using hbound.1
          | inr message => simp [IsOuterHash] at houter
        · exact hfuel
        · exact hcache
        · exact hrevealed
        · exact hvalues
        · exact hpublished
        · exact hrightMaterialized
      · intro result hresult
        exact publishedValues_of_done_runDirectResolvedDetailedFromTable
          (maskedExpandedAdversaryImpl parameter root ftsSecret input)
          (preservesPublishedValuesImpl_maskedExpandedAdversaryImpl parameter root ftsSecret
            input)
          left leftFuel table leftCache result hpublished hresult
      · rintro ⟨leftContext, leftRemaining, ⟨leftOutput, leftFinalCache⟩, leftTable⟩
          ⟨rightContext, rightRemaining, ⟨rightOutput, rightFinalCache⟩, rightTable⟩
          hleftMem hrightMem hrelation
        have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
          ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run leftCache)
          left leftFuel table
            ⟨leftContext, leftRemaining, (leftOutput, leftFinalCache), leftTable⟩ hleftMem
        have hraw := raw_done_of_mem_runDirectResolvedFromTable
          ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run leftCache)
          left leftFuel table
            ⟨leftContext, leftRemaining, (leftOutput, leftFinalCache), leftTable⟩ hdirect
        have hstepBound := maskedExpandedAdversaryImpl_step_isProbeBound parameter root
          ftsSecret input leftCache
        have hremaining := LazyRevealProbe.fuel_le_remaining_add_of_mem_support_runRaw_done
          left.state leftContext.state leftFuel leftRemaining
          (if IsOuterHash input then 1 else 0)
          ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run leftCache)
          (leftOutput, leftFinalCache) hstepBound hraw
        have htailBound :
            (simulateQ
              (SphincsSecurity.expandedAdversaryImpl
                (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                  SecretKey))
              (next leftOutput)).IsQueryBoundP
                (fun query => query matches Sum.inr _) leftRemaining := by
          cases input with
          | inl worldInput =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                OracleComp.isQueryBoundP_query_bind_iff] at hbound
              cases worldInput with
              | inl n =>
                  exact (hbound.2 leftOutput).mono (by
                    simpa [IsOuterHash] using hremaining)
              | inr hashInput =>
                  have htail :
                      (simulateQ
                        (SphincsSecurity.expandedAdversaryImpl
                          (⟨parameter, root,
                            tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
                        (next leftOutput)).IsQueryBoundP
                          (fun query => query matches Sum.inr _) (leftFuel - 1) := by
                    simpa [IsOuterHash] using hbound.2 leftOutput
                  apply htail.mono
                  change leftFuel ≤ leftRemaining + 1 at hremaining
                  omega
          | inr message =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
              change Option Signature at leftOutput
              change LazyRevealProbe.RawResult.done leftContext.state
                  leftRemaining (leftOutput, leftFinalCache) ∈ support
                (LazyRevealProbe.runRaw left.state leftFuel
                  ((maskedSigningImpl parameter root ftsSecret message).run leftCache)) at hraw
              have houtput : leftOutput ∈ support
                  (scheme.sign
                    (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                      SecretKey) message) := by
                exact maskedSign_done_output_mem_support parameter root table ftsSecret
                  message left.state leftContext.state leftCache leftFinalCache
                  leftFuel leftRemaining leftOutput
                    hrelation.context_le.view.leftStarts (by
                      simpa only [SigningSpec, maskedExpandedAdversaryImpl,
                        maskedSigningImpl] using hraw)
              exact (isQueryBoundP_of_bind hbound leftOutput houtput).mono (by
                simpa [IsOuterHash] using hremaining)
        simp only [rightNextObserve]
        have houtputEq : leftOutput = rightOutput := hrelation.value_eq
        rw [← houtputEq]
        exact ih leftOutput
            (canonicalizeMaterializedValues table leftContext) rightContext
            leftRemaining rightRemaining leftFinalCache rightFinalCache
            hrelation.canonicalize_left.context_le hrelation.remaining_le hrelation.cache_eq
            hrelation.canonicalize_left.revealed_eq hrelation.canonicalize_left.values_le
            hrelation.canonicalize_left.left_published hrelation.right_materialized htailBound
      · intro result hresult hdoomedRun
        exact evalDist_runDirectDetailedOrdinaryObserve_eq_true_of_materializedDoomed
          table
          ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
            (next result.value.1)).run result.value.2)
          rightObserve result.context result.remaining hdoomedRun.1.2 hdoomedRun.2
            (fun nextResult _ => hdoomed nextResult)

theorem not_privateStructuralHit_of_directDeferredContext
    (context : DeferredContext)
    (hmaterialized : context = directDeferredContext context.state) :
    ¬PrivateStructuralHit context := by
  intro hprivate
  rcases hprivate with ⟨position, output, hhidden, hvalue, _hhit⟩
  have hsame : context.values position = context.state.values (.position position) := by
    rw [hmaterialized]
    rfl
  rw [hsame, hhidden] at hvalue
  contradiction

noncomputable def retainedResolvedFinalizationOrdinaryObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) : ProbComp Bool :=
  classifyDirectOrdinaryObserve table (resolvedFinalizationObserve table)
    context fuel ((root, value.1), value.2)

set_option maxRecDepth 100000 in
theorem relTriple_directDetailedRetainedRestOrdinaryObserve
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) leftFuel) :
    RelTriple
      (directDetailedBoundaryOrdinaryObserve
        (maskedExpandedAdversaryImpl parameter root ftsSecret)
        (retainedGameRestComputation adversary ⟨root, parameter⟩)
        (retainedResolvedFinalizationOrdinaryObserve table root)
        left leftFuel table leftCache)
      (runDirectDetailedOrdinaryObserve
        (retainedResolvedFinalizationOrdinaryObserve table root)
        right rightFuel table
        ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
          (retainedGameRestComputation adversary ⟨root, parameter⟩)).run rightCache))
      BoolImp := by
  apply relTriple_directDetailedBoundaryOrdinaryObserve_maskedExpandedAdversaryImpl
    parameter root table ftsSecret
  · exact hcontext
  · exact hfuel
  · exact hcache
  · exact hrevealed
  · exact hvalues
  · exact hpublished
  · exact hrightMaterialized
  · exact hbound
  · intro value nextLeft nextRight nextLeftFuel nextRightFuel nextLeftCache nextRightCache
      hnextContext _hnextFuel _hnextCache _hnextRevealed _hnextValues _hnextPublished
      _hnextMaterialized
    exact relTriple_classifyDirectOrdinaryObserve_resolvedFinalization_of_contextLE table
      nextLeft nextRight nextLeftFuel nextRightFuel
      ((root, value), nextLeftCache) ((root, value), nextRightCache) hnextContext
  · intro result hdoomed hmaterialized
    have hnotPrivate :=
      not_privateStructuralHit_of_directDeferredContext result.context hmaterialized
    simp [retainedResolvedFinalizationOrdinaryObserve,
      classifyDirectOrdinaryObserve, hnotPrivate, hdoomed.2.2.2]

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def granularDetailedRetainedRestOrdinaryObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp Bool :=
  directDetailedBoundaryOrdinaryObserve
    (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationOrdinaryObserve table value.1)
    context fuel table value.2

noncomputable def materializedDetailedRetainedRestOrdinaryObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp Bool :=
  runDirectDetailedOrdinaryObserve
    (retainedResolvedFinalizationOrdinaryObserve table value.1)
    context fuel table
    ((simulateQ (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
      (retainedGameRestComputation adversary ⟨value.1, parameter⟩)).run value.2)

noncomputable def granularAllDirectBoundaryDetailedRetainedOrdinary
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool :=
  runDirectDetailedOrdinaryObserve
    (granularDetailedRetainedRestOrdinaryObserve adversary parameter table ftsSecret)
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

noncomputable def materializedBoundaryDetailedRetainedOrdinary
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool :=
  runDirectDetailedOrdinaryObserve
    (materializedDetailedRetainedRestOrdinaryObserve adversary parameter table ftsSecret)
    (directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

set_option maxRecDepth 100000 in
theorem fuel_le_remaining_of_done_maskedPublishedTreeRoot
    (table : OtsSecretIndex → HashOutput) (fuel : Nat)
    (result : ResolvedRunResult (Digest × SplitHashCache))
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    fuel ≤ result.remaining := by
  have hdirect : some result ∈ support
      (runDirectResolvedFromTable
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)) :=
    mem_support_runDirectResolvedFromTable_of_done_detailed
      (alpha := Digest × SplitHashCache)
      (computation := maskedPublishedTreeRoot.run emptySplitHashCache)
      (context :=
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues })
      (fuel := fuel) (table := table) (result := result) hresult
  have hraw : LazyRevealProbe.RawResult.done result.context.state result.remaining result.value ∈
      support (LazyRevealProbe.runRaw
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel
        (maskedPublishedTreeRoot.run emptySplitHashCache)) :=
    raw_done_of_mem_runDirectResolvedFromTable
      (computation := maskedPublishedTreeRoot.run emptySplitHashCache)
      (context :=
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues })
      (fuel := fuel) (table := table) (result := result) hdirect
  have hremaining := LazyRevealProbe.fuel_le_remaining_add_of_mem_support_runRaw_done
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
    result.context.state fuel result.remaining 0
    (maskedPublishedTreeRoot.run emptySplitHashCache) result.value
    (maskedPublishedTreeRoot_probeFree emptySplitHashCache) hraw
  simpa using hremaining

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem relTriple_granularAllDirectBoundaryDetailedRetainedOrdinary
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (hparameter : parameter ∈ support sampleParameter)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    RelTriple
      (granularAllDirectBoundaryDetailedRetainedOrdinary adversary parameter table ftsSecret q)
      (materializedBoundaryDetailedRetainedOrdinary adversary parameter table ftsSecret q)
      BoolImp := by
  unfold granularAllDirectBoundaryDetailedRetainedOrdinary
    materializedBoundaryDetailedRetainedOrdinary
  apply relTriple_runDirectDetailedOrdinaryObserve_maskedPublishedTreeRoot table q
  · intro leftResult rightResult hleftMem _hrightMem hrelation
    have hremaining : q ≤ leftResult.remaining :=
      fuel_le_remaining_of_done_maskedPublishedTreeRoot
        table q leftResult hleftMem
    have hbound := isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter
      hparameter table ftsSecret hfts leftResult.value.1
    have htailBound := hbound.mono (by simpa using hremaining)
    have hroot : leftResult.value.1 = rightResult.value.1 := hrelation.value_eq
    unfold granularDetailedRetainedRestOrdinaryObserve
      materializedDetailedRetainedRestOrdinaryObserve
    rw [← hroot]
    exact relTriple_directDetailedRetainedRestOrdinaryObserve adversary parameter
      leftResult.value.1 table ftsSecret leftResult.context rightResult.context
      leftResult.remaining rightResult.remaining leftResult.value.2 rightResult.value.2
      hrelation.context_le hrelation.remaining_le hrelation.cache_eq hrelation.revealed_eq
      hrelation.values_le hrelation.left_published hrelation.right_materialized htailBound
  · intro result _hresult hdoomed
    unfold materializedDetailedRetainedRestOrdinaryObserve
    exact evalDist_runDirectDetailedOrdinaryObserve_eq_true_of_materializedDoomed table
      ((simulateQ (maskedExpandedAdversaryImpl parameter result.value.1 ftsSecret)
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)).run
          result.value.2)
      (retainedResolvedFinalizationOrdinaryObserve table result.value.1)
      result.context result.remaining hdoomed.1.2 hdoomed.2
      (fun finalResult _hfinal hfinalDoomed hfinalMaterialized => by
        have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
          finalResult.context hfinalMaterialized
        simp [retainedResolvedFinalizationOrdinaryObserve,
          classifyDirectOrdinaryObserve, hnotPrivate, hfinalDoomed.2.2.2])

end SphincsSecurity.Concrete.OtsProbeSimulation
