import SphincsSecurity.Proof.OtsProbeResolvedBoundaryOrdinaryRefinement

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

end SphincsSecurity.Concrete.OtsProbeSimulation
