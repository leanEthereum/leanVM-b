import SphincsSecurity.Proof.OtsProbeResolvedBoundaryOrdinarySigner

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

end SphincsSecurity.Concrete.OtsProbeSimulation
