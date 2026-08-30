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

end SphincsSecurity.Concrete.OtsProbeSimulation
