import SphincsSecurity.Proof.OtsProbeResolvedBoundaryWitnessCoverage

/-!
# Adaptive boundary witness lift

The canonical witness interpreter is coupled to the root-aware materialized interpreter. A
detailed failure on the materialized side is retained either as the first private witness or as
an ordinary failure.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

noncomputable def rootAwareMaterializedDetailedBoundaryObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      ProbComp DirectBoundaryOutcome)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp DirectBoundaryOutcome := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      (DeferredContext → Nat → (α × SplitHashCache) → ProbComp DirectBoundaryOutcome) →
      DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache →
        ProbComp DirectBoundaryOutcome)
    (fun value observe context fuel _table cache => observe context fuel (value, cache))
    (fun query _next recursivelyRun observe context fuel table cache =>
      match query with
      | .inl (.inl n) =>
          runDirectDetailedObserve
            (fun nextContext remaining value =>
              classifyDirectDetailedObserve table
                (fun finalContext finalRemaining finalValue =>
                  recursivelyRun finalValue.1 observe finalContext finalRemaining table
                    finalValue.2)
                nextContext remaining value)
            context fuel table ((splitUniformImpl n).run cache)
      | .inl (.inr input) =>
          let publicContext := materializedCanonicalContext table context.state
          let plan := purePlanProbingHashQuery parameter input publicContext.state
          runDirectDetailedObserve
            (fun nextContext remaining value =>
              classifyDirectDetailedObserve table
                (fun finalContext finalRemaining finalValue =>
                  recursivelyRun finalValue.1 observe finalContext finalRemaining table
                    finalValue.2)
                nextContext remaining value)
            context fuel table
            ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state plan).run
              cache)
      | .inr message =>
          runDirectDetailedObserve
            (fun nextContext remaining value =>
              classifyDirectDetailedObserve table
                (fun finalContext finalRemaining finalValue =>
                  recursivelyRun finalValue.1 observe finalContext finalRemaining table
                    finalValue.2)
                nextContext remaining value)
            context fuel table
            ((maskedSign parameter root ftsSecret message).run cache))
    computation observe context fuel table cache

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_normalizedPrivateWitness_rootAwareMaterializedDetailed
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftObserve : DeferredContext → Nat → (α × SplitHashCache) → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (rightObserve : DeferredContext → Nat → (α × SplitHashCache) →
      ProbComp DirectBoundaryOutcome)
    (candidates : List Probe)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache) (q bound : Nat)
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        computation).IsQueryBoundP (fun query => query matches Sum.inr _) bound)
    (hcontext : FinalizationContextLE table left right)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hcanonical : CanonicalMaterializedValues table left)
    (hleftLower : bound ≤ leftFuel) (hleftUpper : leftFuel ≤ q)
    (hrightLower : q + bound ≤ rightFuel)
    (hterminal : ∀ value nextLeft nextRight nextLeftFuel nextRightFuel
        nextLeftCache nextRightCache nextCandidates,
      FinalizationContextLE table nextLeft nextRight →
      nextLeftFuel ≤ nextRightFuel →
      ordinaryQueryCache nextLeftCache = ordinaryQueryCache nextRightCache →
      nextLeft.state.revealed = nextRight.state.revealed →
      LazyRevealProbe.ValuesLE nextLeft.state nextRight.state →
      PublishedValues nextLeft.state →
      nextRight = directDeferredContext nextRight.state →
      CanonicalMaterializedValues table nextLeft →
      RelTriple
        (leftObserve nextLeft nextLeftFuel (value, nextLeftCache) nextCandidates)
        (rightObserve nextRight nextRightFuel (value, nextRightCache))
        WitnessOrOrdinaryCovers) :
    RelTriple
      (directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
        computation leftObserve candidates left leftFuel table leftCache)
      (rootAwareMaterializedDetailedBoundaryObserve parameter root ftsSecret computation
        rightObserve right rightFuel table rightCache)
      WitnessOrOrdinaryCovers := by
  induction computation using OracleComp.inductionOn generalizing
      candidates left right leftFuel rightFuel leftCache rightCache bound with
  | pure value =>
      simp only [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
        rootAwareMaterializedDetailedBoundaryObserve, OracleComp.construct_pure]
      exact hterminal value left right leftFuel rightFuel leftCache rightCache candidates
        hcontext (by omega) hcache hrevealed hvalues hpublished hrightMaterialized hcanonical
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
        OracleComp.construct_query_bind, rootAwareMaterializedDetailedBoundaryObserve,
        OracleComp.construct_query_bind]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                OracleComp.isQueryBoundP_query_bind_iff] at hbound
              simp only
              let nextLeftObserve : DeferredContext → Nat →
                  (Fin (n + 1) × SplitHashCache) → List Probe →
                    ProbComp PrivateWitnessPlanOutput :=
                fun nextContext remaining value nextCandidates =>
                  directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root
                    ftsSecret (next value.1) leftObserve nextCandidates nextContext remaining
                    table value.2
              let nextRightObserve : DeferredContext → Nat →
                  (Fin (n + 1) × SplitHashCache) → ProbComp DirectBoundaryOutcome :=
                fun nextContext remaining value =>
                  rootAwareMaterializedDetailedBoundaryObserve parameter root ftsSecret
                    (next value.1) rightObserve nextContext remaining table value.2
              apply relTriple_finishDirectWitnessPlan_detailed_of_materializedStable table
              · exact (witnessMaterializedStableCouples_splitUniformImpl table n)
                  left right leftFuel rightFuel leftCache rightCache hcontext (by omega) hcache
                  hrevealed hvalues hpublished hrightMaterialized
              · intro nextLeft nextRight hleftSupport hrightSupport hclean
                have hcanonicalRun := hclean.canonicalize_left
                let canonical := canonicalizeMaterializedValues table nextLeft.context
                have hleftCompletable := hcanonicalRun.context_le.leftCompletable
                have hleftNotPrivate :=
                  not_privateStructuralHit_of_deferredCompletable hleftCompletable
                have hrightNotPrivate :=
                  not_privateStructuralHit_of_deferredCompletable
                    hcanonicalRun.context_le.rightCompletable
                simp only [canonicalizeDirectWitnessPlanObserve, hleftNotPrivate,
                  ↓reduceDIte, hclean.left_published, ↓reduceIte,
                  classifyDirectWitnessPlanObserve, hleftCompletable,
                  classifyDirectDetailedObserve, hrightNotPrivate,
                  hcanonicalRun.context_le.rightCompletable]
                rw [← hclean.value_eq]
                have hleftFuelPreserved : leftFuel ≤ nextLeft.remaining := by
                  have := fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                    ((splitUniformImpl n).run leftCache) left leftFuel table nextLeft 0
                    (splitUniformImpl_probeFree n leftCache) hleftSupport
                  omega
                have hrightFuelPreserved : rightFuel ≤ nextRight.remaining := by
                  have := fuel_le_remaining_add_of_done_runDirectResolvedDetailedFromTable
                    ((splitUniformImpl n).run rightCache) right rightFuel table nextRight 0
                    (splitUniformImpl_probeFree n rightCache) hrightSupport
                  omega
                have hleftRemainingUpper : nextLeft.remaining ≤ leftFuel :=
                  remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                    ((splitUniformImpl n).run leftCache) left leftFuel table nextLeft (by
                      rw [← map_erase_runDirectResolvedWitnessFromTable
                        ((splitUniformImpl n).run leftCache) left leftFuel table, support_map]
                      exact ⟨.done nextLeft, hleftSupport, rfl⟩)
                exact ih nextLeft.value.1 candidates canonical nextRight.context
                  nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2 bound
                  (hbound.2 nextLeft.value.1) hcanonicalRun.context_le hcanonicalRun.cache_eq
                  hcanonicalRun.revealed_eq hcanonicalRun.values_le
                  hcanonicalRun.left_published hcanonicalRun.right_materialized
                  (canonicalizeMaterializedValues_canonical table nextLeft.context
                    hclean.context_le.view.leftConsistent)
                  (by omega) (by omega) (by omega)
              · intro leftRun nextRight _hrightSupport hdoomed
                have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
                  nextRight.context hdoomed.2
                have hnotCompletable : ¬DeferredCompletable table nextRight.context :=
                  hdoomed.1.2.2.2
                simpa [classifyDirectDetailedObserve, hnotPrivate, hnotCompletable] using
                  (relTriple_any_ordinaryFailure_witnessOrOrdinaryCovers leftRun)
          | inr input =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                OracleComp.isQueryBoundP_query_bind_iff] at hbound
              simp only
              have hrightValues :
                  (materializedCanonicalContext table right.state).state.values =
                    left.state.values := by
                unfold materializedCanonicalContext
                rw [← hrightMaterialized]
                exact canonicalized_right_values_eq_of_finalizationContextLE hcontext
                  hrevealed hcanonical
              have hplanEq :
                  purePlanProbingHashQuery parameter input
                      (materializedCanonicalContext table right.state).state =
                    purePlanProbingHashQuery parameter input left.state :=
                purePlanProbingHashQuery_eq_of_values_eq hrightValues parameter input
              rw [hplanEq]
              let plan := purePlanProbingHashQuery parameter input left.state
              have hpublicExecutor :
                  probingHashQueryAfterRootAwarePublicPlan parameter input
                      (materializedCanonicalContext table right.state).state plan =
                    probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan :=
                probingHashQueryAfterRootAwarePublicPlan_eq_of_values_eq parameter input
                  hrightValues plan
              rw [hpublicExecutor]
              let nextCandidates := appendPlannedCandidate candidates
                (rootAwarePlannedCandidate? parameter input left.state)
              let nextLeftObserve : DeferredContext → Nat →
                  (HashOutput × SplitHashCache) → List Probe →
                    ProbComp PrivateWitnessPlanOutput :=
                fun nextContext remaining value laterCandidates =>
                  directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root
                    ftsSecret (next value.1) leftObserve laterCandidates nextContext remaining
                    table value.2
              let nextRightObserve : DeferredContext → Nat →
                  (HashOutput × SplitHashCache) → ProbComp DirectBoundaryOutcome :=
                fun nextContext remaining value =>
                  rootAwareMaterializedDetailedBoundaryObserve parameter root ftsSecret
                    (next value.1) rightObserve nextContext remaining table value.2
              have hboundPositive : 0 < bound := by
                rcases hbound.1 with hnot | hpositive
                · exact (hnot (by simp)).elim
                · exact hpositive
              apply relTriple_finishDirectWitnessPlan_detailed_of_materializedStable table
              · exact relTriple_runDirectResolvedWitness_afterPlan_rootAwarePublic table parameter
                  input left.state plan left right leftFuel rightFuel leftCache rightCache rfl
                  (by omega) (by omega) hcontext hcache hrevealed hvalues hpublished
                  hrightMaterialized
              · intro nextLeft nextRight hleftSupport hrightSupport hclean
                have hcanonicalRun := hclean.canonicalize_left
                let canonical := canonicalizeMaterializedValues table nextLeft.context
                have hleftCompletable := hcanonicalRun.context_le.leftCompletable
                have hleftNotPrivate :=
                  not_privateStructuralHit_of_deferredCompletable hleftCompletable
                have hrightNotPrivate :=
                  not_privateStructuralHit_of_deferredCompletable
                    hcanonicalRun.context_le.rightCompletable
                simp only [canonicalizeDirectWitnessPlanObserve, hleftNotPrivate,
                  ↓reduceDIte, hclean.left_published, ↓reduceIte,
                  classifyDirectWitnessPlanObserve, hleftCompletable,
                  classifyDirectDetailedObserve, hrightNotPrivate,
                  hcanonicalRun.context_le.rightCompletable]
                rw [← hclean.value_eq]
                have hleftSpent : leftFuel ≤ nextLeft.remaining + 1 :=
                  fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                    ((probingHashQueryAfterPlan parameter input plan).run leftCache)
                    left leftFuel table nextLeft 1
                    (probingHashQueryAfterPlan_isProbeBound_one parameter input plan leftCache)
                    hleftSupport
                have hrightSpent : rightFuel ≤ nextRight.remaining + 1 :=
                  fuel_le_remaining_add_of_done_runDirectResolvedDetailedFromTable
                    ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan).run
                      rightCache)
                    right rightFuel table nextRight 1
                    (probingHashQueryAfterRootAwarePublicPlan_isProbeBound_one parameter input
                      left.state plan rightCache)
                    hrightSupport
                have htail :
                    (simulateQ
                      (SphincsSecurity.expandedAdversaryImpl
                        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                          SecretKey))
                      (next nextLeft.value.1)).IsQueryBoundP
                        (fun query => query matches Sum.inr _) (bound - 1) := by
                  simpa [IsOuterHash] using hbound.2 nextLeft.value.1
                exact ih nextLeft.value.1 nextCandidates canonical nextRight.context
                  nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2
                  (bound - 1) htail hcanonicalRun.context_le hcanonicalRun.cache_eq
                  hcanonicalRun.revealed_eq hcanonicalRun.values_le
                  hcanonicalRun.left_published hcanonicalRun.right_materialized
                  (canonicalizeMaterializedValues_canonical table nextLeft.context
                    hclean.context_le.view.leftConsistent)
                  (by omega)
                  ((remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                    ((probingHashQueryAfterPlan parameter input plan).run leftCache)
                    left leftFuel table nextLeft (by
                      rw [← map_erase_runDirectResolvedWitnessFromTable
                        ((probingHashQueryAfterPlan parameter input plan).run leftCache)
                        left leftFuel table, support_map]
                      exact ⟨.done nextLeft, hleftSupport, rfl⟩)).trans hleftUpper)
                  (by omega)
              · intro leftRun nextRight _hrightSupport hdoomed
                have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
                  nextRight.context hdoomed.2
                have hnotCompletable : ¬DeferredCompletable table nextRight.context :=
                  hdoomed.1.2.2.2
                simpa [classifyDirectDetailedObserve, hnotPrivate, hnotCompletable] using
                  (relTriple_any_ordinaryFailure_witnessOrOrdinaryCovers leftRun)
      | inr message =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
          simp only
          let nextLeftObserve : DeferredContext → Nat →
              (Option Signature × SplitHashCache) → List Probe →
                ProbComp PrivateWitnessPlanOutput :=
            fun nextContext remaining value nextCandidates =>
              directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
                (next value.1) leftObserve nextCandidates nextContext remaining table value.2
          let nextRightObserve : DeferredContext → Nat →
              (Option Signature × SplitHashCache) → ProbComp DirectBoundaryOutcome :=
            fun nextContext remaining value =>
              rootAwareMaterializedDetailedBoundaryObserve parameter root ftsSecret
                (next value.1) rightObserve nextContext remaining table value.2
          apply relTriple_finishDirectWitnessPlan_detailed_of_materializedStable table
          · exact (witnessMaterializedStableCouples_maskedSign table parameter root ftsSecret
                message) left right leftFuel rightFuel leftCache rightCache hcontext (by omega)
                hcache hrevealed hvalues hpublished hrightMaterialized
          · intro nextLeft nextRight hleftSupport hrightSupport hclean
            have hcanonicalRun := hclean.canonicalize_left
            let canonical := canonicalizeMaterializedValues table nextLeft.context
            have hleftCompletable := hcanonicalRun.context_le.leftCompletable
            have hleftNotPrivate :=
              not_privateStructuralHit_of_deferredCompletable hleftCompletable
            have hrightNotPrivate :=
              not_privateStructuralHit_of_deferredCompletable
                hcanonicalRun.context_le.rightCompletable
            simp only [canonicalizeDirectWitnessPlanObserve, hleftNotPrivate,
              ↓reduceDIte, hclean.left_published, ↓reduceIte,
              classifyDirectWitnessPlanObserve, hleftCompletable,
              classifyDirectDetailedObserve, hrightNotPrivate,
              hcanonicalRun.context_le.rightCompletable]
            rw [← hclean.value_eq]
            have hleftPreserved : leftFuel ≤ nextLeft.remaining := by
              have := fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                ((maskedSign parameter root ftsSecret message).run leftCache)
                left leftFuel table nextLeft 0
                (maskedSign_probeFree parameter root ftsSecret message leftCache)
                hleftSupport
              omega
            have hrightPreserved : rightFuel ≤ nextRight.remaining := by
              have := fuel_le_remaining_add_of_done_runDirectResolvedDetailedFromTable
                ((maskedSign parameter root ftsSecret message).run rightCache)
                right rightFuel table nextRight 0
                (maskedSign_probeFree parameter root ftsSecret message rightCache)
                hrightSupport
              omega
            have hdetailed : DirectDetailedResult.done nextLeft ∈ support
                (runDirectResolvedDetailedFromTable left leftFuel table
                  ((maskedSign parameter root ftsSecret message).run leftCache)) := by
              rw [← map_erase_runDirectResolvedWitnessFromTable
                ((maskedSign parameter root ftsSecret message).run leftCache)
                left leftFuel table, support_map]
              exact ⟨.done nextLeft, hleftSupport, rfl⟩
            have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
              ((maskedSign parameter root ftsSecret message).run leftCache)
              left leftFuel table nextLeft hdetailed
            have hraw := raw_done_of_mem_runDirectResolvedFromTable
              ((maskedSign parameter root ftsSecret message).run leftCache)
              left leftFuel table nextLeft hdirect
            have houtput : nextLeft.value.1 ∈ support
                (scheme.sign
                  (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                    SecretKey) message) :=
              maskedSign_done_output_mem_support parameter root table ftsSecret message
                left.state nextLeft.context.state leftCache nextLeft.value.2 leftFuel
                nextLeft.remaining nextLeft.value.1 hclean.context_le.view.leftStarts (by
                  simpa only [SigningSpec, maskedExpandedAdversaryImpl, maskedSigningImpl]
                    using hraw)
            have htail := isQueryBoundP_of_bind hbound nextLeft.value.1 houtput
            exact ih nextLeft.value.1 candidates canonical nextRight.context
              nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2 bound
              (htail.mono (by omega)) hcanonicalRun.context_le hcanonicalRun.cache_eq
              hcanonicalRun.revealed_eq hcanonicalRun.values_le
              hcanonicalRun.left_published hcanonicalRun.right_materialized
              (canonicalizeMaterializedValues_canonical table nextLeft.context
                hclean.context_le.view.leftConsistent)
              (by omega)
              ((remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                ((maskedSign parameter root ftsSecret message).run leftCache)
                left leftFuel table nextLeft hdetailed).trans hleftUpper)
              (by omega)
          · intro leftRun nextRight _hrightSupport hdoomed
            have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
              nextRight.context hdoomed.2
            have hnotCompletable : ¬DeferredCompletable table nextRight.context :=
              hdoomed.1.2.2.2
            simpa [classifyDirectDetailedObserve, hnotPrivate, hnotCompletable] using
              (relTriple_any_ordinaryFailure_witnessOrOrdinaryCovers leftRun)

end SphincsSecurity.Concrete.OtsProbeSimulation
