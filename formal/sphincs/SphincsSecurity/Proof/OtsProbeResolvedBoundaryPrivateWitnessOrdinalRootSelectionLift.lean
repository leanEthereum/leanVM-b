import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionOutcome

/-!
# Adaptive lift of delayed root selection

The local uniform, hash and signing kernels are composed through an arbitrary outer computation.
Earlier distinguished-root candidates contradict the retained good prefix, while every clean
transition recurses with the canonical left context supplied by the common finisher.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_directRootSelection_materializedOutcome
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftOutput : HashOutput) (rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hcanonical : CanonicalMaterializedValues table left)
    (hprefix : CandidatesAvoidRoots target (truncateHash leftOutput) rightRoot candidates) :
    RelTriple
      (directDetailedBoundaryPrivateOrdinalSelection ordinal parameter publicRoot ftsSecret
        computation candidates left leftFuel table leftCache)
      (materializedActualRootAvoidingOrdinalSelectionOutcome ordinal parameter publicRoot target
        (truncateHash leftOutput) rightRoot ftsSecret computation candidates right.state rightFuel
        table rightCache)
      (RootSelectionBridgeRel target leftOutput rightRoot ordinal) := by
  induction computation using OracleComp.inductionOn generalizing
      candidates left right leftFuel rightFuel leftCache rightCache with
  | pure value =>
      simp only [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_pure,
        materializedActualRootAvoidingOrdinalSelectionOutcome,
        materializedRootAvoidingOrdinalSelectionOutcome, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp only [selectedPrivateOrdinal?, hselected, ↓reduceDIte]
        apply relTriple_pure_pure
        intro hgood
        right
        simpa [MaterializedSelectionOutcome.Matches,
          materializedOrdinalSelectionMatches] using hgood.1
      · simp only [selectedPrivateOrdinal?, hselected, ↓reduceDIte]
        exact relTriple_pure_pure
          (rootSelectionBridgeRel_none_left target leftOutput rightRoot ordinal _)
  | query_bind query next ih =>
      rw [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_query_bind,
        materializedActualRootAvoidingOrdinalSelectionOutcome,
        materializedRootAvoidingOrdinalSelectionOutcome, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        apply relTriple_pure_pure
        intro hgood
        right
        simpa [MaterializedSelectionOutcome.Matches,
          materializedOrdinalSelectionMatches] using hgood.1
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                change Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α at next
                let leftObserve : DeferredContext → Nat →
                    (Fin (n + 1) × SplitHashCache) → List Probe →
                      ProbComp (Option PrivateOrdinalSelection) :=
                  fun nextContext remaining value laterCandidates =>
                    directDetailedBoundaryPrivateOrdinalSelection ordinal parameter publicRoot
                      ftsSecret (next value.1) laterCandidates nextContext remaining table value.2
                let rightObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe → ProbComp MaterializedSelectionOutcome :=
                  fun nextState remaining output nextCache laterCandidates =>
                    materializedActualRootAvoidingOrdinalSelectionOutcome ordinal parameter
                      publicRoot target (truncateHash leftOutput) rightRoot ftsSecret (next output)
                      laterCandidates nextState remaining table nextCache
                apply relTriple_rootSelection_uniform_step target leftOutput rightRoot ordinal table
                  n leftObserve rightObserve candidates left right leftFuel rightFuel leftCache
                  rightCache hcontext hfuel hcache hrevealed hvalues hpublished hrightMaterialized
                intro nextLeft nextRight hnext hnextCanonical
                rw [← hnext.value_eq]
                simpa [leftObserve, rightObserve] using
                  (ih nextLeft.value.1 candidates nextLeft.context nextRight.context
                  nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2
                  hnext.context_le hnext.remaining_le hnext.cache_eq hnext.revealed_eq
                  hnext.values_le hnext.left_published hnext.right_materialized hnextCanonical
                  hprefix)
            | inr input =>
                change HashOutput → OracleComp (OracleWorld + SigningSpec) α at next
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
                simp only
                rw [hplanEq]
                rw [← rootAwareCandidateForPlan?_purePlan parameter input left.state]
                let plan := purePlanProbingHashQuery parameter input left.state
                have hpublicExecutor :
                    probingHashQueryAfterPublicPlan parameter input
                        (materializedCanonicalContext table right.state).state plan =
                      probingHashQueryAfterPublicPlan parameter input left.state plan :=
                  probingHashQueryAfterPublicPlan_eq_of_values_eq parameter input hrightValues plan
                rw [hpublicExecutor]
                let candidate? := rootAwareCandidateForPlan? parameter input plan
                let nextCandidates := appendPlannedCandidate candidates candidate?
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input left.state))).length := by
                    simpa [plan, candidate?, nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  apply relTriple_pure_pure
                  intro hgood
                  right
                  simpa [MaterializedSelectionOutcome.Matches,
                    materializedOrdinalSelectionMatches] using hgood.1
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input left.state))).length := by
                    simpa [plan, candidate?, nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  by_cases hsafe : RootAwareCandidateAvoidsRoots target
                      (truncateHash leftOutput) rightRoot candidate?
                  · have hsafeActual : RootAwareCandidateAvoidsRoots target
                        (truncateHash leftOutput) rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input left.state)) := by
                      simpa [plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    have hnextPrefix : CandidatesAvoidRoots target
                        (truncateHash leftOutput) rightRoot nextCandidates := by
                      cases hcandidate : candidate? with
                      | none => simpa [nextCandidates, appendPlannedCandidate, hcandidate]
                          using hprefix
                      | some candidate =>
                          simpa [nextCandidates, appendPlannedCandidate, hcandidate] using
                            (hprefix.append candidate (by
                              rw [← rootAwareCandidateAvoidsRoots_iff]
                              simpa [hcandidate] using hsafe))
                    let leftObserve : DeferredContext → Nat →
                        (HashOutput × SplitHashCache) → List Probe →
                          ProbComp (Option PrivateOrdinalSelection) :=
                      fun nextContext remaining value laterCandidates =>
                        directDetailedBoundaryPrivateOrdinalSelection ordinal parameter publicRoot
                          ftsSecret (next value.1) laterCandidates nextContext remaining table
                          value.2
                    let rightObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe → ProbComp MaterializedSelectionOutcome :=
                      fun nextState remaining output nextCache laterCandidates =>
                        materializedActualRootAvoidingOrdinalSelectionOutcome ordinal parameter
                          publicRoot target (truncateHash leftOutput) rightRoot ftsSecret
                          (next output) laterCandidates nextState remaining table nextCache
                    rw [hrightMaterialized]
                    change RelTriple
                      (runDirectResolvedWitnessFromTable left leftFuel table
                          ((probingHashQueryAfterPlan parameter input plan).run leftCache) >>=
                        finishDirectPrivateOrdinalSelection
                          (canonicalizeDirectPrivateOrdinalSelection table leftObserve)
                          nextCandidates)
                      (runDirectResolvedDetailedFromTable (directDeferredContext right.state)
                          rightFuel table
                          ((probingHashQueryAfterPublicPlan parameter input left.state plan).run
                            rightCache) >>=
                        finishMaterializedSelectionOutcome target table rightObserve
                          nextCandidates)
                      (RootSelectionBridgeRel target leftOutput rightRoot ordinal)
                    have hbridge (hprobeFuel : plan.candidate? = none ∨ 0 < leftFuel) :
                        RelTriple
                          (runDirectResolvedWitnessFromTable left leftFuel table
                              ((probingHashQueryAfterPlan parameter input plan).run leftCache) >>=
                            finishDirectPrivateOrdinalSelection
                              (canonicalizeDirectPrivateOrdinalSelection table leftObserve)
                              nextCandidates)
                          (runDirectResolvedDetailedFromTable right rightFuel table
                              ((probingHashQueryAfterPublicPlan parameter input left.state plan).run
                                rightCache) >>=
                            finishMaterializedSelectionOutcome target table rightObserve
                              nextCandidates)
                          (RootSelectionBridgeRel target leftOutput rightRoot ordinal) := by
                      apply relTriple_rootSelection_hash_step target leftOutput rightRoot ordinal
                        table parameter input plan leftObserve rightObserve nextCandidates left right
                        leftFuel rightFuel leftCache rightCache hprobeFuel hcontext hfuel hcache
                        hrevealed hvalues hpublished hrightMaterialized
                      intro nextLeft nextRight hnext hnextCanonical
                      rw [← hnext.value_eq]
                      exact ih nextLeft.value.1 nextCandidates nextLeft.context nextRight.context
                        nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2
                        hnext.context_le hnext.remaining_le hnext.cache_eq hnext.revealed_eq
                        hnext.values_le hnext.left_published hnext.right_materialized
                        hnextCanonical hnextPrefix
                    rw [hrightMaterialized] at hbridge
                    cases hplanCandidate : plan.candidate? with
                    | none =>
                        exact hbridge (Or.inl hplanCandidate)
                    | some plannedCandidate =>
                        by_cases hpositive : 0 < leftFuel
                        · exact hbridge (Or.inr hpositive)
                        · have hzero : leftFuel = 0 := by omega
                          subst leftFuel
                          apply relTriple_of_evalDist_eq_left
                            (oa' := (pure none : ProbComp (Option PrivateOrdinalSelection)))
                            (by
                              unfold probingHashQueryAfterPlan executePlannedHashQuery
                              rw [StateT.run_bind]
                              rw [hplanCandidate]
                              simp only [executeCandidate?]
                              unfold probe
                              simp only [StateT.run_liftM]
                              unfold LazyRevealProbe.probeQuery
                              simp only [pure_bind, bind_assoc]
                              rw [runDirectResolvedWitnessFromTable_probe_query_bind]
                              simp [finishDirectPrivateOrdinalSelection])
                          exact relTriple_pure_none_rootSelectionBridge target leftOutput rightRoot
                            ordinal _
                  · have hsafeActual : ¬RootAwareCandidateAvoidsRoots target
                        (truncateHash leftOutput) rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input left.state)) := by
                      simpa [plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    cases hcandidate : candidate? with
                    | none =>
                        exfalso
                        apply hsafe
                        simp [RootAwareCandidateAvoidsRoots, hcandidate]
                    | some candidate =>
                        have hunsafe : ¬candidate.AvoidsRoots target
                            (truncateHash leftOutput) rightRoot := by
                          rw [← rootAwareCandidateAvoidsRoots_iff]
                          simpa [hcandidate] using hsafe
                        let leftRun : ProbComp (Option PrivateOrdinalSelection) :=
                          runDirectResolvedWitnessFromTable left leftFuel table
                              ((probingHashQueryAfterPlan parameter input plan).run leftCache) >>=
                            finishDirectPrivateOrdinalSelection
                              (canonicalizeDirectPrivateOrdinalSelection table
                                (fun nextContext remaining value laterCandidates =>
                                  directDetailedBoundaryPrivateOrdinalSelection ordinal parameter
                                    publicRoot ftsSecret (next value.1) laterCandidates nextContext
                                    remaining table value.2))
                              nextCandidates
                        have hzeroBridge : RelTriple leftRun
                            (pure (.finished none) : ProbComp MaterializedSelectionOutcome)
                            (RootSelectionBridgeRel target leftOutput rightRoot ordinal) := by
                          apply relTriple_finished_none_of_no_good target leftOutput rightRoot
                            ordinal leftRun
                          intro output houtput hgood
                          cases output with
                          | none => exact hgood
                          | some selection =>
                            have hbranchExtends :
                                PrivateOrdinalSelectionExtends nextCandidates
                                  (some selection) := by
                              unfold leftRun at houtput
                              rw [mem_support_bind_iff] at houtput
                              obtain ⟨result, hresult, hfinish⟩ := houtput
                              apply privateOrdinalSelectionExtends_of_mem_finish _ nextCandidates
                                result (output := some selection) (houtput := hfinish)
                              intro resolved nextOutput heq hnextOutput
                              subst result
                              apply privateOrdinalSelectionExtends_of_mem_canonicalize table _
                                resolved.context resolved.remaining resolved.value nextCandidates
                                (output := nextOutput) (houtput := hnextOutput)
                              intro nextContext finalOutput hfinalOutput
                              exact privateOrdinalSelectionExtends_of_mem_direct ordinal parameter
                                publicRoot ftsSecret (next resolved.value.1) nextCandidates
                                nextContext resolved.remaining table resolved.value.2 finalOutput
                                hfinalOutput
                            apply not_goodForRoots_of_unsafe_prefix (candidate := candidate)
                              hgood hbranchExtends (by omega)
                            · simp [nextCandidates, appendPlannedCandidate, hcandidate]
                            · exact hunsafe
                        dsimp [leftRun, plan, nextCandidates] at hzeroBridge
                        unfold directDetailedBoundaryPrivateOrdinalSelection at hzeroBridge
                        exact hzeroBridge
        | inr message =>
            change Option Signature → OracleComp (OracleWorld + SigningSpec) α at next
            let leftObserve : DeferredContext → Nat →
                (Option Signature × SplitHashCache) → List Probe →
                  ProbComp (Option PrivateOrdinalSelection) :=
              fun nextContext remaining value laterCandidates =>
                directDetailedBoundaryPrivateOrdinalSelection ordinal parameter publicRoot
                  ftsSecret (next value.1) laterCandidates nextContext remaining table value.2
            let rightObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe → ProbComp MaterializedSelectionOutcome :=
              fun nextState remaining output nextCache laterCandidates =>
                materializedActualRootAvoidingOrdinalSelectionOutcome ordinal parameter publicRoot
                  target (truncateHash leftOutput) rightRoot ftsSecret (next output)
                  laterCandidates nextState remaining table nextCache
            rw [hrightMaterialized]
            change RelTriple
              (runDirectResolvedWitnessFromTable left leftFuel table
                  ((maskedSign parameter publicRoot ftsSecret message).run leftCache) >>=
                finishDirectPrivateOrdinalSelection
                  (canonicalizeDirectPrivateOrdinalSelection table leftObserve) candidates)
              (runDirectResolvedDetailedFromTable (directDeferredContext right.state) rightFuel
                  table ((maskedSign parameter publicRoot ftsSecret message).run rightCache) >>=
                finishMaterializedSelectionOutcome target table rightObserve candidates)
              (RootSelectionBridgeRel target leftOutput rightRoot ordinal)
            have hsign := relTriple_rootSelection_sign_step target leftOutput rightRoot ordinal
              table parameter publicRoot ftsSecret message leftObserve rightObserve candidates left
              right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed hvalues
              hpublished hrightMaterialized (by
                intro nextLeft nextRight hnext hnextCanonical
                rw [← hnext.value_eq]
                simpa [leftObserve, rightObserve] using
                  (ih nextLeft.value.1 candidates nextLeft.context nextRight.context
                    nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2
                    hnext.context_le hnext.remaining_le hnext.cache_eq hnext.revealed_eq
                    hnext.values_le hnext.left_published hnext.right_materialized hnextCanonical
                    hprefix))
            rw [hrightMaterialized] at hsign
            exact hsign

end SphincsSecurity.Concrete.OtsProbeSimulation
