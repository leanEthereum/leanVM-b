import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionLift

/-!
# Failure-outcome projection

Every selected result of the failure-retaining materialized prefix is also selected by the
exchangeable optional prefix. Stopped, published and non-completable paths impose no obligation.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_materializedOutcome_optionalSelection
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (matchRoot : Digest) :
    RelTriple
      (materializedRootAvoidingOrdinalSelectionOutcome ordinal parameter target leftRoot rightRoot
        signer computation candidates state fuel table cache)
      (materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot rightRoot signer
        computation candidates state fuel table cache)
      (MaterializedOutcomeOptionRel target matchRoot) := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      simp only [materializedRootAvoidingOrdinalSelectionOutcome,
        materializedRootAvoidingOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure (fun hmatch => hmatch)
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure (fun hmatch => hmatch)
  | query_bind query next ih =>
      rw [materializedRootAvoidingOrdinalSelectionOutcome, OracleComp.construct_query_bind,
        materializedRootAvoidingOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure (fun hmatch => hmatch)
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                change Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α at next
                let outcomeObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe → ProbComp MaterializedSelectionOutcome :=
                  fun nextState remaining output nextCache laterCandidates =>
                    materializedRootAvoidingOrdinalSelectionOutcome ordinal parameter target
                      leftRoot rightRoot signer (next output) laterCandidates nextState remaining
                      table nextCache
                let optionObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe → ProbComp (Option Probe) :=
                  fun nextState remaining output nextCache laterCandidates =>
                    materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot
                      rightRoot signer (next output) laterCandidates nextState remaining table
                      nextCache
                apply relTriple_of_evalDist_eq_right
                  (evalDist_runDetailedMaterializedSelection_eq_clean target optionObserve
                    candidates state fuel table ((splitUniformImpl n).run cache))
                apply relTriple_bind
                  (relTriple_refl
                    (runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
                      ((splitUniformImpl n).run cache)))
                intro leftResult rightResult hresult
                subst rightResult
                apply relTriple_finishMaterializedOutcome_option target matchRoot table
                  outcomeObserve optionObserve candidates leftResult
                intro resolved hcompletable hprivate
                simpa [outcomeObserve, optionObserve] using
                  ih resolved.value.1 candidates resolved.context.state resolved.remaining
                    resolved.value.2
            | inr input =>
                change HashOutput → OracleComp (OracleWorld + SigningSpec) α at next
                let publicContext := materializedCanonicalContext table state
                let plan := purePlanProbingHashQuery parameter input publicContext.state
                let candidate? := rootAwareCandidateForPlan? parameter input plan
                let nextCandidates := appendPlannedCandidate candidates candidate?
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  exact relTriple_pure_pure (fun hmatch => hmatch)
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  by_cases hsafe : RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate?
                  · have hsafeActual : RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    let outcomeObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe → ProbComp MaterializedSelectionOutcome :=
                      fun nextState remaining output nextCache laterCandidates =>
                        materializedRootAvoidingOrdinalSelectionOutcome ordinal parameter target
                          leftRoot rightRoot signer (next output) laterCandidates nextState
                          remaining table nextCache
                    let optionObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe → ProbComp (Option Probe) :=
                      fun nextState remaining output nextCache laterCandidates =>
                        materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot
                          rightRoot signer (next output) laterCandidates nextState remaining table
                          nextCache
                    apply relTriple_of_evalDist_eq_right
                      (evalDist_runDetailedMaterializedSelection_eq_clean target optionObserve
                        nextCandidates state fuel table
                        ((probingHashQueryAfterPublicPlan parameter input publicContext.state plan).run
                          cache))
                    apply relTriple_bind
                      (relTriple_refl
                        (runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
                          ((probingHashQueryAfterPublicPlan parameter input publicContext.state plan).run
                            cache)))
                    intro leftResult rightResult hresult
                    subst rightResult
                    apply relTriple_finishMaterializedOutcome_option target matchRoot table
                      outcomeObserve optionObserve nextCandidates leftResult
                    intro resolved hcompletable hprivate
                    simpa [outcomeObserve, optionObserve] using
                      ih resolved.value.1 nextCandidates resolved.context.state
                        resolved.remaining resolved.value.2
                  · have hsafeActual : ¬RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    exact relTriple_pure_pure (fun hmatch => hmatch)
        | inr message =>
            change Option Signature → OracleComp (OracleWorld + SigningSpec) α at next
            let outcomeObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe → ProbComp MaterializedSelectionOutcome :=
              fun nextState remaining output nextCache laterCandidates =>
                materializedRootAvoidingOrdinalSelectionOutcome ordinal parameter target leftRoot
                  rightRoot signer (next output) laterCandidates nextState remaining table nextCache
            let optionObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe → ProbComp (Option Probe) :=
              fun nextState remaining output nextCache laterCandidates =>
                materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot rightRoot
                  signer (next output) laterCandidates nextState remaining table nextCache
            apply relTriple_of_evalDist_eq_right
              (evalDist_runDetailedMaterializedSelection_eq_clean target optionObserve candidates
                state fuel table ((signer message).run cache))
            apply relTriple_bind
              (relTriple_refl
                (runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
                  ((signer message).run cache)))
            intro leftResult rightResult hresult
            subst rightResult
            apply relTriple_finishMaterializedOutcome_option target matchRoot table outcomeObserve
              optionObserve candidates leftResult
            intro resolved hcompletable hprivate
            simpa [outcomeObserve, optionObserve] using
              ih resolved.value.1 candidates resolved.context.state resolved.remaining
                resolved.value.2

theorem relTriple_materializedActualOutcome_optionalSelection
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    RelTriple
      (materializedActualRootAvoidingOrdinalSelectionOutcome ordinal parameter publicRoot target
        leftRoot rightRoot ftsSecret computation candidates state fuel table cache)
      (materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target leftRoot
        rightRoot ftsSecret computation candidates state fuel table cache)
      (MaterializedOutcomeOptionRel target leftRoot) :=
  relTriple_materializedOutcome_optionalSelection ordinal parameter target leftRoot rightRoot
    (maskedSign parameter publicRoot ftsSecret) computation candidates state fuel table cache
    leftRoot

end SphincsSecurity.Concrete.OtsProbeSimulation
