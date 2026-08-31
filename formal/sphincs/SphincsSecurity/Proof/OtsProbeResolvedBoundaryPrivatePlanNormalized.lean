import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePlanExecution

/-!
# Normalized outer plan trace

The outer private trace computes each hash plan once, records its candidate, and executes the corresponding single-probe suffix. Uniform and signing queries record no candidate.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

noncomputable def directDetailedBoundaryNormalizedPrivatePlanObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp (Bool × List Probe))
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Bool × List Probe) := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      (DeferredContext → Nat → (α × SplitHashCache) →
        List Probe → ProbComp (Bool × List Probe)) →
      List Probe → DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        SplitHashCache → ProbComp (Bool × List Probe))
    (fun value observe candidates context fuel _table cache =>
      observe context fuel (value, cache) candidates)
    (fun query _next recursivelyRun observe candidates context fuel table cache =>
      match query with
      | .inl (.inl n) =>
          runDirectDetailedPrivatePlanObserve
            (canonicalizeDirectDetailedPrivatePlanObserve table
              (fun nextContext remaining value nextCandidates =>
                recursivelyRun value.1 observe nextCandidates nextContext remaining table
                  value.2))
            candidates context fuel table ((splitUniformImpl n).run cache)
      | .inl (.inr input) =>
          let plan := purePlanProbingHashQuery parameter input context.state
          let nextCandidates := appendPlannedCandidate candidates plan.candidate?
          runDirectDetailedPrivatePlanObserve
            (canonicalizeDirectDetailedPrivatePlanObserve table
              (fun nextContext remaining value finalCandidates =>
                recursivelyRun value.1 observe finalCandidates nextContext remaining table
                  value.2))
            nextCandidates context fuel table
              ((probingHashQueryAfterPlan parameter input plan).run cache)
      | .inr message =>
          runDirectDetailedPrivatePlanObserve
            (canonicalizeDirectDetailedPrivatePlanObserve table
              (fun nextContext remaining value nextCandidates =>
                recursivelyRun value.1 observe nextCandidates nextContext remaining table
                  value.2))
            candidates context fuel table
              ((maskedSign parameter root ftsSecret message).run cache))
    computation observe candidates context fuel table cache

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_fst_directDetailedBoundaryNormalizedPrivatePlanObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp (Bool × List Probe))
    (boolObserve : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hproject : ∀ nextContext remaining value nextCandidates,
      evalDist (Prod.fst <$> observe nextContext remaining value nextCandidates) =
        evalDist (boolObserve nextContext remaining value)) :
    evalDist (Prod.fst <$>
        directDetailedBoundaryNormalizedPrivatePlanObserve parameter root ftsSecret computation
          observe candidates context fuel table cache) =
      evalDist (directDetailedBoundaryPrivateObserve
        (maskedExpandedAdversaryImpl parameter root ftsSecret) computation boolObserve
        context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivatePlanObserve, OracleComp.construct_pure,
        directDetailedBoundaryPrivateObserve, OracleComp.construct_pure]
      exact hproject context fuel (value, cache) candidates
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedPrivatePlanObserve, OracleComp.construct_query_bind,
        directDetailedBoundaryPrivateObserve, OracleComp.construct_query_bind]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              change evalDist (Prod.fst <$> runDirectDetailedPrivatePlanObserve _ candidates
                  context fuel table ((splitUniformImpl n).run cache)) =
                evalDist (runDirectDetailedPrivateObserve _ context fuel table
                  ((splitUniformImpl n).run cache))
              apply evalDist_fst_runDirectDetailedPrivatePlanObserve
              intro nextContext remaining value nextCandidates
              apply evalDist_fst_canonicalizeDirectDetailedPrivatePlanObserve
              intro finalContext finalRemaining finalValue finalCandidates
              exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2
          | inr input =>
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextCandidates := appendPlannedCandidate candidates plan.candidate?
              change evalDist (Prod.fst <$> runDirectDetailedPrivatePlanObserve _ nextCandidates
                  context fuel table ((probingHashQueryAfterPlan parameter input plan).run cache)) =
                evalDist (runDirectDetailedPrivateObserve _ context fuel table
                  ((probingHashQuery parameter input).run cache))
              calc
                _ = evalDist (runDirectDetailedPrivateObserve
                      (canonicalizeDirectDetailedPrivateObserve table
                        (fun nextContext remaining value =>
                          directDetailedBoundaryPrivateObserve
                            (maskedExpandedAdversaryImpl parameter root ftsSecret)
                            (next value.1) boolObserve nextContext remaining table value.2))
                      context fuel table
                      ((probingHashQueryAfterPlan parameter input plan).run cache)) := by
                    apply evalDist_fst_runDirectDetailedPrivatePlanObserve
                    intro nextContext remaining value finalCandidates
                    apply evalDist_fst_canonicalizeDirectDetailedPrivatePlanObserve
                    intro finalContext finalRemaining finalValue finalCandidates
                    exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2
                _ = _ := by
                  symm
                  apply evalDist_runDirectDetailedPrivateObserve_probingHashQuery_eq_afterPlan
                  cases hprobe : decodeProbe? parameter input with
                  | some candidate =>
                      cases hposition : decodePosition? parameter input with
                      | none =>
                          exact probingHashQuery_eq_plan_then_afterPlan_of_probe_some_nonleaf
                            parameter input candidate hprobe (by
                              rintro ⟨lay, tree, leafIdx, heq⟩
                              simp [hposition] at heq)
                      | some position =>
                          cases position with
                          | leaf lay tree leafIdx =>
                              exact probingHashQuery_eq_plan_then_afterPlan_leaf parameter input
                                candidate lay tree leafIdx hprobe hposition
                          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
                              exact probingHashQuery_eq_plan_then_afterPlan_of_probe_some_nonleaf
                                parameter input candidate hprobe (by
                                  rintro ⟨lay, tree, leafIdx, heq⟩
                                  simp [hposition] at heq)
                  | none =>
                      cases hposition : decodePosition? parameter input with
                      | none =>
                          exact probingHashQuery_eq_plan_then_afterPlan_of_probe_none_nonnode
                            parameter input hprobe (by
                              rintro ⟨lay, tree, level, nodeIdx, heq⟩
                              simp [hposition] at heq)
                      | some position =>
                          cases position with
                          | node lay tree level nodeIdx =>
                              exact probingHashQuery_eq_plan_then_afterPlan_node parameter input
                                lay tree level nodeIdx hprobe hposition
                          | chain | leaf | ftsLeaf | ftsNode | ftsRoots =>
                              exact probingHashQuery_eq_plan_then_afterPlan_of_probe_none_nonnode
                                parameter input hprobe (by
                                  rintro ⟨lay, tree, level, nodeIdx, heq⟩
                                  simp [hposition] at heq)
      | inr message =>
          change evalDist (Prod.fst <$> runDirectDetailedPrivatePlanObserve _ candidates
              context fuel table ((maskedSign parameter root ftsSecret message).run cache)) =
            evalDist (runDirectDetailedPrivateObserve _ context fuel table
              ((maskedSign parameter root ftsSecret message).run cache))
          apply evalDist_fst_runDirectDetailedPrivatePlanObserve
          intro nextContext remaining value nextCandidates
          apply evalDist_fst_canonicalizeDirectDetailedPrivatePlanObserve
          intro finalContext finalRemaining finalValue finalCandidates
          exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2

noncomputable def granularDetailedRetainedRestNormalizedPrivatePlanObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) :
    ProbComp (Bool × List Probe) :=
  directDetailedBoundaryNormalizedPrivatePlanObserve parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivatePlanObserve table value.1)
    candidates context fuel table value.2

theorem evalDist_fst_granularDetailedRetainedRestNormalizedPrivatePlanObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) :
    evalDist (Prod.fst <$> granularDetailedRetainedRestNormalizedPrivatePlanObserve
        adversary parameter table ftsSecret context fuel value candidates) =
      evalDist (granularDetailedRetainedRestPrivateObserve adversary parameter table ftsSecret
        context fuel value) := by
  unfold granularDetailedRetainedRestNormalizedPrivatePlanObserve
    granularDetailedRetainedRestPrivateObserve
  apply evalDist_fst_directDetailedBoundaryNormalizedPrivatePlanObserve
  intro nextContext remaining nextValue nextCandidates
  exact evalDist_fst_retainedResolvedFinalizationPrivatePlanObserve table value.1 nextContext
    remaining nextValue nextCandidates

noncomputable def granularAllDirectBoundaryNormalizedPrivatePlan
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Bool × List Probe) :=
  runDirectDetailedPrivatePlanObserve
    (granularDetailedRetainedRestNormalizedPrivatePlanObserve adversary parameter table ftsSecret)
    []
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

theorem evalDist_fst_granularAllDirectBoundaryNormalizedPrivatePlan
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (Prod.fst <$> granularAllDirectBoundaryNormalizedPrivatePlan
        adversary parameter table ftsSecret fuel) =
      evalDist (granularAllDirectBoundaryDetailedRetainedPrivate adversary parameter table
        ftsSecret fuel) := by
  unfold granularAllDirectBoundaryNormalizedPrivatePlan
    granularAllDirectBoundaryDetailedRetainedPrivate
  apply evalDist_fst_runDirectDetailedPrivatePlanObserve
  intro nextContext remaining value nextCandidates
  exact evalDist_fst_granularDetailedRetainedRestNormalizedPrivatePlanObserve adversary parameter
    table ftsSecret nextContext remaining value nextCandidates

noncomputable def sampledGranularAllDirectBoundaryNormalizedPrivatePlan
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Bool × List Probe) := do
  let table ← sampleOtsHashTable
  granularAllDirectBoundaryNormalizedPrivatePlan adversary parameter table ftsSecret fuel

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem evalDist_fst_sampledGranularAllDirectBoundaryNormalizedPrivatePlan
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (Prod.fst <$> sampledGranularAllDirectBoundaryNormalizedPrivatePlan
        adversary parameter ftsSecret fuel) =
      evalDist (sampledGranularAllDirectBoundaryDetailedRetainedPrivate adversary parameter
        ftsSecret fuel) := by
  unfold sampledGranularAllDirectBoundaryNormalizedPrivatePlan
    sampledGranularAllDirectBoundaryDetailedRetainedPrivate
  rw [map_bind]
  apply evalDist_bind_congr
  intro table _htable
  exact evalDist_fst_granularAllDirectBoundaryNormalizedPrivatePlan adversary parameter table
    ftsSecret fuel

end SphincsSecurity.Concrete.OtsProbeSimulation
