import SphincsSecurity.Proof.OtsProbeResolvedBoundaryWitnessDomination

/-!
# Root-aware materialized ordinary projection

The detailed materialized comparison is projected exactly to the Boolean ordinary-failure
observer used by its remaining probability bound.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

noncomputable def rootAwareMaterializedDetailedBoundaryOrdinaryObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) : ProbComp Bool := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      (DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool) →
      DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache →
        ProbComp Bool)
    (fun value observe context fuel _table cache => observe context fuel (value, cache))
    (fun query _next recursivelyRun observe context fuel table cache =>
      match query with
      | .inl (.inl n) =>
          runDirectDetailedOrdinaryObserve
            (classifyDirectDetailedOrdinaryObserve table
              (fun nextContext remaining value =>
                recursivelyRun value.1 observe nextContext remaining table value.2))
            context fuel table ((splitUniformImpl n).run cache)
      | .inl (.inr input) =>
          let publicContext := materializedCanonicalContext table context.state
          let plan := purePlanProbingHashQuery parameter input publicContext.state
          runDirectDetailedOrdinaryObserve
            (classifyDirectDetailedOrdinaryObserve table
              (fun nextContext remaining value =>
                recursivelyRun value.1 observe nextContext remaining table value.2))
            context fuel table
            ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state plan).run
              cache)
      | .inr message =>
          runDirectDetailedOrdinaryObserve
            (classifyDirectDetailedOrdinaryObserve table
              (fun nextContext remaining value =>
                recursivelyRun value.1 observe nextContext remaining table value.2))
            context fuel table ((maskedSign parameter root ftsSecret message).run cache))
    computation observe context fuel table cache

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_ordinary_rootAwareMaterializedDetailedBoundaryObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (detailedObserve : DeferredContext → Nat → (α × SplitHashCache) →
      ProbComp DirectBoundaryOutcome)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hproject : ∀ nextContext remaining value,
      evalDist (DirectBoundaryOutcome.ordinary <$>
          detailedObserve nextContext remaining value) =
        evalDist (observe nextContext remaining value)) :
    evalDist (DirectBoundaryOutcome.ordinary <$>
        rootAwareMaterializedDetailedBoundaryObserve parameter root ftsSecret computation
          detailedObserve context fuel table cache) =
      evalDist (rootAwareMaterializedDetailedBoundaryOrdinaryObserve parameter root ftsSecret
        computation observe context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      rw [rootAwareMaterializedDetailedBoundaryObserve, OracleComp.construct_pure,
        rootAwareMaterializedDetailedBoundaryOrdinaryObserve, OracleComp.construct_pure]
      exact hproject context fuel (value, cache)
  | query_bind query next ih =>
      rw [rootAwareMaterializedDetailedBoundaryObserve, OracleComp.construct_query_bind,
        rootAwareMaterializedDetailedBoundaryOrdinaryObserve, OracleComp.construct_query_bind]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              apply evalDist_ordinary_runDirectDetailedObserve
              intro result _hresult
              apply evalDist_ordinary_classifyDirectDetailedObserve
              exact ih result.value.1 result.context result.remaining result.value.2
          | inr input =>
              apply evalDist_ordinary_runDirectDetailedObserve
              intro result _hresult
              apply evalDist_ordinary_classifyDirectDetailedObserve
              exact ih result.value.1 result.context result.remaining result.value.2
      | inr message =>
          apply evalDist_ordinary_runDirectDetailedObserve
          intro result _hresult
          apply evalDist_ordinary_classifyDirectDetailedObserve
          exact ih result.value.1 result.context result.remaining result.value.2

noncomputable def rootAwareMaterializedDetailedRetainedRestOrdinaryObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp Bool :=
  rootAwareMaterializedDetailedBoundaryOrdinaryObserve parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationOrdinaryObserve table value.1)
    context fuel table value.2

set_option maxRecDepth 100000 in
theorem evalDist_ordinary_rootAwareMaterializedDetailedRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) :
    evalDist (DirectBoundaryOutcome.ordinary <$>
        rootAwareMaterializedDetailedRetainedRestObserve adversary parameter table ftsSecret
          context fuel value) =
      evalDist (rootAwareMaterializedDetailedRetainedRestOrdinaryObserve adversary parameter table
        ftsSecret context fuel value) := by
  unfold rootAwareMaterializedDetailedRetainedRestObserve
    rootAwareMaterializedDetailedRetainedRestOrdinaryObserve
  apply evalDist_ordinary_rootAwareMaterializedDetailedBoundaryObserve
  intro nextContext remaining nextValue
  unfold retainedResolvedFinalizationDetailedObserve
    retainedResolvedFinalizationOrdinaryObserve
  exact evalDist_ordinary_classifyDirectObserve table (resolvedFinalizationObserve table)
    nextContext remaining ((value.1, nextValue.1), nextValue.2)

noncomputable def rootAwareMaterializedBoundaryDetailedRetainedOrdinary
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool :=
  runDirectDetailedOrdinaryObserve
    (classifyDirectDetailedOrdinaryObserve table
      (rootAwareMaterializedDetailedRetainedRestOrdinaryObserve adversary parameter table
        ftsSecret))
    (directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
    (2 * fuel) table (maskedPublishedTreeRoot.run emptySplitHashCache)

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxRecDepth 100000 in
theorem evalDist_ordinary_rootAwareMaterializedBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.ordinary <$>
        rootAwareMaterializedBoundaryDetailedRetainedOutcome adversary parameter table
          ftsSecret fuel) =
      evalDist (rootAwareMaterializedBoundaryDetailedRetainedOrdinary adversary parameter table
        ftsSecret fuel) := by
  unfold rootAwareMaterializedBoundaryDetailedRetainedOutcome
    rootAwareMaterializedBoundaryDetailedRetainedOrdinary
  apply evalDist_ordinary_runDirectDetailedObserve
  intro result _hresult
  apply evalDist_ordinary_classifyDirectDetailedObserve
  exact evalDist_ordinary_rootAwareMaterializedDetailedRetainedRestObserve adversary parameter
    table ftsSecret result.context result.remaining result.value

noncomputable def sampledRootAwareMaterializedBoundaryDetailedRetainedOrdinary
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool := do
  let table ← sampleOtsHashTable
  rootAwareMaterializedBoundaryDetailedRetainedOrdinary adversary parameter table ftsSecret fuel

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem evalDist_ordinary_sampledRootAwareMaterializedBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.ordinary <$>
        sampledRootAwareMaterializedBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret fuel) =
      evalDist (sampledRootAwareMaterializedBoundaryDetailedRetainedOrdinary adversary parameter
        ftsSecret fuel) := by
  unfold sampledRootAwareMaterializedBoundaryDetailedRetainedOutcome
    sampledRootAwareMaterializedBoundaryDetailedRetainedOrdinary
  rw [map_bind]
  apply evalDist_bind_congr
  intro table _htable
  exact evalDist_ordinary_rootAwareMaterializedBoundaryDetailedRetainedOutcome adversary
    parameter table ftsSecret fuel

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem probEvent_ordinary_sampledRootAwareMaterializedBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun outcome => outcome.ordinary = true |
        sampledRootAwareMaterializedBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret fuel] =
      Pr[= true |
        sampledRootAwareMaterializedBoundaryDetailedRetainedOrdinary adversary parameter
          ftsSecret fuel] := by
  calc
    _ = Pr[= true | DirectBoundaryOutcome.ordinary <$>
        sampledRootAwareMaterializedBoundaryDetailedRetainedOutcome adversary parameter
          ftsSecret fuel] := by
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      rfl
    _ = _ := OracleComp.probOutput_congr rfl
      (evalDist_ordinary_sampledRootAwareMaterializedBoundaryDetailedRetainedOutcome adversary
        parameter ftsSecret fuel)

end SphincsSecurity.Concrete.OtsProbeSimulation
