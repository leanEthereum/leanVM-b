import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSample

/-!
# Materialized comparison probability

The observation log is proof-only. This file first erases it from the standalone materialized
comparison, leaving the clean state, value, table and remaining probe fuel unchanged.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

set_option linter.constructorNameAsVariable false

noncomputable def materializedCleanBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option (CleanRunResult (α × SplitHashCache))) := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      LazyRevealProbe.State Coordinate → Nat →
        (OtsSecretIndex → HashOutput) → SplitHashCache →
          ProbComp (Option (CleanRunResult (α × SplitHashCache))))
    (fun value state fuel table cache =>
      pure (some ⟨state, fuel, (value, cache), table⟩))
    (fun query _next recursivelyRun state fuel table cache =>
      match query with
      | .inl (.inl n) => do
          let result ← runCleanFromTable state fuel table ((splitUniformImpl n).run cache)
          match result with
          | none => pure none
          | some result =>
              recursivelyRun result.value.1 result.state result.remaining table result.value.2
      | .inl (.inr input) =>
          let publicContext := materializedCanonicalContext table state
          let plan := purePlanProbingHashQuery parameter input publicContext.state
          do
            let result ← runCleanFromTable state fuel table
              ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state plan).run
                cache)
            match result with
            | none => pure none
            | some result =>
                recursivelyRun result.value.1 result.state result.remaining table result.value.2
      | .inr message => do
          let result ← runCleanFromTable state fuel table
            ((maskedSign parameter root ftsSecret message).run cache)
          match result with
          | none => pure none
          | some result =>
              recursivelyRun result.value.1 result.state result.remaining table result.value.2)
    computation state fuel table cache

set_option maxRecDepth 100000 in
theorem map_projectObservedCleanRun_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    projectObservedCleanRun <$>
        observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
          table cache =
      materializedCleanBoundary parameter root ftsSecret computation state fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing observations state fuel cache with
  | pure value =>
      simp [observedMaterializedBoundary, materializedCleanBoundary, projectObservedCleanRun,
        ObservedCleanRunResult.toClean]
  | query_bind query next ih =>
      rw [observedMaterializedBoundary, OracleComp.construct_query_bind,
        materializedCleanBoundary, OracleComp.construct_query_bind]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [map_bind]
              calc
                _ = runObservedCleanFromTable observations state fuel table
                      ((splitUniformImpl n).run cache) >>= fun result =>
                    projectObservedCleanRun <$> match result with
                      | none => pure none
                      | some result =>
                          observedMaterializedBoundary parameter root ftsSecret
                            (next result.value.1) result.observations result.state
                            result.remaining table result.value.2 := by rfl
                _ = runObservedCleanFromTable observations state fuel table
                      ((splitUniformImpl n).run cache) >>= fun result =>
                    match result with
                    | none => pure none
                    | some result =>
                        materializedCleanBoundary parameter root ftsSecret
                          (next result.value.1) result.state result.remaining table
                          result.value.2 := by
                    apply bind_congr
                    intro result
                    cases result with
                    | none => simp [projectObservedCleanRun]
                    | some result =>
                        simpa using (ih result.value.1 result.observations result.state
                          result.remaining result.value.2)
                _ = (projectObservedCleanRun <$>
                      runObservedCleanFromTable observations state fuel table
                        ((splitUniformImpl n).run cache)) >>= fun result =>
                    match result with
                    | none => pure none
                    | some result =>
                        materializedCleanBoundary parameter root ftsSecret
                          (next result.value.1) result.state result.remaining table
                          result.value.2 := by
                    rw [map_eq_bind_pure_comp, bind_assoc]
                    apply bind_congr
                    intro result
                    cases result <;> rfl
                _ = _ := by
                    rw [map_projectObservedCleanRun_runObservedCleanFromTable]
                    rfl
          | inr input =>
              let publicContext := materializedCanonicalContext table state
              let plan := purePlanProbingHashQuery parameter input publicContext.state
              rw [map_bind]
              calc
                _ = runObservedCleanFromTable observations state fuel table
                      ((probingHashQueryAfterRootAwarePublicPlan parameter input
                        publicContext.state plan).run cache) >>= fun result =>
                    projectObservedCleanRun <$> match result with
                      | none => pure none
                      | some result =>
                          observedMaterializedBoundary parameter root ftsSecret
                            (next result.value.1) result.observations result.state
                            result.remaining table result.value.2 := by rfl
                _ = runObservedCleanFromTable observations state fuel table
                      ((probingHashQueryAfterRootAwarePublicPlan parameter input
                        publicContext.state plan).run cache) >>= fun result =>
                    match result with
                    | none => pure none
                    | some result =>
                        materializedCleanBoundary parameter root ftsSecret
                          (next result.value.1) result.state result.remaining table
                          result.value.2 := by
                    apply bind_congr
                    intro result
                    cases result with
                    | none => simp [projectObservedCleanRun]
                    | some result =>
                        simpa using (ih result.value.1 result.observations result.state
                          result.remaining result.value.2)
                _ = (projectObservedCleanRun <$>
                      runObservedCleanFromTable observations state fuel table
                        ((probingHashQueryAfterRootAwarePublicPlan parameter input
                          publicContext.state plan).run cache)) >>= fun result =>
                    match result with
                    | none => pure none
                    | some result =>
                        materializedCleanBoundary parameter root ftsSecret
                          (next result.value.1) result.state result.remaining table
                          result.value.2 := by
                    rw [map_eq_bind_pure_comp, bind_assoc]
                    apply bind_congr
                    intro result
                    cases result <;> rfl
                _ = _ := by
                    rw [map_projectObservedCleanRun_runObservedCleanFromTable]
                    rfl
      | inr message =>
          rw [map_bind]
          calc
            _ = runObservedCleanFromTable observations state fuel table
                  ((maskedSign parameter root ftsSecret message).run cache) >>= fun result =>
                projectObservedCleanRun <$> match result with
                  | none => pure none
                  | some result =>
                      observedMaterializedBoundary parameter root ftsSecret
                        (next result.value.1) result.observations result.state result.remaining
                        table result.value.2 := by rfl
            _ = runObservedCleanFromTable observations state fuel table
                  ((maskedSign parameter root ftsSecret message).run cache) >>= fun result =>
                match result with
                | none => pure none
                | some result =>
                    materializedCleanBoundary parameter root ftsSecret
                      (next result.value.1) result.state result.remaining table result.value.2 := by
                apply bind_congr
                intro result
                cases result with
                | none => simp [projectObservedCleanRun]
                | some result =>
                    simpa using (ih result.value.1 result.observations result.state
                      result.remaining result.value.2)
            _ = (projectObservedCleanRun <$>
                  runObservedCleanFromTable observations state fuel table
                    ((maskedSign parameter root ftsSecret message).run cache)) >>= fun result =>
                match result with
                | none => pure none
                | some result =>
                    materializedCleanBoundary parameter root ftsSecret
                      (next result.value.1) result.state result.remaining table result.value.2 := by
                rw [map_eq_bind_pure_comp, bind_assoc]
                apply bind_congr
                intro result
                cases result <;> rfl
            _ = _ := by
                rw [map_projectObservedCleanRun_runObservedCleanFromTable]
                rfl

noncomputable def materializedCleanRetainedRunFromTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (Option (CleanRunResult (RetainedGameResult × SplitHashCache))) := do
  let rootResult ← runCleanFromTable LazyRevealProbe.State.empty fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure none
  | some rootResult => do
      let restResult ← materializedCleanBoundary parameter rootResult.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩)
        rootResult.state rootResult.remaining table rootResult.value.2
      match restResult with
      | none => pure none
      | some restResult =>
          pure (some
            { restResult with
              value := ((rootResult.value.1, restResult.value.1), restResult.value.2) })

noncomputable def finishMaterializedCleanRunFromTable
    (table : OtsSecretIndex → HashOutput)
    (result : Option (CleanRunResult α)) :
    ProbComp (Option (CleanRunResult α)) := by
  classical
  exact match result with
  | none => pure none
  | some result =>
      if DeferredCompletable table (directDeferredContext result.state) then
        finishCleanRunFromTable (some result)
      else
        pure none

noncomputable def sampledMaterializedClean
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Option (CleanRunResult (RetainedGameResult × SplitHashCache))) := do
  let table ← sampleOtsHashTable
  let result ← materializedCleanRetainedRunFromTable adversary parameter ftsSecret fuel table
  finishMaterializedCleanRunFromTable table result

attribute [local irreducible] observedMaterializedRetainedRunFromTable in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem map_projectObservedCleanRun_observedMaterializedRetainedRunFromTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    projectObservedCleanRun <$>
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table =
      materializedCleanRetainedRunFromTable adversary parameter ftsSecret fuel table := by
  rw [observedMaterializedRetainedRunFromTable, materializedCleanRetainedRunFromTable, map_bind]
  calc
    _ = (runObservedCleanFromTable [] LazyRevealProbe.State.empty fuel table
          (maskedPublishedTreeRoot.run emptySplitHashCache) >>= fun rootResult =>
        match rootResult with
        | none => pure none
        | some rootResult => do
            let restResult ← materializedCleanBoundary parameter rootResult.value.1 ftsSecret
              (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩)
              rootResult.state rootResult.remaining table rootResult.value.2
            match restResult with
            | none => pure none
            | some restResult => pure (some
                { restResult with
                  value := ((rootResult.value.1, restResult.value.1), restResult.value.2) })) := by
        apply bind_congr
        intro rootResult
        cases rootResult with
        | none => simp [projectObservedCleanRun]
        | some rootResult =>
            simp only
            rw [map_bind]
            calc
              _ = observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
                    (retainedGameRestComputation adversary
                      ⟨rootResult.value.1, parameter⟩)
                    rootResult.observations rootResult.state rootResult.remaining table
                    rootResult.value.2 >>= fun restResult =>
                  match restResult with
                  | none => pure none
                  | some restResult => pure (some
                      { restResult.toClean with
                        value := ((rootResult.value.1, restResult.value.1),
                          restResult.value.2) }) := by
                  apply bind_congr
                  intro restResult
                  cases restResult <;>
                    simp [projectObservedCleanRun, ObservedCleanRunResult.toClean]
              _ = (projectObservedCleanRun <$>
                    observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
                      (retainedGameRestComputation adversary
                        ⟨rootResult.value.1, parameter⟩)
                      rootResult.observations rootResult.state rootResult.remaining table
                      rootResult.value.2) >>= fun restResult =>
                  match restResult with
                  | none => pure none
                  | some restResult => pure (some
                      { restResult with
                        value := ((rootResult.value.1, restResult.value.1),
                          restResult.value.2) }) := by
                  rw [map_eq_bind_pure_comp, bind_assoc]
                  apply bind_congr
                  intro restResult
                  cases restResult <;> rfl
              _ = materializedCleanBoundary parameter rootResult.value.1 ftsSecret
                    (retainedGameRestComputation adversary
                      ⟨rootResult.value.1, parameter⟩)
                    rootResult.state rootResult.remaining table rootResult.value.2 >>=
                  fun restResult =>
                    match restResult with
                    | none => pure none
                    | some restResult => pure (some
                        { restResult with
                          value := ((rootResult.value.1, restResult.value.1),
                            restResult.value.2) }) := by
                  rw [map_projectObservedCleanRun_observedMaterializedBoundary]
              _ = _ := by rfl
    _ = ((projectObservedCleanRun <$>
          runObservedCleanFromTable [] LazyRevealProbe.State.empty fuel table
            (maskedPublishedTreeRoot.run emptySplitHashCache)) >>= fun rootResult =>
        match rootResult with
        | none => pure none
        | some rootResult => do
            let restResult ← materializedCleanBoundary parameter rootResult.value.1 ftsSecret
              (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩)
              rootResult.state rootResult.remaining table rootResult.value.2
            match restResult with
            | none => pure none
            | some restResult => pure (some
                { restResult with
                  value := ((rootResult.value.1, restResult.value.1), restResult.value.2) })) := by
        rw [map_eq_bind_pure_comp, bind_assoc]
        apply bind_congr
        intro rootResult
        cases rootResult <;> rfl
    _ = _ := by rw [map_projectObservedCleanRun_runObservedCleanFromTable]

theorem map_projectObservedCleanRun_finishObservedMaterializedCleanRunFromTable
    (table : OtsSecretIndex → HashOutput)
    (result : Option (ObservedCleanRunResult α)) :
    projectObservedCleanRun <$>
        finishObservedMaterializedCleanRunFromTable table result =
      finishMaterializedCleanRunFromTable table (projectObservedCleanRun result) := by
  classical
  cases result with
  | none =>
      simp [finishObservedMaterializedCleanRunFromTable,
        finishMaterializedCleanRunFromTable, projectObservedCleanRun]
  | some result =>
      unfold finishObservedMaterializedCleanRunFromTable
        finishMaterializedCleanRunFromTable
      change projectObservedCleanRun <$>
          (if DeferredCompletable table (directDeferredContext result.state) then
            finishObservedCleanRunFromTable (some result)
          else pure none) =
        if DeferredCompletable table (directDeferredContext result.state) then
          finishCleanRunFromTable (some result.toClean)
        else pure none
      by_cases hcompletable :
          DeferredCompletable table (directDeferredContext result.state)
      · simp only [hcompletable, ↓reduceIte]
        simpa [projectObservedCleanRun] using
          (map_projectObservedCleanRun_finishObservedCleanRunFromTable (some result))
      · simp [hcompletable, projectObservedCleanRun]

set_option maxRecDepth 100000 in
theorem map_projectObservedCleanRun_sampledObservedMaterializedClean
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    projectObservedCleanRun <$>
        sampledObservedMaterializedClean adversary parameter ftsSecret fuel =
      sampledMaterializedClean adversary parameter ftsSecret fuel := by
  unfold sampledObservedMaterializedClean sampledMaterializedClean
  rw [map_bind]
  apply bind_congr
  intro table
  rw [map_bind]
  calc
    _ = observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table >>=
        fun result => finishMaterializedCleanRunFromTable table
          (projectObservedCleanRun result) := by
      apply bind_congr
      intro result
      exact map_projectObservedCleanRun_finishObservedMaterializedCleanRunFromTable table result
    _ = (projectObservedCleanRun <$>
          observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table) >>=
        finishMaterializedCleanRunFromTable table := by
      rw [map_eq_bind_pure_comp, bind_assoc]
      apply bind_congr
      intro result
      rfl
    _ = _ := by
      rw [map_projectObservedCleanRun_observedMaterializedRetainedRunFromTable]

theorem probEvent_sampledObservedMaterializedClean_none_eq_clean
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[= none | sampledObservedMaterializedClean adversary parameter ftsSecret fuel] =
      Pr[= none | sampledMaterializedClean adversary parameter ftsSecret fuel] := by
  calc
    _ = Pr[= none | projectObservedCleanRun <$>
        sampledObservedMaterializedClean adversary parameter ftsSecret fuel] := by
      rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map]
      apply OracleComp.probEvent_congr'
      · intro result _hresult
        cases result <;> simp [projectObservedCleanRun]
      · rfl
    _ = _ := OracleComp.probOutput_congr rfl
      (congrArg evalDist
        (map_projectObservedCleanRun_sampledObservedMaterializedClean adversary parameter
          ftsSecret fuel))

end SphincsSecurity.Concrete.OtsProbeSimulation
