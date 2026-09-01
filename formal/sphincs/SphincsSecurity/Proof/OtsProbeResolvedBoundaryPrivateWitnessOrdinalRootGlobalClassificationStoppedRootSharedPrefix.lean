import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootEager

/-!
# Shared observed and root-selection prefix

The observed materialized execution and the failure-retaining root-selection outcome execute the
same prefix. This module runs that prefix once. When selection or failure becomes determined, it
freezes the outcome and lets only the observed execution finish. The two projections are therefore
the original observed run and the original materialized outcome, while their joint support retains
the correlation needed to exclude a conservative failure on a successful observed run.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable

private theorem spmf_bind_const_of_no_failure_local
    {p : SPMF α} (hp : Pr[⊥ | p] = 0) (q : SPMF β) :
    (p >>= fun _ => q) = q := by
  apply SPMF.ext
  intro value
  change Pr[= value | p >>= fun _ => q] = Pr[= value | q]
  rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right, tsum_probOutput_eq_sub, hp,
    tsub_zero, one_mul]

private theorem map_bind_of_map_eq
    (p : ProbComp α) (f : α → ProbComp β) (project : β → γ)
    (observe : α → δ) (q : ProbComp δ) (g : δ → ProbComp γ)
    (hp : observe <$> p = q)
    (hf : ∀ value, project <$> f value = g (observe value)) :
    project <$> (p >>= f) = q >>= g := by
  rw [map_bind, ← hp, bind_map_left]
  apply bind_congr
  exact hf

private theorem evalDist_map_bind_congr
    (p : ProbComp α) (f : α → ProbComp β) (project : β → γ)
    (g : α → ProbComp γ)
    (hf : ∀ value, evalDist (project <$> f value) = evalDist (g value)) :
    evalDist (project <$> (p >>= f)) = evalDist (p >>= g) := by
  rw [map_bind, evalDist_bind, evalDist_bind]
  apply bind_congr
  exact hf

def observedResultOfDetailed
    (observations : List CleanProbeObservation) :
    DirectDetailedResult (α × SplitHashCache) →
      Option (ObservedCleanRunResult (α × SplitHashCache)) :=
  projectDirectDetailedObserved observations

theorem map_observedResultOfDetailed_run_eq_observed_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate)
      (α × SplitHashCache))
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hprobeFree : computation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0) :
    observedResultOfDetailed observations <$>
        runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table computation =
      runObservedCleanFromTable observations state fuel table computation := by
  unfold observedResultOfDetailed
  calc
    _ = attachCleanProbeObservations observations <$>
        (projectDirectDetailedClean <$>
          runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
            computation) := by
      rw [Functor.map_map]
      apply map_congr
      intro result
      exact projectDirectDetailedObserved_eq_attach observations result
    _ = attachCleanProbeObservations observations <$>
        runCleanFromTable state fuel table computation := by
      rw [map_projectDirectDetailedClean_run_eq_clean]
    _ = _ := map_attachCleanProbeObservations_runCleanFromTable_of_probeFree computation
      observations state fuel table hprobeFree

noncomputable def finishObservedWithSelectionOutcome
    (parameter : PublicParameter) (publicRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (outcome : MaterializedSelectionOutcome) :
    ProbComp
      (Option (ObservedCleanRunResult (α × SplitHashCache)) ×
        MaterializedSelectionOutcome) := do
  let observed ← observedMaterializedBoundary parameter publicRoot ftsSecret computation
    observations state fuel table cache
  pure (observed, outcome)

theorem map_fst_finishObservedWithSelectionOutcome
    (parameter : PublicParameter) (publicRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (outcome : MaterializedSelectionOutcome) :
    Prod.fst <$> finishObservedWithSelectionOutcome parameter publicRoot ftsSecret computation
        observations state fuel table cache outcome =
      observedMaterializedBoundary parameter publicRoot ftsSecret computation observations state
        fuel table cache := by
  simp [finishObservedWithSelectionOutcome, map_eq_bind_pure_comp, bind_assoc]

theorem map_snd_finishObservedWithSelectionOutcome
    (parameter : PublicParameter) (publicRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (outcome : MaterializedSelectionOutcome) :
    evalDist (Prod.snd <$> finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
        computation observations state fuel table cache outcome) =
      evalDist (pure outcome : ProbComp MaterializedSelectionOutcome) := by
  simp only [finishObservedWithSelectionOutcome, map_bind, map_pure]
  rw [evalDist_bind]
  exact spmf_bind_const_of_no_failure_local
    (p := evalDist (observedMaterializedBoundary parameter publicRoot ftsSecret computation
      observations state fuel table cache))
    (probFailure_eq_zero (mx := observedMaterializedBoundary parameter publicRoot ftsSecret
      computation observations state fuel table cache))
    (evalDist (pure outcome : ProbComp MaterializedSelectionOutcome))

noncomputable def continueObservedRootSelectionSharedPrefix
    (parameter : PublicParameter) (publicRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (next : α → OracleComp (OracleWorld + SigningSpec) β)
    (observations : List CleanProbeObservation) (candidates : List Probe)
    (table : OtsSecretIndex → HashOutput)
    (recursivelyRun : α → List CleanProbeObservation → List Probe →
      LazyRevealProbe.State Coordinate → Nat → (OtsSecretIndex → HashOutput) →
        SplitHashCache →
          ProbComp
            (Option (ObservedCleanRunResult (β × SplitHashCache)) ×
              MaterializedSelectionOutcome)) :
    DirectDetailedResult (α × SplitHashCache) →
      ProbComp
        (Option (ObservedCleanRunResult (β × SplitHashCache)) ×
          MaterializedSelectionOutcome) := by
  classical
  exact fun detailed => match detailed with
  | .stopped _ => pure (none, .failed)
  | .done result =>
      if DeferredCompletable table (directDeferredContext result.context.state) then
        if Coordinate.position target ∈ result.context.state.revealed then
          finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
            (next result.value.1) observations result.context.state result.remaining table
            result.value.2 .failed
        else
          recursivelyRun result.value.1 observations candidates result.context.state
            result.remaining table result.value.2
      else
        finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
          (next result.value.1) observations result.context.state result.remaining table
          result.value.2 .failed

theorem map_fst_continueObservedRootSelectionSharedPrefix
    (parameter : PublicParameter) (publicRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (next : α → OracleComp (OracleWorld + SigningSpec) β)
    (observations : List CleanProbeObservation) (candidates : List Probe)
    (table : OtsSecretIndex → HashOutput)
    (recursivelyRun : α → List CleanProbeObservation → List Probe →
      LazyRevealProbe.State Coordinate → Nat → (OtsSecretIndex → HashOutput) →
        SplitHashCache →
          ProbComp
            (Option (ObservedCleanRunResult (β × SplitHashCache)) ×
              MaterializedSelectionOutcome))
    (hrecursive : ∀ value state fuel cache,
      Prod.fst <$> recursivelyRun value observations candidates state fuel table cache =
        observedMaterializedBoundary parameter publicRoot ftsSecret (next value) observations
          state fuel table cache)
    (detailed : DirectDetailedResult (α × SplitHashCache)) :
    Prod.fst <$> continueObservedRootSelectionSharedPrefix parameter publicRoot ftsSecret target
        next observations candidates table recursivelyRun detailed =
      match observedResultOfDetailed observations detailed with
      | none => pure none
      | some result =>
          observedMaterializedBoundary parameter publicRoot ftsSecret (next result.value.1)
            result.observations result.state result.remaining table result.value.2 := by
  cases detailed with
  | stopped reason => rfl
  | done result =>
      unfold continueObservedRootSelectionSharedPrefix observedResultOfDetailed
        projectDirectDetailedObserved
      by_cases hcompletable :
          DeferredCompletable table (directDeferredContext result.context.state)
      · simp only [hcompletable, ↓reduceIte]
        by_cases hrevealed : Coordinate.position target ∈ result.context.state.revealed
        · simp only [hrevealed, ↓reduceIte]
          exact map_fst_finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
            (next result.value.1) observations result.context.state result.remaining table
            result.value.2 .failed
        · simp only [hrevealed, ↓reduceIte]
          exact hrecursive result.value.1 result.context.state result.remaining result.value.2
      · simp only [hcompletable, ↓reduceIte]
        exact map_fst_finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
          (next result.value.1) observations result.context.state result.remaining table
          result.value.2 .failed

theorem evalDist_map_snd_continueObservedRootSelectionSharedPrefix
    (parameter : PublicParameter) (publicRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (next : α → OracleComp (OracleWorld + SigningSpec) β)
    (observations : List CleanProbeObservation) (candidates : List Probe)
    (table : OtsSecretIndex → HashOutput)
    (recursivelyRun : α → List CleanProbeObservation → List Probe →
      LazyRevealProbe.State Coordinate → Nat → (OtsSecretIndex → HashOutput) →
        SplitHashCache →
          ProbComp
            (Option (ObservedCleanRunResult (β × SplitHashCache)) ×
              MaterializedSelectionOutcome))
    (outcomeObserve : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp MaterializedSelectionOutcome)
    (hrecursive : ∀ value state fuel cache,
      evalDist (Prod.snd <$>
          recursivelyRun value observations candidates state fuel table cache) =
        evalDist (outcomeObserve state fuel value cache candidates))
    (detailed : DirectDetailedResult (α × SplitHashCache)) :
    evalDist (Prod.snd <$>
        continueObservedRootSelectionSharedPrefix parameter publicRoot ftsSecret target next
          observations candidates table recursivelyRun detailed) =
      evalDist
        (finishMaterializedSelectionOutcome target table outcomeObserve candidates detailed) := by
  cases detailed with
  | stopped reason => simp [continueObservedRootSelectionSharedPrefix,
      finishMaterializedSelectionOutcome]
  | done result =>
      unfold continueObservedRootSelectionSharedPrefix finishMaterializedSelectionOutcome
      by_cases hcompletable :
          DeferredCompletable table (directDeferredContext result.context.state)
      · simp only [hcompletable, ↓reduceIte]
        by_cases hrevealed : Coordinate.position target ∈ result.context.state.revealed
        · simp only [hrevealed, ↓reduceIte]
          exact map_snd_finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
            (next result.value.1) observations result.context.state result.remaining table
            result.value.2 .failed
        · simp only [hrevealed, ↓reduceIte]
          exact hrecursive result.value.1 result.context.state result.remaining result.value.2
      · simp only [hcompletable, ↓reduceIte]
        exact map_snd_finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
          (next result.value.1) observations result.context.state result.remaining table
          result.value.2 .failed

noncomputable def materializedActualRootAwareOrdinalSelectionOutcome
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp MaterializedSelectionOutcome := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List Probe → LazyRevealProbe.State Coordinate → Nat →
        (OtsSecretIndex → HashOutput) → SplitHashCache →
          ProbComp MaterializedSelectionOutcome)
    (fun _value candidates _state _fuel _table _cache =>
      if hselected : ordinal < candidates.length then
        pure (.finished (some (candidates.get ⟨ordinal, hselected⟩)))
      else pure (.finished none))
    (fun query next recursivelyRun candidates state fuel table cache =>
      if hselected : ordinal < candidates.length then
        pure (.finished (some (candidates.get ⟨ordinal, hselected⟩)))
      else
        match query with
        | .inl (.inl n) =>
            runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
                ((splitUniformImpl n).run cache) >>=
              finishMaterializedSelectionOutcome target table
                (fun nextState remaining value nextCache laterCandidates =>
                  recursivelyRun value laterCandidates nextState remaining table nextCache)
                candidates
        | .inl (.inr input) =>
            let publicContext := materializedCanonicalContext table state
            let plan := purePlanProbingHashQuery parameter input publicContext.state
            let candidate? := rootAwareCandidateForPlan? parameter input plan
            let nextCandidates := appendPlannedCandidate candidates candidate?
            if hnextSelected : ordinal < nextCandidates.length then
              pure (.finished (some (nextCandidates.get ⟨ordinal, hnextSelected⟩)))
            else if RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate? then
              runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
                  ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                    plan).run cache) >>=
                finishMaterializedSelectionOutcome target table
                  (fun nextState remaining value nextCache laterCandidates =>
                    recursivelyRun value laterCandidates nextState remaining table nextCache)
                  nextCandidates
            else pure (.finished none)
        | .inr message =>
            runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
                ((maskedSign parameter publicRoot ftsSecret message).run cache) >>=
              finishMaterializedSelectionOutcome target table
                (fun nextState remaining value nextCache laterCandidates =>
                  recursivelyRun value laterCandidates nextState remaining table nextCache)
                candidates)
    computation candidates state fuel table cache

theorem materializedActualRootAwareOrdinalSelectionOutcome_uniform_query_bind
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (n : Nat)
    (next : Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    materializedActualRootAwareOrdinalSelectionOutcome ordinal parameter publicRoot target leftRoot
        rightRoot ftsSecret
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inl n))) >>= next) candidates state fuel table cache =
      if hselected : ordinal < candidates.length then
        pure (.finished (some (candidates.get ⟨ordinal, hselected⟩)))
      else
        runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
            ((splitUniformImpl n).run cache) >>=
          finishMaterializedSelectionOutcome target table
            (fun nextState remaining value nextCache laterCandidates =>
              materializedActualRootAwareOrdinalSelectionOutcome ordinal parameter publicRoot
                target leftRoot rightRoot ftsSecret (next value) laterCandidates nextState
                remaining table nextCache)
            candidates := by
  rw [materializedActualRootAwareOrdinalSelectionOutcome,
    OracleComp.construct_query_bind]
  unfold materializedActualRootAwareOrdinalSelectionOutcome
  rfl

theorem materializedActualRootAwareOrdinalSelectionOutcome_hash_query_bind
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    materializedActualRootAwareOrdinalSelectionOutcome ordinal parameter publicRoot target leftRoot
        rightRoot ftsSecret
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next) candidates state fuel table cache =
      if hselected : ordinal < candidates.length then
        pure (.finished (some (candidates.get ⟨ordinal, hselected⟩)))
      else
        let publicContext := materializedCanonicalContext table state
        let plan := purePlanProbingHashQuery parameter input publicContext.state
        let candidate? := rootAwareCandidateForPlan? parameter input plan
        let nextCandidates := appendPlannedCandidate candidates candidate?
        if hnextSelected : ordinal < nextCandidates.length then
          pure (.finished (some (nextCandidates.get ⟨ordinal, hnextSelected⟩)))
        else if RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate? then
          runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
              ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                plan).run cache) >>=
            finishMaterializedSelectionOutcome target table
              (fun nextState remaining value nextCache laterCandidates =>
                materializedActualRootAwareOrdinalSelectionOutcome ordinal parameter publicRoot
                  target leftRoot rightRoot ftsSecret (next value) laterCandidates nextState
                  remaining table nextCache)
              nextCandidates
        else pure (.finished none) := by
  rw [materializedActualRootAwareOrdinalSelectionOutcome,
    OracleComp.construct_query_bind]
  unfold materializedActualRootAwareOrdinalSelectionOutcome
  rfl

theorem materializedActualRootAwareOrdinalSelectionOutcome_sign_query_bind
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : SignRequest)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    materializedActualRootAwareOrdinalSelectionOutcome ordinal parameter publicRoot target leftRoot
        rightRoot ftsSecret
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (Sum.inr message)) >>= next)
        candidates state fuel table cache =
      if hselected : ordinal < candidates.length then
        pure (.finished (some (candidates.get ⟨ordinal, hselected⟩)))
      else
        runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
            ((maskedSign parameter publicRoot ftsSecret message).run cache) >>=
          finishMaterializedSelectionOutcome target table
            (fun nextState remaining value nextCache laterCandidates =>
              materializedActualRootAwareOrdinalSelectionOutcome ordinal parameter publicRoot
                target leftRoot rightRoot ftsSecret (next value) laterCandidates nextState
                remaining table nextCache)
            candidates := by
  rw [materializedActualRootAwareOrdinalSelectionOutcome,
    OracleComp.construct_query_bind]
  unfold materializedActualRootAwareOrdinalSelectionOutcome
  rfl

noncomputable def observedRootSelectionSharedPrefix
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation) (candidates : List Probe)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp
      (Option (ObservedCleanRunResult (α × SplitHashCache)) ×
        MaterializedSelectionOutcome) := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List CleanProbeObservation → List Probe → LazyRevealProbe.State Coordinate → Nat →
        (OtsSecretIndex → HashOutput) → SplitHashCache →
          ProbComp
            (Option (ObservedCleanRunResult (α × SplitHashCache)) ×
              MaterializedSelectionOutcome))
    (fun value observations candidates state fuel table cache =>
      let observed : ObservedCleanRunResult (α × SplitHashCache) :=
        ⟨state, fuel, (value, cache), table, observations⟩
      if hselected : ordinal < candidates.length then
        pure (some observed, .finished (some (candidates.get ⟨ordinal, hselected⟩)))
      else pure (some observed, .finished none))
    (fun query next recursivelyRun observations candidates state fuel table cache =>
      if hselected : ordinal < candidates.length then
        finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
          (liftM (OracleSpec.query query) >>= next) observations state fuel table cache
          (.finished (some (candidates.get ⟨ordinal, hselected⟩)))
      else
        match query with
        | .inl (.inl n) => do
            let detailed ← runDirectResolvedDetailedFromTable (directDeferredContext state) fuel
              table ((splitUniformImpl n).run cache)
            continueObservedRootSelectionSharedPrefix parameter publicRoot ftsSecret target next
              observations candidates table recursivelyRun detailed
        | .inl (.inr input) =>
            let publicContext := materializedCanonicalContext table state
            let plan := purePlanProbingHashQuery parameter input publicContext.state
            let candidate? := rootAwareCandidateForPlan? parameter input plan
            let nextCandidates := appendPlannedCandidate candidates candidate?
            let nextObservations := observationsAfterCandidate observations state candidate?
            if hnextSelected : ordinal < nextCandidates.length then
              finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
                (liftM (OracleSpec.query (Sum.inl (Sum.inr input))) >>= next) observations state fuel
                table cache
                (.finished (some (nextCandidates.get ⟨ordinal, hnextSelected⟩)))
            else if RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate? then do
              let detailed ← runDirectResolvedDetailedFromTable (directDeferredContext state) fuel
                table
                ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state plan).run
                  cache)
              continueObservedRootSelectionSharedPrefix parameter publicRoot ftsSecret target next
                nextObservations nextCandidates table recursivelyRun detailed
            else
              finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
                (liftM (OracleSpec.query (Sum.inl (Sum.inr input))) >>= next) observations state fuel
                table cache (.finished none)
        | .inr message => do
            let detailed ← runDirectResolvedDetailedFromTable (directDeferredContext state) fuel
              table ((maskedSign parameter publicRoot ftsSecret message).run cache)
            continueObservedRootSelectionSharedPrefix parameter publicRoot ftsSecret target next
              observations candidates table recursivelyRun detailed)
    computation observations candidates state fuel table cache

theorem observedRootSelectionSharedPrefix_query_bind
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range query →
      OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation) (candidates : List Probe)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    observedRootSelectionSharedPrefix ordinal parameter publicRoot target leftRoot rightRoot
        ftsSecret (liftM (OracleSpec.query query) >>= next) observations candidates state fuel table
        cache = (if hselected : ordinal < candidates.length then
        finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
          (liftM (OracleSpec.query query) >>= next) observations state fuel table cache
          (.finished (some (candidates.get ⟨ordinal, hselected⟩)))
      else
        match query with
        | .inl (.inl n) => do
            let detailed ← runDirectResolvedDetailedFromTable (directDeferredContext state) fuel
              table ((splitUniformImpl n).run cache)
            continueObservedRootSelectionSharedPrefix parameter publicRoot ftsSecret target next
              observations candidates table
              (fun value =>
                observedRootSelectionSharedPrefix ordinal parameter publicRoot target leftRoot
                  rightRoot ftsSecret (next value))
              detailed
        | .inl (.inr input) =>
            let publicContext := materializedCanonicalContext table state
            let plan := purePlanProbingHashQuery parameter input publicContext.state
            let candidate? := rootAwareCandidateForPlan? parameter input plan
            let nextCandidates := appendPlannedCandidate candidates candidate?
            let nextObservations := observationsAfterCandidate observations state candidate?
            if hnextSelected : ordinal < nextCandidates.length then
              finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
                (liftM (OracleSpec.query (Sum.inl (Sum.inr input))) >>= next) observations state fuel
                table cache
                (.finished (some (nextCandidates.get ⟨ordinal, hnextSelected⟩)))
            else if RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate? then do
              let detailed ← runDirectResolvedDetailedFromTable (directDeferredContext state) fuel
                table
                ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                  plan).run cache)
              continueObservedRootSelectionSharedPrefix parameter publicRoot ftsSecret target next
                nextObservations nextCandidates table
                (fun value =>
                  observedRootSelectionSharedPrefix ordinal parameter publicRoot target leftRoot
                    rightRoot ftsSecret (next value))
                detailed
            else
              finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
                (liftM (OracleSpec.query (Sum.inl (Sum.inr input))) >>= next) observations state fuel
                table cache (.finished none)
        | .inr message => do
            let detailed ← runDirectResolvedDetailedFromTable (directDeferredContext state) fuel
              table ((maskedSign parameter publicRoot ftsSecret message).run cache)
            continueObservedRootSelectionSharedPrefix parameter publicRoot ftsSecret target next
              observations candidates table
              (fun value =>
                observedRootSelectionSharedPrefix ordinal parameter publicRoot target leftRoot
                  rightRoot ftsSecret (next value))
              detailed) := by
  rw [observedRootSelectionSharedPrefix, OracleComp.construct_query_bind]
  unfold observedRootSelectionSharedPrefix
  cases query with
  | inl worldQuery => cases worldQuery <;> rfl
  | inr message => rfl

theorem observedMaterializedBoundary_uniform_query_bind
    (parameter : PublicParameter) (publicRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (n : Nat)
    (next : Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    observedMaterializedBoundary parameter publicRoot ftsSecret
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inl n))) >>= next) observations state fuel table
        cache = (do
      let result ← runObservedCleanFromTable observations state fuel table
        ((splitUniformImpl n).run cache)
      match result with
      | none => pure none
      | some result =>
          observedMaterializedBoundary parameter publicRoot ftsSecret (next result.value.1)
            result.observations result.state result.remaining table result.value.2) := by
  rw [observedMaterializedBoundary, OracleComp.construct_query_bind]
  unfold observedMaterializedBoundary
  rfl

theorem observedMaterializedBoundary_hash_query_bind
    (parameter : PublicParameter) (publicRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    observedMaterializedBoundary parameter publicRoot ftsSecret
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next) observations state fuel table
        cache = (do
      let publicContext := materializedCanonicalContext table state
      let plan := purePlanProbingHashQuery parameter input publicContext.state
      let result ← runObservedCleanFromTable observations state fuel table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state plan).run
          cache)
      match result with
      | none => pure none
      | some result =>
          observedMaterializedBoundary parameter publicRoot ftsSecret (next result.value.1)
            result.observations result.state result.remaining table result.value.2) := by
  rw [observedMaterializedBoundary, OracleComp.construct_query_bind]
  unfold observedMaterializedBoundary
  rfl

theorem observedMaterializedBoundary_sign_query_bind
    (parameter : PublicParameter) (publicRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : SignRequest)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    observedMaterializedBoundary parameter publicRoot ftsSecret
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (Sum.inr message)) >>= next)
        observations state fuel table cache = (do
      let result ← runObservedCleanFromTable observations state fuel table
        ((maskedSign parameter publicRoot ftsSecret message).run cache)
      match result with
      | none => pure none
      | some result =>
          observedMaterializedBoundary parameter publicRoot ftsSecret (next result.value.1)
            result.observations result.state result.remaining table result.value.2) := by
  rw [observedMaterializedBoundary, OracleComp.construct_query_bind]
  unfold observedMaterializedBoundary
  rfl

theorem map_fst_continueObservedRootSelectionSharedPrefix_recurse
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (next : α → OracleComp (OracleWorld + SigningSpec) β)
    (observations : List CleanProbeObservation) (candidates : List Probe)
    (table : OtsSecretIndex → HashOutput)
    (hrecursive : ∀ value state fuel cache,
      Prod.fst <$> observedRootSelectionSharedPrefix ordinal parameter publicRoot target leftRoot
          rightRoot ftsSecret (next value) observations candidates state fuel table cache =
        observedMaterializedBoundary parameter publicRoot ftsSecret (next value) observations state
          fuel table cache)
    (detailed : DirectDetailedResult (α × SplitHashCache)) :
    Prod.fst <$> continueObservedRootSelectionSharedPrefix parameter publicRoot ftsSecret target
        next observations candidates table
        (fun value => observedRootSelectionSharedPrefix ordinal parameter publicRoot target leftRoot
          rightRoot ftsSecret (next value)) detailed =
      match observedResultOfDetailed observations detailed with
      | none => pure none
      | some result =>
          observedMaterializedBoundary parameter publicRoot ftsSecret (next result.value.1)
            result.observations result.state result.remaining table result.value.2 := by
  exact map_fst_continueObservedRootSelectionSharedPrefix parameter publicRoot ftsSecret target next
    observations candidates table
    (fun value => observedRootSelectionSharedPrefix ordinal parameter publicRoot target leftRoot
      rightRoot ftsSecret (next value)) hrecursive detailed

theorem evalDist_map_snd_continueObservedRootSelectionSharedPrefix_recurse
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (next : α → OracleComp (OracleWorld + SigningSpec) β)
    (observations : List CleanProbeObservation) (candidates : List Probe)
    (table : OtsSecretIndex → HashOutput)
    (hrecursive : ∀ value state fuel cache,
      evalDist (Prod.snd <$>
          observedRootSelectionSharedPrefix ordinal parameter publicRoot target leftRoot rightRoot
            ftsSecret (next value) observations candidates state fuel table cache) =
        evalDist
          (materializedActualRootAwareOrdinalSelectionOutcome ordinal parameter publicRoot target
            leftRoot rightRoot ftsSecret (next value) candidates state fuel table cache))
    (detailed : DirectDetailedResult (α × SplitHashCache)) :
    evalDist (Prod.snd <$>
        continueObservedRootSelectionSharedPrefix parameter publicRoot ftsSecret target next
          observations candidates table
          (fun value => observedRootSelectionSharedPrefix ordinal parameter publicRoot target
            leftRoot rightRoot ftsSecret (next value)) detailed) =
      evalDist
        (finishMaterializedSelectionOutcome target table
          (fun nextState remaining value nextCache laterCandidates =>
            materializedActualRootAwareOrdinalSelectionOutcome ordinal parameter publicRoot target
              leftRoot rightRoot ftsSecret (next value) laterCandidates nextState remaining table
              nextCache)
          candidates detailed) := by
  exact evalDist_map_snd_continueObservedRootSelectionSharedPrefix parameter publicRoot ftsSecret
    target next observations candidates table
    (fun value => observedRootSelectionSharedPrefix ordinal parameter publicRoot target leftRoot
      rightRoot ftsSecret (next value))
    (fun nextState remaining value nextCache laterCandidates =>
      materializedActualRootAwareOrdinalSelectionOutcome ordinal parameter publicRoot target
        leftRoot rightRoot ftsSecret (next value) laterCandidates nextState remaining table
        nextCache)
    hrecursive detailed

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem map_fst_observedRootSelectionSharedPrefix
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation) (candidates : List Probe)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    Prod.fst <$> observedRootSelectionSharedPrefix ordinal parameter publicRoot target leftRoot
        rightRoot ftsSecret computation observations candidates state fuel table cache =
      observedMaterializedBoundary parameter publicRoot ftsSecret computation observations state
        fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing
      observations candidates state fuel cache with
  | pure value =>
      rw [observedRootSelectionSharedPrefix, OracleComp.construct_pure,
        observedMaterializedBoundary, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length <;> simp [hselected]
  | query_bind query next ih =>
      rw [observedRootSelectionSharedPrefix_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact map_fst_finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
          (liftM (OracleSpec.query query) >>= next) observations state fuel table cache
          (.finished (some (candidates.get ⟨ordinal, hselected⟩)))
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                rw [observedMaterializedBoundary_uniform_query_bind]
                apply map_bind_of_map_eq
                  (observe := observedResultOfDetailed observations)
                · exact map_observedResultOfDetailed_run_eq_observed_of_probeFree
                    ((splitUniformImpl n).run cache) observations state fuel table
                    (splitUniformImpl_probeFree n cache)
                · intro detailed
                  cases detailed with
                  | stopped reason =>
                      exact map_fst_continueObservedRootSelectionSharedPrefix_recurse ordinal
                        parameter publicRoot target leftRoot rightRoot ftsSecret next observations
                        candidates table
                        (fun value nextState remaining nextCache =>
                          ih value observations candidates nextState remaining nextCache)
                        (.stopped reason)
                  | done result =>
                      exact map_fst_continueObservedRootSelectionSharedPrefix_recurse ordinal
                        parameter publicRoot target leftRoot rightRoot ftsSecret next observations
                        candidates table
                        (fun value nextState remaining nextCache =>
                          ih value observations candidates nextState remaining nextCache)
                        (.done result)
            | inr input =>
                rw [observedMaterializedBoundary_hash_query_bind]
                let publicContext := materializedCanonicalContext table state
                let plan := purePlanProbingHashQuery parameter input publicContext.state
                let candidate? := rootAwareCandidateForPlan? parameter input plan
                let nextCandidates := appendPlannedCandidate candidates candidate?
                let nextObservations := observationsAfterCandidate observations state candidate?
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [nextCandidates, candidate?, plan, publicContext] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  exact map_fst_finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
                    (liftM (OracleSpec.query (Sum.inl (Sum.inr input))) >>= next) observations state
                    fuel table cache (.finished
                      (some ((appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).get
                              ⟨ordinal, hactual⟩)))
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [nextCandidates, candidate?, plan, publicContext] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  by_cases hsafe :
                      RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate?
                  · have hactualSafe : RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [candidate?, plan, publicContext] using hsafe
                    simp only [hactualSafe, ↓reduceIte]
                    apply map_bind_of_map_eq
                      (observe := observedResultOfDetailed nextObservations)
                    · unfold observedResultOfDetailed nextObservations candidate? plan
                        publicContext
                      exact map_projectDirectDetailedObserved_rootAwarePublic parameter input
                        (materializedCanonicalContext table state).state
                        (purePlanProbingHashQuery parameter input
                          (materializedCanonicalContext table state).state)
                        observations state fuel table cache
                    · intro detailed
                      cases detailed with
                      | stopped reason =>
                          exact map_fst_continueObservedRootSelectionSharedPrefix_recurse ordinal
                            parameter publicRoot target leftRoot rightRoot ftsSecret next
                            nextObservations nextCandidates table
                            (fun value nextState remaining nextCache => ih value nextObservations
                              nextCandidates nextState remaining nextCache)
                            (.stopped reason)
                      | done result =>
                          exact map_fst_continueObservedRootSelectionSharedPrefix_recurse ordinal
                            parameter publicRoot target leftRoot rightRoot ftsSecret next
                            nextObservations nextCandidates table
                            (fun value nextState remaining nextCache => ih value nextObservations
                              nextCandidates nextState remaining nextCache)
                            (.done result)
                  · have hactualSafe : ¬RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [candidate?, plan, publicContext] using hsafe
                    simp only [hactualSafe, ↓reduceIte]
                    exact map_fst_finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
                      (liftM (OracleSpec.query (Sum.inl (Sum.inr input))) >>= next) observations
                      state fuel table cache (.finished none)
        | inr message =>
            rw [observedMaterializedBoundary_sign_query_bind]
            apply map_bind_of_map_eq
              (observe := observedResultOfDetailed observations)
            · exact map_observedResultOfDetailed_run_eq_observed_of_probeFree
                ((maskedSign parameter publicRoot ftsSecret message).run cache) observations state
                fuel table (maskedSign_probeFree parameter publicRoot ftsSecret message cache)
            · intro detailed
              cases detailed with
              | stopped reason =>
                  exact map_fst_continueObservedRootSelectionSharedPrefix_recurse ordinal
                    parameter publicRoot target leftRoot rightRoot ftsSecret next observations
                    candidates table
                    (fun value nextState remaining nextCache =>
                      ih value observations candidates nextState remaining nextCache)
                    (.stopped reason)
              | done result =>
                  exact map_fst_continueObservedRootSelectionSharedPrefix_recurse ordinal
                    parameter publicRoot target leftRoot rightRoot ftsSecret next observations
                    candidates table
                    (fun value nextState remaining nextCache =>
                      ih value observations candidates nextState remaining nextCache)
                    (.done result)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem evalDist_map_snd_observedRootSelectionSharedPrefix
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation) (candidates : List Probe)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    evalDist (Prod.snd <$>
        observedRootSelectionSharedPrefix ordinal parameter publicRoot target leftRoot rightRoot
          ftsSecret computation observations candidates state fuel table cache) =
      evalDist
        (materializedActualRootAwareOrdinalSelectionOutcome ordinal parameter publicRoot target
          leftRoot rightRoot ftsSecret computation candidates state fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing
      observations candidates state fuel cache with
  | pure value =>
      rw [observedRootSelectionSharedPrefix, OracleComp.construct_pure,
        materializedActualRootAwareOrdinalSelectionOutcome, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length <;> simp [hselected]
  | query_bind query next ih =>
      rw [observedRootSelectionSharedPrefix_query_bind]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [materializedActualRootAwareOrdinalSelectionOutcome_uniform_query_bind]
              by_cases hselected : ordinal < candidates.length
              · simp only [hselected, ↓reduceDIte]
                exact map_snd_finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
                  (liftM (OracleSpec.query (Sum.inl (Sum.inl n))) >>= next) observations state fuel
                  table cache (.finished (some (candidates.get ⟨ordinal, hselected⟩)))
              · simp only [hselected, ↓reduceDIte]
                apply evalDist_map_bind_congr
                intro detailed
                cases detailed with
                | stopped reason =>
                    exact
                      evalDist_map_snd_continueObservedRootSelectionSharedPrefix_recurse ordinal
                        parameter publicRoot target leftRoot rightRoot ftsSecret next observations
                        candidates table
                        (fun value nextState remaining nextCache =>
                          ih value observations candidates nextState remaining nextCache)
                        (.stopped reason)
                | done result =>
                    exact
                      evalDist_map_snd_continueObservedRootSelectionSharedPrefix_recurse ordinal
                        parameter publicRoot target leftRoot rightRoot ftsSecret next observations
                        candidates table
                        (fun value nextState remaining nextCache =>
                          ih value observations candidates nextState remaining nextCache)
                        (.done result)
          | inr input =>
              rw [materializedActualRootAwareOrdinalSelectionOutcome_hash_query_bind]
              by_cases hselected : ordinal < candidates.length
              · simp only [hselected, ↓reduceDIte]
                exact map_snd_finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
                  (liftM (OracleSpec.query (Sum.inl (Sum.inr input))) >>= next) observations state
                  fuel table cache (.finished (some (candidates.get ⟨ordinal, hselected⟩)))
              · simp only [hselected, ↓reduceDIte]
                let publicContext := materializedCanonicalContext table state
                let plan := purePlanProbingHashQuery parameter input publicContext.state
                let candidate? := rootAwareCandidateForPlan? parameter input plan
                let nextCandidates := appendPlannedCandidate candidates candidate?
                let nextObservations := observationsAfterCandidate observations state candidate?
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [nextCandidates, candidate?, plan, publicContext] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  exact map_snd_finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
                    (liftM (OracleSpec.query (Sum.inl (Sum.inr input))) >>= next) observations state
                    fuel table cache (.finished
                      (some ((appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).get
                              ⟨ordinal, hactual⟩)))
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [nextCandidates, candidate?, plan, publicContext] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  by_cases hsafe :
                      RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate?
                  · have hactualSafe : RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [candidate?, plan, publicContext] using hsafe
                    simp only [hactualSafe, ↓reduceIte]
                    apply evalDist_map_bind_congr
                    intro detailed
                    cases detailed with
                    | stopped reason =>
                        exact
                          evalDist_map_snd_continueObservedRootSelectionSharedPrefix_recurse
                            ordinal parameter publicRoot target leftRoot rightRoot ftsSecret next
                            nextObservations nextCandidates table
                            (fun value nextState remaining nextCache => ih value nextObservations
                              nextCandidates nextState remaining nextCache)
                            (.stopped reason)
                    | done result =>
                        exact
                          evalDist_map_snd_continueObservedRootSelectionSharedPrefix_recurse
                            ordinal parameter publicRoot target leftRoot rightRoot ftsSecret next
                            nextObservations nextCandidates table
                            (fun value nextState remaining nextCache => ih value nextObservations
                              nextCandidates nextState remaining nextCache)
                            (.done result)
                  · have hactualSafe : ¬RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [candidate?, plan, publicContext] using hsafe
                    simp only [hactualSafe, ↓reduceIte]
                    exact map_snd_finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
                      (liftM (OracleSpec.query (Sum.inl (Sum.inr input))) >>= next) observations
                      state fuel table cache (.finished none)
      | inr message =>
          rw [materializedActualRootAwareOrdinalSelectionOutcome_sign_query_bind]
          by_cases hselected : ordinal < candidates.length
          · simp only [hselected, ↓reduceDIte]
            exact map_snd_finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
              (liftM (OracleSpec.query (Sum.inr message)) >>= next) observations state fuel table
              cache (.finished (some (candidates.get ⟨ordinal, hselected⟩)))
          · simp only [hselected, ↓reduceDIte]
            apply evalDist_map_bind_congr
            intro detailed
            cases detailed with
            | stopped reason =>
                exact evalDist_map_snd_continueObservedRootSelectionSharedPrefix_recurse ordinal
                  parameter publicRoot target leftRoot rightRoot ftsSecret next observations
                  candidates table
                  (fun value nextState remaining nextCache =>
                    ih value observations candidates nextState remaining nextCache)
                  (.stopped reason)
            | done result =>
                exact evalDist_map_snd_continueObservedRootSelectionSharedPrefix_recurse ordinal
                  parameter publicRoot target leftRoot rightRoot ftsSecret next observations
                  candidates table
                  (fun value nextState remaining nextCache =>
                    ih value observations candidates nextState remaining nextCache)
                  (.done result)

end SphincsSecurity.Concrete.OtsProbeSimulation
