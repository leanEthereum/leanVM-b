import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSample

/-!
# Materialized comparison probability

The observation log is proof-only. This file first erases it from the standalone materialized
comparison, leaving the clean state, value, table and remaining probe fuel unchanged.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

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

theorem materializedCanonicalContext_values_eq_of_probeStateLE
    (table : OtsSecretIndex → HashOutput)
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : ProbeStateLE left right) :
    (materializedCanonicalContext table left).state.values =
      (materializedCanonicalContext table right).state.values := by
  change publicMaterializedValues table (directDeferredContext left) =
    publicMaterializedValues table (directDeferredContext right)
  funext coordinate
  unfold publicMaterializedValues
  have hrevealed : coordinate ∈ left.revealed ↔ coordinate ∈ right.revealed :=
    hstate.revealed_iff coordinate
  by_cases hleftRevealed : coordinate ∈ left.revealed
  · have hrightRevealed : coordinate ∈ right.revealed := hrevealed.mp hleftRevealed
    simp only [directDeferredContext, hleftRevealed, hrightRevealed, ↓reduceIte]
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx => simp [resolvedCompletionValue]
    | position position =>
        simp [resolvedCompletionValue, DeferredContext.positionValue, directDeferredValues,
          hstate.values]
  · have hrightRevealed : coordinate ∉ right.revealed := by
      simpa [hrevealed] using hleftRevealed
    simp [directDeferredContext, hleftRevealed, hrightRevealed]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_materializedCleanBoundary_probeLE
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (leftFuel rightFuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hstate : ProbeStateLE leftState rightState)
    (hfuel : rightFuel ≤ leftFuel) (hcache : leftCache = rightCache) :
    RelTriple
      (materializedCleanBoundary parameter root ftsSecret computation leftState leftFuel table
        leftCache)
      (materializedCleanBoundary parameter root ftsSecret computation rightState rightFuel table
        rightCache)
      CleanRunProbeLE := by
  induction computation using OracleComp.inductionOn generalizing leftState rightState leftFuel
      rightFuel leftCache rightCache with
  | pure value =>
      subst rightCache
      simp [materializedCleanBoundary, CleanRunProbeLE, hstate, hfuel]
  | query_bind query next ih =>
      rw [materializedCleanBoundary, OracleComp.construct_query_bind,
        materializedCleanBoundary, OracleComp.construct_query_bind]
      have continueAfter
          (leftRun rightRun : ProbComp (Option (CleanRunResult
            ((OracleWorld + SigningSpec).Range query × SplitHashCache))))
          (hrun : RelTriple leftRun rightRun CleanRunProbeLE) :
          RelTriple
            (leftRun >>= fun result =>
              match result with
              | none => pure none
              | some result =>
                  materializedCleanBoundary parameter root ftsSecret
                    (next result.value.1) result.state result.remaining table result.value.2)
            (rightRun >>= fun result =>
              match result with
              | none => pure none
              | some result =>
                  materializedCleanBoundary parameter root ftsSecret
                    (next result.value.1) result.state result.remaining table result.value.2)
            CleanRunProbeLE := by
        apply relTriple_bind hrun
        intro leftResult rightResult hresult
        cases rightResult with
        | none => exact relTriple_any_pure_none_clean _
        | some rightResult =>
            cases leftResult with
            | none => simp [CleanRunProbeLE] at hresult
            | some leftResult =>
                simp only
                rcases hresult with ⟨hvalue, htable, hremaining, hnextState⟩
                have houtput : leftResult.value.1 = rightResult.value.1 :=
                  congrArg Prod.fst hvalue
                have hnextCache : leftResult.value.2 = rightResult.value.2 :=
                  congrArg Prod.snd hvalue
                rw [← houtput, ← hnextCache]
                exact ih leftResult.value.1 leftResult.state rightResult.state
                  leftResult.remaining rightResult.remaining leftResult.value.2
                  leftResult.value.2 hnextState hremaining rfl
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              change Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α at next
              simp only
              subst rightCache
              have hstep := relTriple_runCleanFromTable_probeStateLE
                ((splitUniformImpl n).run leftCache) leftState rightState leftFuel rightFuel
                table hstate hfuel
              convert (continueAfter _ _ hstep) using 1 <;> rfl
          | inr input =>
              change HashOutput → OracleComp (OracleWorld + SigningSpec) α at next
              simp only
              let leftPublic := materializedCanonicalContext table leftState
              let rightPublic := materializedCanonicalContext table rightState
              have hpublicValues : leftPublic.state.values = rightPublic.state.values :=
                materializedCanonicalContext_values_eq_of_probeStateLE table hstate
              have hplan : purePlanProbingHashQuery parameter input leftPublic.state =
                  purePlanProbingHashQuery parameter input rightPublic.state :=
                purePlanProbingHashQuery_eq_of_values_eq hpublicValues parameter input
              let plan := purePlanProbingHashQuery parameter input leftPublic.state
              have hexecutor :
                  probingHashQueryAfterRootAwarePublicPlan parameter input leftPublic.state plan =
                    probingHashQueryAfterRootAwarePublicPlan parameter input rightPublic.state
                      plan :=
                probingHashQueryAfterRootAwarePublicPlan_eq_of_values_eq parameter input
                  hpublicValues plan
              rw [← hplan]
              subst rightCache
              rw [← hexecutor]
              have hstep := relTriple_runCleanFromTable_probeStateLE
                ((probingHashQueryAfterRootAwarePublicPlan parameter input leftPublic.state
                  plan).run leftCache)
                leftState rightState leftFuel rightFuel table hstate hfuel
              convert (continueAfter _ _ hstep) using 1 <;>
                simp only [leftPublic, plan, materializedCleanBoundary] <;>
                apply bind_congr <;> intro result <;> cases result <;> rfl
      | inr message =>
          change Option Signature → OracleComp (OracleWorld + SigningSpec) α at next
          simp only
          subst rightCache
          have hstep := relTriple_runCleanFromTable_probeStateLE
            ((maskedSign parameter root ftsSecret message).run leftCache)
            leftState rightState leftFuel rightFuel table hstate hfuel
          convert (continueAfter _ _ hstep) using 1 <;>
            simp only [materializedCleanBoundary] <;>
            apply bind_congr <;> intro result <;> cases result <;> rfl

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

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_materializedCleanRetainedRunFromTable_probeLE
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (leftFuel rightFuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hfuel : rightFuel ≤ leftFuel) :
    RelTriple
      (materializedCleanRetainedRunFromTable adversary parameter ftsSecret leftFuel table)
      (materializedCleanRetainedRunFromTable adversary parameter ftsSecret rightFuel table)
      CleanRunProbeLE := by
  unfold materializedCleanRetainedRunFromTable
  have hroot := relTriple_runCleanFromTable_probeStateLE
    (maskedPublishedTreeRoot.run emptySplitHashCache)
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
    LazyRevealProbe.State.empty leftFuel rightFuel table (ProbeStateLE.refl _) hfuel
  apply relTriple_bind hroot
  intro leftRoot rightRoot hrootResult
  cases rightRoot with
  | none => exact relTriple_any_pure_none_clean _
  | some rightRoot =>
      cases leftRoot with
      | none => simp [CleanRunProbeLE] at hrootResult
      | some leftRoot =>
          simp only
          rcases hrootResult with ⟨hvalue, htable, hremaining, hstate⟩
          have hrootValue : leftRoot.value.1 = rightRoot.value.1 :=
            congrArg Prod.fst hvalue
          have hcache : leftRoot.value.2 = rightRoot.value.2 :=
            congrArg Prod.snd hvalue
          rw [← hrootValue, ← hcache]
          have hrest := relTriple_materializedCleanBoundary_probeLE parameter
            leftRoot.value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨leftRoot.value.1, parameter⟩)
            leftRoot.state rightRoot.state leftRoot.remaining rightRoot.remaining table
            leftRoot.value.2 leftRoot.value.2 hstate hremaining rfl
          apply relTriple_bind hrest
          intro leftRest rightRest hrestResult
          cases rightRest with
          | none => exact relTriple_any_pure_none_clean _
          | some rightRest =>
              cases leftRest with
              | none => simp [CleanRunProbeLE] at hrestResult
              | some leftRest =>
                  rcases hrestResult with ⟨hrestValue, hrestTable, hrestRemaining,
                    hrestState⟩
                  exact relTriple_pure_pure ⟨by
                    rw [hrestValue], hrestTable, hrestRemaining, hrestState⟩

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

theorem deferredCompletable_direct_of_probeStateLE
    (table : OtsSecretIndex → HashOutput)
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : ProbeStateLE left right)
    (hcompletable : DeferredCompletable table (directDeferredContext right)) :
    DeferredCompletable table (directDeferredContext left) := by
  obtain ⟨completion, hvalues, hprivate, hpending, htable⟩ := hcompletable
  refine ⟨completion, ?_, ?_, ?_, htable⟩
  · intro coordinate output hvalue
    apply hvalues coordinate output
    simpa [directDeferredContext, hstate.values] using hvalue
  · intro position output hvalue
    apply hprivate position output
    simpa [directDeferredContext, directDeferredValues, hstate.values] using hvalue
  · intro coordinate candidate hpendingLeft
    exact hpending coordinate candidate (hstate.pending hpendingLeft)

theorem relTriple_finishMaterializedCleanRunFromTable_probeLE
    (table : OtsSecretIndex → HashOutput)
    (left right : Option (CleanRunResult α))
    (hrelation : CleanRunProbeLE left right) :
    RelTriple
      (finishMaterializedCleanRunFromTable table left)
      (finishMaterializedCleanRunFromTable table right)
      CleanFinishFailureLE := by
  classical
  cases right with
  | none => exact relTriple_cleanFinish_any_pure_none _
  | some rightResult =>
      cases left with
      | none => simp [CleanRunProbeLE] at hrelation
      | some leftResult =>
          rcases hrelation with ⟨hvalue, htable, hremaining, hstate⟩
          by_cases hleftCompletable :
              DeferredCompletable table (directDeferredContext leftResult.state)
          · by_cases hrightCompletable :
                DeferredCompletable table (directDeferredContext rightResult.state)
            · simp only [finishMaterializedCleanRunFromTable, hleftCompletable,
                hrightCompletable, ↓reduceIte]
              exact relTriple_finishCleanRunFromTable_probeLE (some leftResult)
                (some rightResult) ⟨hvalue, htable, hremaining, hstate⟩
            · simp only [finishMaterializedCleanRunFromTable, hleftCompletable,
                hrightCompletable, ↓reduceIte]
              exact relTriple_cleanFinish_any_pure_none _
          · have hrightNotCompletable :
                ¬DeferredCompletable table (directDeferredContext rightResult.state) := by
              intro hrightCompletable
              exact hleftCompletable
                (deferredCompletable_direct_of_probeStateLE table hstate hrightCompletable)
            simp [finishMaterializedCleanRunFromTable, hleftCompletable,
              hrightNotCompletable, CleanFinishFailureLE]

noncomputable def sampledMaterializedClean
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Option (CleanRunResult (RetainedGameResult × SplitHashCache))) := do
  let table ← sampleOtsHashTable
  let result ← materializedCleanRetainedRunFromTable adversary parameter ftsSecret fuel table
  finishMaterializedCleanRunFromTable table result

set_option maxRecDepth 100000 in
theorem relTriple_sampledMaterializedClean_fuelLE
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (leftFuel rightFuel : Nat) (hfuel : rightFuel ≤ leftFuel) :
    RelTriple
      (sampledMaterializedClean adversary parameter ftsSecret leftFuel)
      (sampledMaterializedClean adversary parameter ftsSecret rightFuel)
      CleanFinishFailureLE := by
  unfold sampledMaterializedClean
  apply relTriple_bind (relTriple_refl sampleOtsHashTable)
  intro leftTable rightTable htable
  subst rightTable
  apply relTriple_bind
    (relTriple_materializedCleanRetainedRunFromTable_probeLE adversary parameter ftsSecret
      leftFuel rightFuel leftTable hfuel)
  intro leftResult rightResult hresult
  exact relTriple_finishMaterializedCleanRunFromTable_probeLE leftTable leftResult rightResult
    hresult

theorem probEvent_sampledMaterializedClean_none_fuel_mono
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (leftFuel rightFuel : Nat) (hfuel : rightFuel ≤ leftFuel) :
    Pr[= none | sampledMaterializedClean adversary parameter ftsSecret leftFuel] ≤
      Pr[= none | sampledMaterializedClean adversary parameter ftsSecret rightFuel] := by
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  apply probEvent_le_of_relTriple
    (relTriple_sampledMaterializedClean_fuelLE adversary parameter ftsSecret leftFuel rightFuel
      hfuel)
  intro left right hrelation hleft
  exact hrelation hleft

def canonicalPublicProbeState (state : LazyRevealProbe.State Coordinate) :
    LazyRevealProbe.State Coordinate :=
  { state with
    values := fun coordinate =>
      if coordinate ∈ state.revealed then state.values coordinate else none }

theorem canonicalPublicProbeState_eq_materializedCanonicalContext_state
    (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (hstarts : StartTableAgrees state table)
    (hpublished : PublishedValues state) :
    canonicalPublicProbeState state =
      (materializedCanonicalContext table state).state := by
  cases state with
  | mk pending values revealed ensured =>
      unfold canonicalPublicProbeState materializedCanonicalContext
        canonicalizeMaterializedValues
      rw [LazyRevealProbe.State.mk.injEq]
      refine ⟨rfl, ?_, rfl, rfl⟩
      funext coordinate
      unfold publicMaterializedValues
      by_cases hrevealed : coordinate ∈ revealed
      · simp only [hrevealed, ↓reduceIte, directDeferredContext]
        cases coordinate with
        | chainStart lay tree leafIdx chainIdx =>
            cases hvalue : values (.chainStart lay tree leafIdx chainIdx) with
            | none => exact False.elim (hpublished _ hrevealed hvalue)
            | some output =>
                have heq := hstarts ⟨lay, tree, leafIdx, chainIdx⟩ output hvalue
                simp [resolvedCompletionValue, heq]
        | position position =>
            cases hvalue : values (.position position) with
            | none => exact False.elim (hpublished _ hrevealed hvalue)
            | some output =>
                simp [resolvedCompletionValue, DeferredContext.positionValue, hvalue]
      · simp [hrevealed, directDeferredContext]

noncomputable def finishCleanFailureObserve
    (observe : (OtsSecretIndex → HashOutput) →
      LazyRevealProbe.State Coordinate → Nat → α → ProbComp Bool) :
    Option (CleanRunResult α) → ProbComp Bool
  | none => pure true
  | some result => observe result.table result.state result.remaining result.value

set_option maxRecDepth 100000 in
theorem evalDist_runDirectDetailedSafeOrdinary_eq_cleanFailureObserve
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : (OtsSecretIndex → HashOutput) →
      LazyRevealProbe.State Coordinate → Nat → α → ProbComp Bool)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe fuel) :
    𝒟[runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
        computation >>=
      finishDirectDetailedSafeOrdinaryObserve
        (fun nextTable context remaining value =>
          observe nextTable context.state remaining value)] =
      𝒟[runCleanFromTable state fuel table computation >>=
        finishCleanFailureObserve observe] := by
  let detailed := runDirectResolvedDetailedFromTable
    (directDeferredContext state) fuel table computation
  calc
    _ = 𝒟[(projectDirectDetailedClean <$> detailed) >>=
          finishCleanFailureObserve observe] := by
      rw [map_eq_bind_pure_comp, bind_assoc]
      apply evalDist_bind_congr
      intro result hresult
      simp only [Function.comp_apply, pure_bind]
      have hshape := directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
        computation state fuel table result hresult
      cases result with
      | stopped reason =>
          cases reason with
          | ordinaryHit => rfl
          | privateStructuralHit => exact False.elim hshape
          | fuelExhausted =>
              exact False.elim
                (fuelExhausted_not_mem_support_runDirectResolvedDetailedFromTable
                  computation (directDeferredContext state) fuel table hbound hresult)
      | done result =>
          simp [finishDirectDetailedSafeOrdinaryObserve, finishCleanFailureObserve,
            projectDirectDetailedClean, DirectDetailedResult.toOption,
            projectResolvedRunResult]
    _ = _ := by
      rw [map_projectDirectDetailedClean_run_eq_clean]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_runDirectDetailedSafeOrdinary_eq_sampledCleanFailureObserve
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : (OtsSecretIndex → HashOutput) →
      LazyRevealProbe.State Coordinate → Nat → α → ProbComp Bool)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe fuel) :
    𝒟[runDirectDetailedSafeOrdinaryWithCompletionTable
        (fun nextTable context remaining value =>
          observe nextTable context.state remaining value)
        (directDeferredContext state) fuel computation] =
      𝒟[do
        let base ← sampleOtsHashTable
        let table := completedStartTable state base
        let result ← runCleanFromTable state fuel table computation
        finishCleanFailureObserve observe result] := by
  calc
    _ = 𝒟[(do
          let base ← sampleOtsHashTable
          let table := completedStartTable state base
          runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
            computation) >>=
        finishDirectDetailedSafeOrdinaryObserve
          (fun nextTable context remaining value =>
            observe nextTable context.state remaining value)] :=
      (evalDist_sampled_runDirectDetailedSafeOrdinary_eq_completionTable computation
        (fun nextTable context remaining value =>
          observe nextTable context.state remaining value)
        (directDeferredContext state) fuel).symm
    _ = _ := by
      rw [bind_assoc, evalDist_bind, evalDist_bind]
      apply congrArg
      funext base
      exact evalDist_runDirectDetailedSafeOrdinary_eq_cleanFailureObserve computation observe
        state fuel (completedStartTable state base) hbound

set_option maxRecDepth 100000 in
theorem fuel_le_remaining_add_of_mem_runCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : CleanRunResult α)
    (bound : Nat)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hresult : some result ∈ support
      (runCleanFromTable state fuel table computation)) :
    fuel ≤ result.remaining + bound := by
  rw [← map_projectDirectDetailedClean_run_eq_clean computation state fuel table,
    support_map] at hresult
  obtain ⟨detailed, hdetailed, hproject⟩ := hresult
  cases detailed with
  | stopped reason =>
      simp [projectDirectDetailedClean, DirectDetailedResult.toOption,
        projectResolvedRunResult] at hproject
  | done detailed =>
      have heq : result =
          ⟨detailed.context.state, detailed.remaining, detailed.value, detailed.table⟩ :=
        Option.some.inj (by simpa [projectDirectDetailedClean,
          DirectDetailedResult.toOption, projectResolvedRunResult] using hproject.symm)
      rw [heq]
      exact fuel_le_remaining_add_of_done_runDirectResolvedDetailedFromTable computation
        (directDeferredContext state) fuel table detailed bound hbound hdetailed

set_option maxRecDepth 100000 in
theorem publishedValues_of_mem_runCleanFromTable
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (result : CleanRunResult (α × SplitHashCache))
    (hpublished : PublishedValues state)
    (hpreserves : PreservesPublishedValues computation)
    (hresult : some result ∈ support
      (runCleanFromTable state fuel table (computation.run cache))) :
    PublishedValues result.state := by
  rw [← map_projectDirectDetailedClean_run_eq_clean (computation.run cache) state fuel table,
    support_map] at hresult
  obtain ⟨detailed, hdetailed, hproject⟩ := hresult
  cases detailed with
  | stopped reason =>
      simp [projectDirectDetailedClean, DirectDetailedResult.toOption,
        projectResolvedRunResult] at hproject
  | done detailed =>
      have heq : result =
          ⟨detailed.context.state, detailed.remaining, detailed.value, detailed.table⟩ :=
        Option.some.inj (by simpa [projectDirectDetailedClean,
          DirectDetailedResult.toOption, projectResolvedRunResult] using hproject.symm)
      have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
        (computation.run cache) (directDeferredContext state) fuel table detailed hdetailed
      have hraw := raw_done_of_mem_runDirectResolvedFromTable
        (computation.run cache) (directDeferredContext state) fuel table detailed hdirect
      rw [heq]
      exact hpreserves state cache fuel detailed.context.state detailed.remaining
        detailed.value.1 detailed.value.2 hpublished hraw

noncomputable def materializedCleanBoundaryFailureFromTable
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) : ProbComp Bool := do
  let result ← materializedCleanBoundary parameter root ftsSecret computation state fuel table
    cache
  let final ← finishCleanRunFromTable result
  pure final.isNone

noncomputable def sampledMaterializedCleanBoundaryFailure
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache) : ProbComp Bool := do
  let base ← sampleOtsHashTable
  materializedCleanBoundaryFailureFromTable parameter root ftsSecret computation state fuel
    (completedStartTable state base) cache

theorem materializedCleanBoundaryFailureFromTable_uniform_query_bind
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (n : Nat) (next : Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hstarts : StartTableAgrees state table) :
    𝒟[materializedCleanBoundaryFailureFromTable parameter root ftsSecret
        ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (.inl (.inl n)))) >>= next) state fuel table cache] = 𝒟[do
      let result ← runCleanFromTable state fuel table ((splitUniformImpl n).run cache)
      finishCleanFailureObserve
        (fun nextTable nextState remaining value =>
          materializedCleanBoundaryFailureFromTable parameter root ftsSecret
            (next (value : Fin (n + 1) × SplitHashCache).1) nextState remaining nextTable
            value.2)
        result] := by
  rw [materializedCleanBoundaryFailureFromTable, materializedCleanBoundary,
    OracleComp.construct_query_bind]
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      have htable := (startTableAgrees_of_mem_runCleanFromTable
        ((splitUniformImpl n).run cache) state fuel table hstarts result hresult).1
      simp [finishCleanFailureObserve, materializedCleanBoundaryFailureFromTable,
        materializedCleanBoundary, htable]

theorem materializedCleanBoundaryFailureFromTable_hash_query_bind
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hstarts : StartTableAgrees state table) (hpublished : PublishedValues state) :
    let publicState := canonicalPublicProbeState state
    let plan := purePlanProbingHashQuery parameter input publicState
    𝒟[materializedCleanBoundaryFailureFromTable parameter root ftsSecret
        ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (.inl (.inr input)))) >>= next) state fuel table cache] = 𝒟[do
      let result ← runCleanFromTable state fuel table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache)
      finishCleanFailureObserve
        (fun nextTable nextState remaining value =>
          materializedCleanBoundaryFailureFromTable parameter root ftsSecret
            (next (value : HashOutput × SplitHashCache).1) nextState remaining nextTable
            value.2)
        result] := by
  dsimp only
  have hpublic := canonicalPublicProbeState_eq_materializedCanonicalContext_state table state
    hstarts hpublished
  rw [materializedCleanBoundaryFailureFromTable, materializedCleanBoundary,
    OracleComp.construct_query_bind]
  simp only
  rw [← hpublic]
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      have htable := (startTableAgrees_of_mem_runCleanFromTable
        ((probingHashQueryAfterRootAwarePublicPlan parameter input
          (canonicalPublicProbeState state)
          (purePlanProbingHashQuery parameter input (canonicalPublicProbeState state))).run cache)
        state fuel table hstarts result hresult).1
      simp [finishCleanFailureObserve, materializedCleanBoundaryFailureFromTable,
        materializedCleanBoundary, htable]

theorem materializedCleanBoundaryFailureFromTable_sign_query_bind
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (message : SignRequest)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hstarts : StartTableAgrees state table) :
    𝒟[materializedCleanBoundaryFailureFromTable parameter root ftsSecret
        ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (.inr message))) >>= next) state fuel table cache] = 𝒟[do
      let result ← runCleanFromTable state fuel table
        ((maskedSign parameter root ftsSecret message).run cache)
      finishCleanFailureObserve
        (fun nextTable nextState remaining value =>
          materializedCleanBoundaryFailureFromTable parameter root ftsSecret
            (next (value : Option Signature × SplitHashCache).1) nextState remaining nextTable
            value.2)
        result] := by
  rw [materializedCleanBoundaryFailureFromTable, materializedCleanBoundary,
    OracleComp.construct_query_bind]
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      have htable := (startTableAgrees_of_mem_runCleanFromTable
        ((maskedSign parameter root ftsSecret message).run cache)
        state fuel table hstarts result hresult).1
      simp [finishCleanFailureObserve, materializedCleanBoundaryFailureFromTable,
        materializedCleanBoundary, htable]

theorem preservesPublishedValues_resolvePublicKnownInput
    (parameter : PublicParameter) (publicState : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (input : HashInput) :
    PreservesPublishedValues
      (resolvePublicKnownInput parameter publicState coordinate input) := by
  unfold resolvePublicKnownInput
  cases hknown : purePeekTableInput parameter publicState coordinate with
  | none =>
      exact PreservesPublishedValues.of_preservesCoordinate fun other =>
        preservesCoordinate_splitHashQuery other (.ordinary input)
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        have hpreserves :=
          (preservesPublishedValues_revealCoordinateOutput_publish coordinate).bind
            fun output =>
              (PreservesPublishedValues.of_preservesCoordinate fun other =>
                preservesCoordinate_modify other fun cache =>
                  Function.update cache (.ordinary input) (some output)).bind fun _ =>
                    PreservesPublishedValues.pure output
        simpa only [bind_assoc, pure_bind] using hpreserves
      · simp only [heq, ↓reduceIte]
        exact PreservesPublishedValues.of_preservesCoordinate fun other =>
          preservesCoordinate_splitHashQuery other (.ordinary input)

theorem preservesPublishedValues_probingHashQueryAfterRootAwarePublicPlan
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery) :
    PreservesPublishedValues
      (probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan) := by
  unfold probingHashQueryAfterRootAwarePublicPlan
  apply (preservesPublishedValues_executeCandidate
    (rootAwareCandidateForPlan? parameter input plan)).bind
  intro _
  cases plan.action with
  | ordinary => exact preservesPublishedValues_splitHashQuery_ordinary input
  | resolve coordinate =>
      exact preservesPublishedValues_resolvePublicKnownInput parameter publicState coordinate input

noncomputable def guardedMaterializedCleanContinuation
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (next : β → OracleComp (OracleWorld + SigningSpec) α)
    (bound : Nat) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat)
    (value : β × SplitHashCache) : ProbComp Bool := by
  classical
  exact if PublishedValues context.state ∧ bound ≤ fuel then
      materializedCleanBoundaryFailureFromTable parameter root ftsSecret (next value.1)
        context.state fuel table value.2
    else
      pure false

set_option maxRecDepth 100000 in
theorem evalDist_sampledCleanStep_eq_safeGuardedContinuation
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (next : β → OracleComp (OracleWorld + SigningSpec) α)
    (inner : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache) (stepBound nextBound : Nat)
    (hpublished : PublishedValues state)
    (hinnerBound : (inner.run cache).IsQueryBoundP LazyRevealProbe.IsProbe stepBound)
    (hpreserves : PreservesPublishedValues inner)
    (hbudget : nextBound + stepBound ≤ fuel) :
    𝒟[do
        let base ← sampleOtsHashTable
        let table := completedStartTable state base
        let result ← runCleanFromTable state fuel table (inner.run cache)
        finishCleanFailureObserve
          (fun nextTable nextState remaining value =>
            materializedCleanBoundaryFailureFromTable parameter root ftsSecret
              (next (value : β × SplitHashCache).1) nextState remaining nextTable value.2)
          result] =
      𝒟[runDirectDetailedSafeOrdinaryWithCompletionTable
        (guardedMaterializedCleanContinuation parameter root ftsSecret next nextBound)
        (directDeferredContext state) fuel (inner.run cache)] := by
  symm
  calc
    _ = 𝒟[do
        let base ← sampleOtsHashTable
        let table := completedStartTable state base
        let result ← runCleanFromTable state fuel table (inner.run cache)
        finishCleanFailureObserve
          (fun nextTable nextState remaining value =>
            guardedMaterializedCleanContinuation parameter root ftsSecret next nextBound
              nextTable (directDeferredContext nextState) remaining value)
          result] :=
      evalDist_runDirectDetailedSafeOrdinary_eq_sampledCleanFailureObserve
        (inner.run cache)
        (fun nextTable nextState remaining value =>
          guardedMaterializedCleanContinuation parameter root ftsSecret next nextBound
            nextTable (directDeferredContext nextState) remaining
              (value : β × SplitHashCache))
        state fuel (hinnerBound.mono (by omega))
    _ = _ := by
      apply evalDist_bind_congr
      intro base _hbase
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => rfl
      | some result =>
          have hnextPublished := publishedValues_of_mem_runCleanFromTable inner state cache fuel
            (completedStartTable state base) result hpublished hpreserves hresult
          have hfuel := fuel_le_remaining_add_of_mem_runCleanFromTable (inner.run cache) state fuel
            (completedStartTable state base) result stepBound hinnerBound hresult
          have hnextBudget : nextBound ≤ result.remaining := by omega
          simp only [finishCleanFailureObserve]
          unfold guardedMaterializedCleanContinuation
          simp only [directDeferredContext]
          rw [if_pos ⟨hnextPublished, hnextBudget⟩]

theorem probEvent_sampledRunThenFinalizeClean_none_le
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe fuel) :
    Pr[= none | sampledRunThenFinalizeClean state fuel computation] ≤
      ((fuel + state.pending.card : Nat) : ENNReal) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ = Pr[= none | detailedExperimentCleanWithCompletionTable state fuel computation] :=
      OracleComp.probOutput_congr rfl
        (by
          unfold sampledRunThenFinalizeClean
          exact evalDist_runThenFinalizeCleanFromTable_eq_detailed computation state fuel)
    _ = Pr[= true | LazyRevealProbe.experiment state fuel computation] :=
      probEvent_detailedExperimentClean_none_eq_hit computation state fuel hbound
    _ ≤ _ := by
      rw [← probEvent_eq_eq_probOutput]
      exact LazyRevealProbe.experiment_probability_le state fuel computation

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_sampledMaterializedCleanBoundaryFailure_le
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : LazyRevealProbe.State Coordinate) (fuel bound : Nat)
    (cache : SplitHashCache)
    (hbound : computation.IsQueryBoundP IsOuterHash bound)
    (hbudget : bound ≤ fuel)
    (hpublished : PublishedValues state) :
    Pr[= true |
        sampledMaterializedCleanBoundaryFailure parameter root ftsSecret computation state fuel
          cache] ≤
      ((fuel + state.pending.card : Nat) : ENNReal) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing state fuel bound cache with
  | pure value =>
      have hdist :
          𝒟[Option.isNone <$> sampledRunThenFinalizeClean state fuel
            (pure (value, cache) : OracleComp (LazyRevealProbe.World Coordinate)
              (α × SplitHashCache))] =
            𝒟[sampledMaterializedCleanBoundaryFailure parameter root ftsSecret
              (pure value) state fuel cache] := by
        unfold sampledRunThenFinalizeClean sampledMaterializedCleanBoundaryFailure
          materializedCleanBoundaryFailureFromTable
        rw [map_bind]
        apply evalDist_bind_congr
        intro base _hbase
        rw [runCleanFromTable_pure_oracle]
        simp [materializedCleanBoundary]
      calc
        _ = Pr[= true | Option.isNone <$> sampledRunThenFinalizeClean state fuel
              (pure (value, cache) : OracleComp (LazyRevealProbe.World Coordinate)
                (α × SplitHashCache))] :=
          OracleComp.probOutput_congr rfl hdist.symm
        _ = Pr[= none | sampledRunThenFinalizeClean state fuel
              (pure (value, cache) : OracleComp (LazyRevealProbe.World Coordinate)
                (α × SplitHashCache))] := by
          rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map]
          apply OracleComp.probEvent_congr'
          · intro result _hresult
            cases result <;> simp
          · rfl
        _ ≤ _ := probEvent_sampledRunThenFinalizeClean_none_le
          (pure (value, cache) : OracleComp (LazyRevealProbe.World Coordinate)
            (α × SplitHashCache)) state fuel (by simp)
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              have hinnerBound : ((splitUniformImpl n).run cache).IsQueryBoundP
                  LazyRevealProbe.IsProbe 0 := splitUniformImpl_probeFree n cache
              have hstep := evalDist_sampledCleanStep_eq_safeGuardedContinuation
                parameter root ftsSecret next (splitUniformImpl n) state fuel cache 0 bound
                hpublished hinnerBound (preservesPublishedValuesImpl_splitUniformImpl n)
                (by omega)
              have hdist :
                  𝒟[sampledMaterializedCleanBoundaryFailure parameter root ftsSecret
                    ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                      (.inl (.inl n)))) >>= next) state fuel cache] =
                    𝒟[runDirectDetailedSafeOrdinaryWithCompletionTable
                      (guardedMaterializedCleanContinuation parameter root ftsSecret next bound)
                      (directDeferredContext state) fuel ((splitUniformImpl n).run cache)] := by
                calc
                  _ = 𝒟[do
                      let base ← sampleOtsHashTable
                      let table := completedStartTable state base
                      let result ← runCleanFromTable state fuel table
                        ((splitUniformImpl n).run cache)
                      finishCleanFailureObserve
                        (fun nextTable nextState remaining value =>
                          materializedCleanBoundaryFailureFromTable parameter root ftsSecret
                            (next (value : Fin (n + 1) × SplitHashCache).1) nextState remaining
                            nextTable value.2)
                        result] := by
                    unfold sampledMaterializedCleanBoundaryFailure
                    apply evalDist_bind_congr
                    intro base _hbase
                    exact materializedCleanBoundaryFailureFromTable_uniform_query_bind parameter
                      root ftsSecret n next state fuel (completedStartTable state base) cache
                      (startTableAgrees_completedStartTable state base)
                  _ = _ := hstep
              calc
                _ = Pr[= true | runDirectDetailedSafeOrdinaryWithCompletionTable
                      (guardedMaterializedCleanContinuation parameter root ftsSecret next bound)
                      (directDeferredContext state) fuel ((splitUniformImpl n).run cache)] :=
                  OracleComp.probOutput_congr rfl hdist
                _ ≤ _ := by
                  rw [← probEvent_eq_eq_probOutput]
                  apply probEvent_runDirectDetailedSafeOrdinaryWithCompletionTable_le
                  intro nextContext remaining value
                  rw [probEvent_eq_eq_probOutput]
                  by_cases hguard : PublishedValues nextContext.state ∧ bound ≤ remaining
                  · simp only [guardedMaterializedCleanContinuation, hguard]
                    exact ih value.1 nextContext.state remaining bound value.2
                      (by simpa [IsOuterHash] using hbound.2 value.1) hguard.2 hguard.1
                  · simp [guardedMaterializedCleanContinuation, hguard]
          | inr input =>
              let publicState := canonicalPublicProbeState state
              let plan := purePlanProbingHashQuery parameter input publicState
              let inner := probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan
              let nextBound := bound - 1
              have hpositive : 0 < bound := by
                rcases hbound.1 with hnot | hpositive
                · exact (hnot (by simp [IsOuterHash])).elim
                · exact hpositive
              have hinnerBound : (inner.run cache).IsQueryBoundP
                  LazyRevealProbe.IsProbe 1 :=
                probingHashQueryAfterRootAwarePublicPlan_isProbeBound_one parameter input
                  publicState plan cache
              have hstep := evalDist_sampledCleanStep_eq_safeGuardedContinuation
                parameter root ftsSecret next inner state fuel cache 1 nextBound hpublished
                hinnerBound
                (preservesPublishedValues_probingHashQueryAfterRootAwarePublicPlan parameter input
                  publicState plan)
                (by dsimp only [nextBound]; omega)
              have hdist :
                  𝒟[sampledMaterializedCleanBoundaryFailure parameter root ftsSecret
                    ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                      (.inl (.inr input)))) >>= next) state fuel cache] =
                    𝒟[runDirectDetailedSafeOrdinaryWithCompletionTable
                      (guardedMaterializedCleanContinuation parameter root ftsSecret next nextBound)
                      (directDeferredContext state) fuel (inner.run cache)] := by
                calc
                  _ = 𝒟[do
                      let base ← sampleOtsHashTable
                      let table := completedStartTable state base
                      let result ← runCleanFromTable state fuel table (inner.run cache)
                      finishCleanFailureObserve
                        (fun nextTable nextState remaining value =>
                          materializedCleanBoundaryFailureFromTable parameter root ftsSecret
                            (next (value : HashOutput × SplitHashCache).1) nextState remaining
                            nextTable value.2)
                        result] := by
                    unfold sampledMaterializedCleanBoundaryFailure
                    apply evalDist_bind_congr
                    intro base _hbase
                    simpa only [publicState, plan, inner] using
                      (materializedCleanBoundaryFailureFromTable_hash_query_bind parameter root
                        ftsSecret input next state fuel (completedStartTable state base) cache
                        (startTableAgrees_completedStartTable state base) hpublished)
                  _ = _ := hstep
              calc
                _ = Pr[= true | runDirectDetailedSafeOrdinaryWithCompletionTable
                      (guardedMaterializedCleanContinuation parameter root ftsSecret next nextBound)
                      (directDeferredContext state) fuel (inner.run cache)] :=
                  OracleComp.probOutput_congr rfl hdist
                _ ≤ _ := by
                  rw [← probEvent_eq_eq_probOutput]
                  apply probEvent_runDirectDetailedSafeOrdinaryWithCompletionTable_le
                  intro nextContext remaining value
                  rw [probEvent_eq_eq_probOutput]
                  by_cases hguard : PublishedValues nextContext.state ∧
                      nextBound ≤ remaining
                  · simp only [guardedMaterializedCleanContinuation, hguard]
                    exact ih value.1 nextContext.state remaining nextBound value.2
                      (by
                        dsimp only [nextBound]
                        simpa [IsOuterHash] using hbound.2 value.1)
                      hguard.2 hguard.1
                  · simp [guardedMaterializedCleanContinuation, hguard]
      | inr message =>
          have hinnerBound : ((maskedSign parameter root ftsSecret message).run cache).IsQueryBoundP
              LazyRevealProbe.IsProbe 0 :=
            maskedSign_probeFree parameter root ftsSecret message cache
          have hstep := evalDist_sampledCleanStep_eq_safeGuardedContinuation
            parameter root ftsSecret next (maskedSign parameter root ftsSecret message)
            state fuel cache 0 bound hpublished hinnerBound
            (preservesPublishedValues_maskedSign parameter root ftsSecret message) (by omega)
          have hdist :
              𝒟[sampledMaterializedCleanBoundaryFailure parameter root ftsSecret
                ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                  (.inr message))) >>= next) state fuel cache] =
                𝒟[runDirectDetailedSafeOrdinaryWithCompletionTable
                  (guardedMaterializedCleanContinuation parameter root ftsSecret next bound)
                  (directDeferredContext state) fuel
                  ((maskedSign parameter root ftsSecret message).run cache)] := by
            calc
              _ = 𝒟[do
                  let base ← sampleOtsHashTable
                  let table := completedStartTable state base
                  let result ← runCleanFromTable state fuel table
                    ((maskedSign parameter root ftsSecret message).run cache)
                  finishCleanFailureObserve
                    (fun nextTable nextState remaining value =>
                      materializedCleanBoundaryFailureFromTable parameter root ftsSecret
                        (next (value : Option Signature × SplitHashCache).1) nextState remaining
                        nextTable value.2)
                    result] := by
                unfold sampledMaterializedCleanBoundaryFailure
                apply evalDist_bind_congr
                intro base _hbase
                exact materializedCleanBoundaryFailureFromTable_sign_query_bind parameter root
                  ftsSecret message next state fuel (completedStartTable state base) cache
                  (startTableAgrees_completedStartTable state base)
              _ = _ := hstep
          calc
            _ = Pr[= true | runDirectDetailedSafeOrdinaryWithCompletionTable
                  (guardedMaterializedCleanContinuation parameter root ftsSecret next bound)
                  (directDeferredContext state) fuel
                  ((maskedSign parameter root ftsSecret message).run cache)] :=
              OracleComp.probOutput_congr rfl hdist
            _ ≤ _ := by
              rw [← probEvent_eq_eq_probOutput]
              apply probEvent_runDirectDetailedSafeOrdinaryWithCompletionTable_le
              intro nextContext remaining value
              rw [probEvent_eq_eq_probOutput]
              by_cases hguard : PublishedValues nextContext.state ∧ bound ≤ remaining
              · simp only [guardedMaterializedCleanContinuation, hguard]
                exact ih value.1 nextContext.state remaining bound value.2
                  (by simpa [IsOuterHash] using hbound.2 value.1) hguard.2 hguard.1
              · simp [guardedMaterializedCleanContinuation, hguard]

noncomputable def sampledMaterializedCleanUnguarded
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Option (CleanRunResult (RetainedGameResult × SplitHashCache))) := do
  let table ← sampleOtsHashTable
  let result ← materializedCleanRetainedRunFromTable adversary parameter ftsSecret fuel table
  finishCleanRunFromTable result

noncomputable def guardedMaterializedRootContinuation
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (bound : Nat)
    (table : OtsSecretIndex → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (value : Digest × SplitHashCache) : ProbComp Bool := by
  classical
  exact if PublishedValues state ∧ bound ≤ fuel then
      materializedCleanBoundaryFailureFromTable parameter value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
        state fuel table value.2
    else
      pure false

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_sampledMaterializedCleanUnguarded_isNone_eq_safeRoot_of_fuel
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel bound : Nat)
    (hbudget : bound ≤ fuel) :
    𝒟[Option.isNone <$>
        sampledMaterializedCleanUnguarded adversary parameter ftsSecret fuel] =
      𝒟[runDirectDetailedSafeOrdinaryWithCompletionTable
        (fun table context remaining value =>
          guardedMaterializedRootContinuation adversary parameter ftsSecret bound table
            context.state remaining value)
        (directDeferredContext
          (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)) fuel
        (maskedPublishedTreeRoot.run emptySplitHashCache)] := by
  have hsafe := evalDist_runDirectDetailedSafeOrdinary_eq_sampledCleanFailureObserve
    (maskedPublishedTreeRoot.run emptySplitHashCache)
    (fun table state remaining value =>
      guardedMaterializedRootContinuation adversary parameter ftsSecret bound table
        state remaining value)
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel
    (maskedPublishedTreeRoot_probeFree emptySplitHashCache |>.mono (by omega))
  calc
    _ = 𝒟[do
        let base ← sampleOtsHashTable
        let table := completedStartTable
          (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) base
        let result ← runCleanFromTable LazyRevealProbe.State.empty fuel table
          (maskedPublishedTreeRoot.run emptySplitHashCache)
        finishCleanFailureObserve
          (fun nextTable state remaining value =>
            guardedMaterializedRootContinuation adversary parameter ftsSecret bound nextTable
              state remaining value)
          result] := by
      unfold sampledMaterializedCleanUnguarded materializedCleanRetainedRunFromTable
      rw [map_bind]
      apply evalDist_bind_congr
      intro table _htable
      rw [completedStartTable_empty, map_bind]
      simp only [bind_assoc]
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => rfl
      | some result =>
          have hpublished := publishedValues_of_mem_runCleanFromTable maskedPublishedTreeRoot
            (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) emptySplitHashCache fuel
            table result (by simp [PublishedValues, LazyRevealProbe.State.empty])
            preservesPublishedValues_maskedPublishedTreeRoot hresult
          have hfuel := fuel_le_remaining_add_of_mem_runCleanFromTable
            (maskedPublishedTreeRoot.run emptySplitHashCache)
            (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table result 0
            (maskedPublishedTreeRoot_probeFree emptySplitHashCache) hresult
          have hremaining : bound ≤ result.remaining := by omega
          have hguard : PublishedValues result.state ∧ bound ≤ result.remaining :=
            ⟨hpublished, hremaining⟩
          have htable := (startTableAgrees_of_mem_runCleanFromTable
            (maskedPublishedTreeRoot.run emptySplitHashCache)
            (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
            (startTableAgrees_empty table) result hresult).1
          simp only [finishCleanFailureObserve, guardedMaterializedRootContinuation,
            if_pos hguard]
          rw [← htable]
          unfold materializedCleanBoundaryFailureFromTable
          simp only [bind_assoc]
          apply evalDist_bind_congr
          intro restResult _hrestResult
          cases restResult with
          | none => simp [finishCleanRunFromTable]
          | some restResult =>
              simp only [finishCleanRunFromTable, pure_bind]
              rw [map_bind]
              simp only [bind_assoc]
              apply evalDist_bind_congr
              intro finalized _hfinalized
              cases finalized <;> rfl
    _ = _ := hsafe.symm

theorem evalDist_sampledMaterializedCleanUnguarded_isNone_eq_safeRoot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) :
    𝒟[Option.isNone <$>
        sampledMaterializedCleanUnguarded adversary parameter ftsSecret q] =
      𝒟[runDirectDetailedSafeOrdinaryWithCompletionTable
        (fun table context remaining value =>
          guardedMaterializedRootContinuation adversary parameter ftsSecret q table
            context.state remaining value)
        (directDeferredContext
          (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)) q
        (maskedPublishedTreeRoot.run emptySplitHashCache)] :=
  evalDist_sampledMaterializedCleanUnguarded_isNone_eq_safeRoot_of_fuel adversary parameter
    ftsSecret q q le_rfl

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledMaterializedCleanUnguarded_none_le_of_fuel
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (hbudget : q ≤ fuel) :
    Pr[= none | sampledMaterializedCleanUnguarded adversary parameter ftsSecret fuel] ≤
      (fuel : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ = Pr[= true | Option.isNone <$>
        sampledMaterializedCleanUnguarded adversary parameter ftsSecret fuel] := by
      rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map]
      apply OracleComp.probEvent_congr'
      · intro result _hresult
        cases result <;> simp
      · rfl
    _ = Pr[= true | runDirectDetailedSafeOrdinaryWithCompletionTable
        (fun table context remaining value =>
          guardedMaterializedRootContinuation adversary parameter ftsSecret q table
            context.state remaining value)
        (directDeferredContext
          (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)) fuel
        (maskedPublishedTreeRoot.run emptySplitHashCache)] :=
      OracleComp.probOutput_congr rfl
        (evalDist_sampledMaterializedCleanUnguarded_isNone_eq_safeRoot_of_fuel adversary parameter
          ftsSecret fuel q hbudget)
    _ ≤ _ := by
      rw [← probEvent_eq_eq_probOutput]
      have hsafe := probEvent_runDirectDetailedSafeOrdinaryWithCompletionTable_le
        (maskedPublishedTreeRoot.run emptySplitHashCache)
        (fun table context remaining value =>
          guardedMaterializedRootContinuation adversary parameter ftsSecret q table
            context.state remaining value)
        (by
          intro context remaining value
          rw [probEvent_eq_eq_probOutput]
          by_cases hguard : PublishedValues context.state ∧ q ≤ remaining
          · simpa [guardedMaterializedRootContinuation, hguard,
                sampledMaterializedCleanBoundaryFailure] using
              (probEvent_sampledMaterializedCleanBoundaryFailure_le parameter value.1
              ftsSecret
              (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
              context.state remaining q value.2 (hbound value.1) hguard.2 hguard.1)
          · simp [guardedMaterializedRootContinuation, hguard])
        (directDeferredContext
          (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)) fuel
      simpa [emptyWitnessDeferredContext, LazyRevealProbe.State.empty] using hsafe

theorem probEvent_sampledMaterializedCleanUnguarded_none_le
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    Pr[= none | sampledMaterializedCleanUnguarded adversary parameter ftsSecret q] ≤
      (q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
  probEvent_sampledMaterializedCleanUnguarded_none_le_of_fuel adversary parameter ftsSecret q q
    hbound le_rfl

noncomputable def materializedSafeBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) : ProbComp Bool := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      (DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool) →
        DeferredContext → Nat → SplitHashCache → ProbComp Bool)
    (fun value observe context fuel cache => observe context fuel (value, cache))
    (fun query _next recursivelyRun observe context fuel cache =>
      match query with
      | .inl (.inl n) =>
          runDirectDetailedSafeOrdinaryWithCompletionTable
            (fun _ nextContext remaining value =>
              recursivelyRun value.1 observe nextContext remaining value.2)
            context fuel ((splitUniformImpl n).run cache)
      | .inl (.inr input) =>
          let publicState := canonicalPublicProbeState context.state
          let plan := purePlanProbingHashQuery parameter input publicState
          runDirectDetailedSafeOrdinaryWithCompletionTable
            (fun _ nextContext remaining value =>
              recursivelyRun value.1 observe nextContext remaining value.2)
            context fuel
              ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
                cache)
      | .inr message =>
          runDirectDetailedSafeOrdinaryWithCompletionTable
            (fun _ nextContext remaining value =>
              recursivelyRun value.1 observe nextContext remaining value.2)
            context fuel ((maskedSign parameter root ftsSecret message).run cache))
    computation observe context fuel cache

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_materializedSafeBoundary_le
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    (hobserve : ∀ context fuel value,
      Pr[= true | observe context fuel value] ≤
        ((fuel + context.state.pending.card : Nat) : ENNReal) *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    Pr[= true |
        materializedSafeBoundary parameter root ftsSecret computation observe context fuel
          cache] ≤
      ((fuel + context.state.pending.card : Nat) : ENNReal) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      simpa [materializedSafeBoundary] using hobserve context fuel (value, cache)
  | query_bind query next ih =>
      rw [materializedSafeBoundary, OracleComp.construct_query_bind]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              simp only
              rw [← probEvent_eq_eq_probOutput]
              apply probEvent_runDirectDetailedSafeOrdinaryWithCompletionTable_le
              intro nextContext remaining value
              have hdist :
                  𝒟[do
                    let _base ← sampleOtsHashTable
                    materializedSafeBoundary parameter root ftsSecret (next value.1)
                      observe nextContext remaining value.2] =
                    𝒟[materializedSafeBoundary parameter root ftsSecret (next value.1)
                      observe nextContext remaining value.2] :=
                evalDist_sampleOtsHashTable_bind_const _
              have hih := ih value.1 nextContext remaining value.2
              rw [← probEvent_eq_eq_probOutput] at hih
              exact (OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans hih
          | inr input =>
              simp only
              rw [← probEvent_eq_eq_probOutput]
              apply probEvent_runDirectDetailedSafeOrdinaryWithCompletionTable_le
              intro nextContext remaining value
              have hdist :
                  𝒟[do
                    let _base ← sampleOtsHashTable
                    materializedSafeBoundary parameter root ftsSecret (next value.1)
                      observe nextContext remaining value.2] =
                    𝒟[materializedSafeBoundary parameter root ftsSecret (next value.1)
                      observe nextContext remaining value.2] :=
                evalDist_sampleOtsHashTable_bind_const _
              have hih := ih value.1 nextContext remaining value.2
              rw [← probEvent_eq_eq_probOutput] at hih
              exact (OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans hih
      | inr message =>
          simp only
          rw [← probEvent_eq_eq_probOutput]
          apply probEvent_runDirectDetailedSafeOrdinaryWithCompletionTable_le
          intro nextContext remaining value
          have hdist :
              𝒟[do
                let _base ← sampleOtsHashTable
                materializedSafeBoundary parameter root ftsSecret (next value.1)
                  observe nextContext remaining value.2] =
                𝒟[materializedSafeBoundary parameter root ftsSecret (next value.1)
                  observe nextContext remaining value.2] :=
            evalDist_sampleOtsHashTable_bind_const _
          have hih := ih value.1 nextContext remaining value.2
          rw [← probEvent_eq_eq_probOutput] at hih
          exact (OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans hih

noncomputable def materializedSafeFinalObserve
    (context : DeferredContext) (_fuel : Nat)
    (_value : RetainedRestResult × SplitHashCache) : ProbComp Bool :=
  LazyRevealProbe.finalize context.state

theorem probEvent_materializedSafeFinalObserve_le
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) :
    Pr[= true | materializedSafeFinalObserve context fuel value] ≤
      ((fuel + context.state.pending.card : Nat) : ENNReal) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  unfold materializedSafeFinalObserve
  rw [← probEvent_eq_eq_probOutput]
  refine (LazyRevealProbe.finalize_probability_le context.state).trans ?_
  have hnat : context.state.pending.card ≤ fuel + context.state.pending.card := by omega
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) zero_le

noncomputable def materializedSafeRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ProbComp Bool :=
  runDirectDetailedSafeOrdinaryWithCompletionTable
    (fun _ context remaining value =>
      materializedSafeBoundary parameter value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
        materializedSafeFinalObserve context remaining value.2)
    emptyWitnessDeferredContext fuel (maskedPublishedTreeRoot.run emptySplitHashCache)

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxRecDepth 100000 in
theorem probEvent_materializedSafeRetained_le
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[= true | materializedSafeRetained adversary parameter ftsSecret fuel] ≤
      (fuel : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  unfold materializedSafeRetained
  have hbound := probEvent_runDirectDetailedSafeOrdinaryWithCompletionTable_le
    (maskedPublishedTreeRoot.run emptySplitHashCache)
    (fun _ context remaining value =>
      materializedSafeBoundary parameter value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
        materializedSafeFinalObserve context remaining value.2)
    (by
      intro context remaining value
      have hdist :
          𝒟[do
            let _base ← sampleOtsHashTable
            materializedSafeBoundary parameter value.1 ftsSecret
              (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
              materializedSafeFinalObserve context remaining value.2] =
            𝒟[materializedSafeBoundary parameter value.1 ftsSecret
              (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
              materializedSafeFinalObserve context remaining value.2] :=
        evalDist_sampleOtsHashTable_bind_const _
      have hsafe := probEvent_materializedSafeBoundary_le parameter value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
        materializedSafeFinalObserve probEvent_materializedSafeFinalObserve_le context remaining
        value.2
      rw [← probEvent_eq_eq_probOutput] at hsafe
      exact (OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans hsafe)
    emptyWitnessDeferredContext fuel
  simpa [emptyWitnessDeferredContext, LazyRevealProbe.State.empty] using hbound

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
