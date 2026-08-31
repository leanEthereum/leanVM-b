import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionMaterialize

/-!
# Materialized root-avoiding ordinal prefix

The auxiliary prefix executes against the already materialized shadow but derives every planned
candidate from its canonical public view. Before the selected ordinal it stops if a candidate
guesses either distinguished root. On the surviving branch every direct query satisfies the cache
quotient's safe-input premise.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

noncomputable def materializedCanonicalContext
    (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate) : DeferredContext :=
  canonicalizeMaterializedValues table (directDeferredContext state)

theorem materializedCanonicalContext_state_eq_of_rootHidden
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : RootHiddenStateRel target leftOutput rightOutput left right)
    (table : OtsSecretIndex → HashOutput) :
    (materializedCanonicalContext table left).state =
      (materializedCanonicalContext table right).state := by
  exact (hrel.directContext.canonicalize table).state

def RootSafePlannedHash
    (target : Position) (leftRoot rightRoot : Digest)
    (plan : PlannedHashQuery) (candidate? : Option Probe) : Prop :=
  RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate? ∧
    plan.action ≠ .resolve (.position target)

theorem rootSafePlannedHash_swap
    (target : Position) (leftRoot rightRoot : Digest)
    (plan : PlannedHashQuery) (candidate? : Option Probe) :
    RootSafePlannedHash target leftRoot rightRoot plan candidate? ↔
      RootSafePlannedHash target rightRoot leftRoot plan candidate? := by
  constructor
  · rintro ⟨⟨hleft, hright⟩, haction⟩
    exact ⟨⟨hright, hleft⟩, haction⟩
  · rintro ⟨⟨hright, hleft⟩, haction⟩
    exact ⟨⟨hleft, hright⟩, haction⟩

noncomputable def purePeekPositionValues
    (state : LazyRevealProbe.State Coordinate) : List Position → Option (List Digest)
  | [] => some []
  | position :: remaining =>
      match truncateHash <$> state.values (.position position) with
      | none => none
      | some value =>
          match purePeekPositionValues state remaining with
          | none => none
          | some values => some (value :: values)

noncomputable def purePeekTableInput
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate) :
    Coordinate → Option HashInput
  | .chainStart _ _ _ _ => none
  | .position position@(.chain lay tree leafIdx chainIdx step) =>
      if step.val = 0 then
        match truncateHash <$> state.values (.chainStart lay tree leafIdx chainIdx) with
        | none => none
        | some value => some (tweakableHashInput parameter position.domain (digestBytes value))
      else
        match purePeekPositionValues state position.children with
        | none => none
        | some values => some (tweakableHashInput parameter position.domain
            (values.flatMap digestBytes))
  | .position position =>
      match purePeekPositionValues state position.children with
      | none => none
      | some values => some (tweakableHashInput parameter position.domain
          (values.flatMap digestBytes))

noncomputable def resolvePublicKnownInput
    (parameter : PublicParameter) (publicState : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (input : HashInput) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput :=
  match purePeekTableInput parameter publicState coordinate with
  | some knownInput =>
      if knownInput = input then do
        let output ← revealCoordinateOutput coordinate
        publishCoordinate coordinate
        modify fun cache : SplitHashCache =>
          Function.update cache (.ordinary input) (some output)
        pure output
      else splitHashQuery (.ordinary input)
  | none => splitHashQuery (.ordinary input)

noncomputable def probingHashQueryAfterPublicPlan
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput := do
  executeCandidate? plan.candidate?
  match plan.action with
  | .ordinary => splitHashQuery (.ordinary input)
  | .resolve coordinate => resolvePublicKnownInput parameter publicState coordinate input

noncomputable def finishMaterializedPrivateOrdinalSelection
    (observe : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp (Option Probe))
    (candidates : List Probe) :
    Option (CleanRunResult (α × SplitHashCache)) → ProbComp (Option Probe)
  | none => pure none
  | some result =>
      observe result.state result.remaining result.value.1 result.value.2 candidates

noncomputable def continueMaterializedPrivateOrdinalSelection
    (target : Position)
    (observe : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp (Option Probe))
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (value : α) (cache : SplitHashCache) (candidates : List Probe) :
    ProbComp (Option Probe) :=
  if Coordinate.position target ∈ state.revealed then pure none
  else observe state fuel value cache candidates

noncomputable def materializedRootAvoidingOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option Probe) := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List Probe → LazyRevealProbe.State Coordinate → Nat →
        (OtsSecretIndex → HashOutput) → SplitHashCache → ProbComp (Option Probe))
    (fun _value candidates state _fuel _table _cache =>
      if hselected : ordinal < candidates.length then
        pure (some (candidates.get ⟨ordinal, hselected⟩))
      else pure none)
    (fun query _next recursivelyRun candidates state fuel table cache =>
      if hselected : ordinal < candidates.length then
        pure (some (candidates.get ⟨ordinal, hselected⟩))
      else
        match query with
        | .inl (.inl n) =>
            runCleanFromTable state fuel table ((splitUniformImpl n).run cache) >>=
              finishMaterializedPrivateOrdinalSelection
                (continueMaterializedPrivateOrdinalSelection target
                  (fun nextState remaining value nextCache laterCandidates =>
                    recursivelyRun value laterCandidates nextState remaining table nextCache))
                candidates
        | .inl (.inr input) =>
            let publicContext := materializedCanonicalContext table state
            let plan := purePlanProbingHashQuery parameter input publicContext.state
            let candidate? := rootAwareCandidateForPlan? parameter input plan
            let nextCandidates := appendPlannedCandidate candidates candidate?
            if hnextSelected : ordinal < nextCandidates.length then
              pure (some (nextCandidates.get ⟨ordinal, hnextSelected⟩))
            else if RootSafePlannedHash target leftRoot rightRoot plan candidate? then
              runCleanFromTable state fuel table
                  ((probingHashQueryAfterPublicPlan parameter input publicContext.state plan).run
                    cache) >>=
                finishMaterializedPrivateOrdinalSelection
                  (continueMaterializedPrivateOrdinalSelection target
                    (fun nextState remaining value nextCache laterCandidates =>
                      recursivelyRun value laterCandidates nextState remaining table nextCache))
                  nextCandidates
            else pure none
        | .inr message =>
            runCleanFromTable state fuel table ((signer message).run cache) >>=
              finishMaterializedPrivateOrdinalSelection
                (continueMaterializedPrivateOrdinalSelection target
                  (fun nextState remaining value nextCache laterCandidates =>
                    recursivelyRun value laterCandidates nextState remaining table nextCache))
                candidates)
    computation candidates state fuel table cache

noncomputable def materializedActualRootAvoidingOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option Probe) :=
  materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot rightRoot
    (maskedSign parameter publicRoot ftsSecret) computation candidates state fuel table cache

noncomputable def materializedComparisonRootAvoidingOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option Probe) :=
  materializedRootAvoidingOrdinalSelection ordinal parameter target
    (truncateHash leftOutput) (truncateHash rightOutput)
    (maskedSignWithTargetComparison parameter publicRoot target (truncateHash rightOutput)
      ftsSecret)
    computation candidates state fuel table cache

set_option maxRecDepth 100000 in
theorem materializedRootAvoidingOrdinalSelection_swap_roots
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot rightRoot signer
        computation candidates state fuel table cache =
      materializedRootAvoidingOrdinalSelection ordinal parameter target rightRoot leftRoot signer
        computation candidates state fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing
      candidates state fuel cache with
  | pure value =>
      simp [materializedRootAvoidingOrdinalSelection]
  | query_bind query next ih =>
      rw [materializedRootAvoidingOrdinalSelection, OracleComp.construct_query_bind,
        materializedRootAvoidingOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp [hselected]
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                apply bind_congr
                intro result
                cases result with
                | none => rfl
                | some result =>
                    unfold finishMaterializedPrivateOrdinalSelection
                    unfold continueMaterializedPrivateOrdinalSelection
                    by_cases hrevealed : Coordinate.position target ∈ result.state.revealed
                    · simp [hrevealed]
                    · simp only [hrevealed, ↓reduceIte]
                      exact ih result.value.1 candidates result.state result.remaining
                        result.value.2
            | inr input =>
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
                  simp [hactual]
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  have hsafe := rootSafePlannedHash_swap target leftRoot rightRoot
                    (purePlanProbingHashQuery parameter input
                      (materializedCanonicalContext table state).state)
                    (rootAwareCandidateForPlan? parameter input
                      (purePlanProbingHashQuery parameter input
                        (materializedCanonicalContext table state).state))
                  rw [propext hsafe]
                  by_cases hholds : RootSafePlannedHash target rightRoot leftRoot
                      (purePlanProbingHashQuery parameter input
                        (materializedCanonicalContext table state).state)
                      (rootAwareCandidateForPlan? parameter input
                        (purePlanProbingHashQuery parameter input
                          (materializedCanonicalContext table state).state))
                  · simp only [hholds, ↓reduceIte]
                    apply bind_congr
                    intro result
                    cases result with
                    | none => rfl
                    | some result =>
                        unfold finishMaterializedPrivateOrdinalSelection
                        unfold continueMaterializedPrivateOrdinalSelection
                        by_cases hrevealed : Coordinate.position target ∈ result.state.revealed
                        · simp [hrevealed]
                        · simp only [hrevealed, ↓reduceIte]
                          exact ih result.value.1 nextCandidates result.state result.remaining
                            result.value.2
                  · simp [hholds]
        | inr message =>
            apply bind_congr
            intro result
            cases result with
            | none => rfl
            | some result =>
                unfold finishMaterializedPrivateOrdinalSelection
                unfold continueMaterializedPrivateOrdinalSelection
                by_cases hrevealed : Coordinate.position target ∈ result.state.revealed
                · simp [hrevealed]
                · simp only [hrevealed, ↓reduceIte]
                  exact ih result.value.1 candidates result.state result.remaining result.value.2

end SphincsSecurity.Concrete.OtsProbeSimulation
