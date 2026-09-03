import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProbability

/-!
# Common root-aware production selector

The fixed-target root bound leaves a target-specific production weight. This module defines the
single deferred selector whose position fibers will account for all of those weights. It executes
the proof-only root-aware probe, but neither its computation nor its sampled state names a target.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational


theorem materializedCanonicalContext_values_materialize_hidden
    (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate) (target : Position) (output : HashOutput)
    (hhidden : Coordinate.position target ∉ state.revealed) :
    (materializedCanonicalContext table
        (state.materialize (.position target) output)).state.values =
      (materializedCanonicalContext table state).state.values := by
  funext coordinate
  unfold materializedCanonicalContext canonicalizeMaterializedValues
    publicMaterializedValues directDeferredContext
  simp only [LazyRevealProbe.State.materialize]
  by_cases hrevealed : coordinate ∈ state.revealed
  · have hne : coordinate ≠ .position target := by
      intro heq
      subst coordinate
      exact hhidden hrevealed
    rw [if_pos hrevealed, if_pos hrevealed]
    unfold resolvedCompletionValue DeferredContext.positionValue
    cases coordinate with
    | chainStart => rfl
    | position position =>
        have hposition : position ≠ target := by
          simpa using hne
        simp [directDeferredValues, Function.update_of_ne, hposition]
  · rw [if_neg hrevealed, if_neg hrevealed]

theorem purePlanProbingHashQuery_materialize_hidden
    (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate) (target : Position) (output : HashOutput)
    (hhidden : Coordinate.position target ∉ state.revealed)
    (parameter : PublicParameter) (input : HashInput) :
    purePlanProbingHashQuery parameter input
        (materializedCanonicalContext table
          (state.materialize (.position target) output)).state =
      purePlanProbingHashQuery parameter input
        (materializedCanonicalContext table state).state :=
  purePlanProbingHashQuery_eq_of_values_eq
    (materializedCanonicalContext_values_materialize_hidden table state target output hhidden)
    parameter input

noncomputable def runPermissiveFromTable
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    ProbComp (Option (CleanRunResult α)) :=
  OracleComp.construct
    (C := fun _ : OracleComp (LazyRevealProbe.World Coordinate) α =>
      LazyRevealProbe.State Coordinate → Nat → (OtsSecretIndex → HashOutput) →
        ProbComp (Option (CleanRunResult α)))
    (fun value state remaining table => pure (some ⟨state, remaining, value, table⟩))
    (fun input _next recursivelyRun state fuel table =>
      match input with
      | .uniform n => do
          let output ← liftM (unifSpec.query n)
          recursivelyRun output state fuel table
      | .hashOutput => do
          let output ← LazyRevealProbe.sampleHashOutput
          recursivelyRun output state fuel table
      | .ensure coordinate =>
          recursivelyRun () (state.ensure coordinate) fuel table
      | .probe coordinate candidate =>
          match fuel with
          | 0 => pure none
          | remaining + 1 =>
              if coordinate ∈ state.revealed then
                recursivelyRun () state remaining table
              else
                recursivelyRun () (state.addPending coordinate candidate) remaining table
      | .peek coordinate =>
          recursivelyRun (state.values coordinate) state fuel table
      | .publish coordinate =>
          recursivelyRun () (state.publish coordinate) fuel table
      | .reveal coordinate =>
          match state.values coordinate with
          | some output => recursivelyRun output state fuel table
          | none =>
              match coordinate with
              | .chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  recursivelyRun output (state.materialize coordinate output) fuel table
              | .position _ => do
                  let output ← LazyRevealProbe.sampleHashOutput
                  recursivelyRun output (state.materialize coordinate output) fuel table)
    computation state fuel table

structure PermissiveStateRel
    (left right : LazyRevealProbe.State Coordinate) : Prop where
  values : left.values = right.values
  revealed : left.revealed = right.revealed

def PermissiveCleanRel :
    Option (CleanRunResult α) → Option (CleanRunResult α) → Prop
  | none, none => True
  | some left, some right =>
      PermissiveStateRel left.state right.state ∧
        left.remaining = right.remaining ∧ left.value = right.value ∧ left.table = right.table
  | _, _ => False

theorem PermissiveStateRel.ensure
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : PermissiveStateRel left right) (coordinate : Coordinate) :
    PermissiveStateRel (left.ensure coordinate) (right.ensure coordinate) := by
  exact ⟨hrel.values, hrel.revealed⟩

theorem PermissiveStateRel.addPending
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : PermissiveStateRel left right) (coordinate : Coordinate) (candidate : Digest) :
    PermissiveStateRel (left.addPending coordinate candidate)
      (right.addPending coordinate candidate) := by
  exact ⟨hrel.values, hrel.revealed⟩

theorem PermissiveStateRel.publish
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : PermissiveStateRel left right) (coordinate : Coordinate) :
    PermissiveStateRel (left.publish coordinate) (right.publish coordinate) := by
  exact ⟨hrel.values,
    by simp [LazyRevealProbe.State.publish, hrel.revealed]⟩

theorem PermissiveStateRel.materialize
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : PermissiveStateRel left right) (coordinate : Coordinate) (output : HashOutput) :
    PermissiveStateRel (left.materialize coordinate output)
      (right.materialize coordinate output) := by
  exact ⟨by simp [LazyRevealProbe.State.materialize, hrel.values], hrel.revealed⟩

theorem materializedCanonicalContext_values_eq_of_permissiveStateRel
    (table : OtsSecretIndex → HashOutput)
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : PermissiveStateRel left right) :
    (materializedCanonicalContext table left).state.values =
      (materializedCanonicalContext table right).state.values := by
  change publicMaterializedValues table (directDeferredContext left) =
    publicMaterializedValues table (directDeferredContext right)
  funext coordinate
  unfold publicMaterializedValues
  have hrevealed : coordinate ∈ left.revealed ↔ coordinate ∈ right.revealed := by
    rw [hstate.revealed]
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

set_option maxRecDepth 100000 in
theorem relTriple_runPermissiveFromTable_of_stateRel
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (left right : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hstate : PermissiveStateRel left right) :
    RelTriple
      (runPermissiveFromTable left fuel table computation)
      (runPermissiveFromTable right fuel table computation)
      PermissiveCleanRel := by
  induction computation using OracleComp.inductionOn generalizing left right fuel with
  | pure value =>
      simp [runPermissiveFromTable, PermissiveCleanRel, hstate]
  | query_bind query next ih =>
      rw [runPermissiveFromTable, OracleComp.construct_query_bind,
        runPermissiveFromTable, OracleComp.construct_query_bind]
      cases query with
      | uniform n =>
          apply relTriple_bind (relTriple_refl (liftM (unifSpec.query n)))
          intro leftOutput rightOutput heq
          subst rightOutput
          exact ih leftOutput left right fuel hstate
      | hashOutput =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput heq
          subst rightOutput
          exact ih leftOutput left right fuel hstate
      | ensure coordinate =>
          exact ih () (left.ensure coordinate) (right.ensure coordinate) fuel
            (hstate.ensure coordinate)
      | probe coordinate candidate =>
          cases fuel with
          | zero => simp [PermissiveCleanRel]
          | succ remaining =>
              have hrevealed : coordinate ∈ left.revealed ↔ coordinate ∈ right.revealed := by
                rw [hstate.revealed]
              by_cases hleft : coordinate ∈ left.revealed
              · have hright : coordinate ∈ right.revealed := hrevealed.mp hleft
                simp only [hleft, hright, ↓reduceIte]
                exact ih () left right remaining hstate
              · have hright : coordinate ∉ right.revealed := by
                  simpa [hrevealed] using hleft
                simp only [hleft, hright, ↓reduceIte]
                exact ih () (left.addPending coordinate candidate)
                  (right.addPending coordinate candidate) remaining
                  (hstate.addPending coordinate candidate)
      | peek coordinate =>
          have hvalue := congrFun hstate.values coordinate
          simp only
          rw [hvalue]
          exact ih (right.values coordinate) left right fuel hstate
      | publish coordinate =>
          exact ih () (left.publish coordinate) (right.publish coordinate) fuel
            (hstate.publish coordinate)
      | reveal coordinate =>
          have hvalue := congrFun hstate.values coordinate
          cases hleft : left.values coordinate with
          | some output =>
              have hright : right.values coordinate = some output := by
                rw [← hvalue]
                exact hleft
              simp only [hleft, hright]
              exact ih output left right fuel hstate
          | none =>
              have hright : right.values coordinate = none := by
                rw [← hvalue]
                exact hleft
              simp only [hleft, hright]
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  exact ih (table ⟨lay, tree, leafIdx, chainIdx⟩)
                    (left.materialize (.chainStart lay tree leafIdx chainIdx)
                      (table ⟨lay, tree, leafIdx, chainIdx⟩))
                    (right.materialize (.chainStart lay tree leafIdx chainIdx)
                      (table ⟨lay, tree, leafIdx, chainIdx⟩)) fuel
                    (hstate.materialize (.chainStart lay tree leafIdx chainIdx)
                      (table ⟨lay, tree, leafIdx, chainIdx⟩))
              | position position =>
                  apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
                  intro leftOutput rightOutput heq
                  subst rightOutput
                  exact ih leftOutput (left.materialize (.position position) leftOutput)
                    (right.materialize (.position position) leftOutput) fuel
                    (hstate.materialize (.position position) leftOutput)

def CleanPermissiveRel :
    Option (CleanRunResult α) → Option (CleanRunResult α) → Prop
  | none, _ => True
  | some left, right => right = some left

theorem relTriple_none_any_cleanPermissive
    (right : ProbComp (Option (CleanRunResult α))) :
    RelTriple (pure none : ProbComp (Option (CleanRunResult α))) right
      CleanPermissiveRel := by
  have hbase := relTriple_true
    (pure none : ProbComp (Option (CleanRunResult α))) right
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun value => value = none) (by
        intro value hvalue
        simpa using hvalue)
  apply relTriple_post_mono hsupported
  intro left right hrelation
  rw [hrelation.2]
  trivial

set_option maxRecDepth 100000 in
theorem relTriple_runCleanFromTable_runPermissiveFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runCleanFromTable state fuel table computation)
      (runPermissiveFromTable state fuel table computation)
      CleanPermissiveRel := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      simp [runCleanFromTable, runPermissiveFromTable, CleanPermissiveRel]
  | query_bind query next ih =>
      rw [runCleanFromTable, OracleComp.construct_query_bind,
        runPermissiveFromTable, OracleComp.construct_query_bind]
      cases query with
      | uniform n =>
          apply relTriple_bind (relTriple_refl (liftM (unifSpec.query n)))
          intro left right heq
          subst right
          exact ih left state fuel
      | hashOutput =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro left right heq
          subst right
          exact ih left state fuel
      | ensure coordinate => exact ih () (state.ensure coordinate) fuel
      | probe coordinate candidate =>
          cases fuel with
          | zero => simp [CleanPermissiveRel]
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () state remaining
              · simp only [hrevealed, ↓reduceIte]
                exact ih () (state.addPending coordinate candidate) remaining
      | peek coordinate => exact ih (state.values coordinate) state fuel
      | publish coordinate => exact ih () (state.publish coordinate) fuel
      | reveal coordinate =>
          cases hvalue : state.values coordinate with
          | some output =>
              simp only [hvalue]
              exact ih output state fuel
          | none =>
              simp only [hvalue]
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : state.hitAt (.chainStart lay tree leafIdx chainIdx) output
                  · simp only [output, hhit, ↓reduceIte]
                    exact relTriple_none_any_cleanPermissive
                      (runPermissiveFromTable
                        (state.materialize (.chainStart lay tree leafIdx chainIdx) output)
                        fuel table (next output))
                  · simp only [output, hhit, ↓reduceIte]
                    exact ih output
                      (state.materialize (.chainStart lay tree leafIdx chainIdx) output) fuel
              | position position =>
                  apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
                  intro left right heq
                  subst right
                  by_cases hhit : state.hitAt (.position position) left
                  · simp only [hhit, ↓reduceIte]
                    exact relTriple_none_any_cleanPermissive
                      (runPermissiveFromTable
                        (state.materialize (.position position) left) fuel table (next left))
                  · simp only [hhit, ↓reduceIte]
                    exact ih left (state.materialize (.position position) left) fuel

noncomputable def finishPermissivePrivateOrdinalSelection
    (observe : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp (Option Probe))
    (candidates : List Probe) : Option (CleanRunResult (α × SplitHashCache)) →
      ProbComp (Option Probe)
  | none => pure none
  | some result =>
      observe result.state result.remaining result.value.1 result.value.2 candidates

noncomputable def permissiveRootAwarePlan
    (parameter : PublicParameter) (input : HashInput)
    (table : OtsSecretIndex → HashOutput) (state : LazyRevealProbe.State Coordinate) :
    PlannedHashQuery :=
  purePlanProbingHashQuery parameter input (materializedCanonicalContext table state).state

noncomputable def permissiveRootAwareCandidates
    (parameter : PublicParameter) (input : HashInput)
    (table : OtsSecretIndex → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (candidates : List Probe) : List Probe :=
  appendPlannedCandidate candidates
    (rootAwareCandidateForPlan? parameter input
      (permissiveRootAwarePlan parameter input table state))

noncomputable def permissiveRootAwarePublicActionWithPlan
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (cache : SplitHashCache) :
    OracleComp (LazyRevealProbe.World Coordinate) (HashOutput × SplitHashCache) :=
  (probingHashQueryAfterRootAwarePublicPlan parameter input state plan).run cache

noncomputable def permissiveRootAwarePublicAction
    (parameter : PublicParameter) (input : HashInput)
    (table : OtsSecretIndex → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) :
    OracleComp (LazyRevealProbe.World Coordinate) (HashOutput × SplitHashCache) :=
  permissiveRootAwarePublicActionWithPlan parameter input
    (materializedCanonicalContext table state).state
    (permissiveRootAwarePlan parameter input table state) cache

noncomputable def selectPermissiveOrdinal
    (ordinal : Nat) (candidates : List Probe) (otherwise : ProbComp (Option Probe)) :
    ProbComp (Option Probe) :=
  if hselected : ordinal < candidates.length then
    pure (some (candidates.get ⟨ordinal, hselected⟩))
  else
    otherwise

noncomputable def permissiveRootAwareHashContinue
    (_ordinal : Nat) (parameter : PublicParameter) (input : HashInput)
    (recursivelyRun : HashOutput → List Probe → LazyRevealProbe.State Coordinate → Nat →
      (OtsSecretIndex → HashOutput) → SplitHashCache → ProbComp (Option Probe))
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option Probe) :=
  runPermissiveFromTable state fuel table
      (permissiveRootAwarePublicAction parameter input table state cache) >>=
    finishPermissivePrivateOrdinalSelection
      (fun nextState remaining value nextCache laterCandidates =>
        recursivelyRun value laterCandidates nextState remaining table nextCache)
      (permissiveRootAwareCandidates parameter input table state candidates)

noncomputable def permissiveRootAwareHashStep
    (ordinal : Nat) (parameter : PublicParameter) (input : HashInput)
    (recursivelyRun : HashOutput → List Probe → LazyRevealProbe.State Coordinate → Nat →
      (OtsSecretIndex → HashOutput) → SplitHashCache → ProbComp (Option Probe))
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option Probe) :=
  selectPermissiveOrdinal ordinal
    (permissiveRootAwareCandidates parameter input table state candidates)
    (permissiveRootAwareHashContinue ordinal parameter input recursivelyRun candidates state fuel
      table cache)

noncomputable def permissiveRootAwareOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option Probe) := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List Probe → LazyRevealProbe.State Coordinate → Nat →
        (OtsSecretIndex → HashOutput) → SplitHashCache → ProbComp (Option Probe))
    (fun _value candidates _state _fuel _table _cache =>
      if hselected : ordinal < candidates.length then
        pure (some (candidates.get ⟨ordinal, hselected⟩))
      else pure none)
    (fun query _next recursivelyRun candidates state fuel table cache =>
      if hselected : ordinal < candidates.length then
        pure (some (candidates.get ⟨ordinal, hselected⟩))
      else
        match query with
        | .inl (.inl n) =>
            runPermissiveFromTable state fuel table ((splitUniformImpl n).run cache) >>=
              finishPermissivePrivateOrdinalSelection
                (fun nextState remaining value nextCache laterCandidates =>
                  recursivelyRun value laterCandidates nextState remaining table nextCache)
                candidates
        | .inl (.inr input) =>
            permissiveRootAwareHashStep ordinal parameter input recursivelyRun candidates state
              fuel table cache
        | .inr message =>
            runPermissiveFromTable state fuel table
                ((maskedSign parameter root ftsSecret message).run cache) >>=
              finishPermissivePrivateOrdinalSelection
                (fun nextState remaining value nextCache laterCandidates =>
                  recursivelyRun value laterCandidates nextState remaining table nextCache)
                candidates)
    computation candidates state fuel table cache

theorem relTriple_finishPermissivePrivateOrdinalSelection_eq
    (leftObserve rightObserve : LazyRevealProbe.State Coordinate → Nat → α →
      SplitHashCache → List Probe → ProbComp (Option Probe))
    (leftCandidates rightCandidates : List Probe)
    (left right : Option (CleanRunResult (α × SplitHashCache)))
    (hresult : PermissiveCleanRel left right)
    (hrecursive : ∀ (leftResult rightResult : CleanRunResult (α × SplitHashCache)),
      PermissiveCleanRel (some leftResult) (some rightResult) →
      RelTriple
        (leftObserve leftResult.state leftResult.remaining leftResult.value.1
          leftResult.value.2 leftCandidates)
        (rightObserve rightResult.state rightResult.remaining rightResult.value.1
          rightResult.value.2 rightCandidates)
        (EqRel (Option Probe))) :
    RelTriple
      (finishPermissivePrivateOrdinalSelection leftObserve leftCandidates left)
      (finishPermissivePrivateOrdinalSelection rightObserve rightCandidates right)
      (EqRel (Option Probe)) := by
  cases left with
  | none =>
      cases right with
      | none => exact relTriple_pure_pure rfl
      | some right => exact False.elim hresult
  | some left =>
      cases right with
      | none => exact False.elim hresult
      | some right => exact hrecursive left right hresult

theorem relTriple_selectPermissiveOrdinal
    (ordinal : Nat) (leftCandidates rightCandidates : List Probe)
    (leftOtherwise rightOtherwise : ProbComp (Option Probe))
    (hcandidates : leftCandidates = rightCandidates)
    (hotherwise : RelTriple leftOtherwise rightOtherwise (EqRel (Option Probe))) :
    RelTriple
      (selectPermissiveOrdinal ordinal leftCandidates leftOtherwise)
      (selectPermissiveOrdinal ordinal rightCandidates rightOtherwise)
      (EqRel (Option Probe)) := by
  subst rightCandidates
  unfold selectPermissiveOrdinal
  by_cases hselected : ordinal < leftCandidates.length
  · simp only [hselected, ↓reduceDIte]
    exact relTriple_pure_pure rfl
  · simp only [hselected, ↓reduceDIte]
    exact hotherwise

theorem permissiveRootAwarePlan_eq_of_stateRel
    (parameter : PublicParameter) (input : HashInput)
    (table : OtsSecretIndex → HashOutput)
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : PermissiveStateRel left right) :
    permissiveRootAwarePlan parameter input table left =
      permissiveRootAwarePlan parameter input table right := by
  unfold permissiveRootAwarePlan
  exact purePlanProbingHashQuery_eq_of_values_eq
    (materializedCanonicalContext_values_eq_of_permissiveStateRel table hstate)
    parameter input

theorem permissiveRootAwareCandidates_eq_of_stateRel
    (parameter : PublicParameter) (input : HashInput)
    (table : OtsSecretIndex → HashOutput) (candidates : List Probe)
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : PermissiveStateRel left right) :
    permissiveRootAwareCandidates parameter input table left candidates =
      permissiveRootAwareCandidates parameter input table right candidates := by
  unfold permissiveRootAwareCandidates
  rw [permissiveRootAwarePlan_eq_of_stateRel parameter input table hstate]

theorem permissiveRootAwarePublicActionWithPlan_eq_of_values_eq
    (parameter : PublicParameter) (input : HashInput)
    {left right : LazyRevealProbe.State Coordinate}
    (hvalues : left.values = right.values) (plan : PlannedHashQuery)
    (cache : SplitHashCache) :
    permissiveRootAwarePublicActionWithPlan parameter input left plan cache =
      permissiveRootAwarePublicActionWithPlan parameter input right plan cache := by
  exact congrArg (fun computation => computation.run cache)
    (probingHashQueryAfterRootAwarePublicPlan_eq_of_values_eq parameter input hvalues plan)

theorem permissiveRootAwarePublicAction_eq_of_stateRel
    (parameter : PublicParameter) (input : HashInput)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : PermissiveStateRel left right) :
    permissiveRootAwarePublicAction parameter input table left cache =
      permissiveRootAwarePublicAction parameter input table right cache := by
  unfold permissiveRootAwarePublicAction
  have hvalues := materializedCanonicalContext_values_eq_of_permissiveStateRel table hstate
  calc
    permissiveRootAwarePublicActionWithPlan parameter input
        (materializedCanonicalContext table left).state
        (permissiveRootAwarePlan parameter input table left) cache =
      permissiveRootAwarePublicActionWithPlan parameter input
        (materializedCanonicalContext table right).state
        (permissiveRootAwarePlan parameter input table left) cache :=
      permissiveRootAwarePublicActionWithPlan_eq_of_values_eq parameter input hvalues _ cache
    _ = permissiveRootAwarePublicActionWithPlan parameter input
        (materializedCanonicalContext table right).state
        (permissiveRootAwarePlan parameter input table right) cache :=
      congrArg
        (fun plan => permissiveRootAwarePublicActionWithPlan parameter input
          (materializedCanonicalContext table right).state plan cache)
        (permissiveRootAwarePlan_eq_of_stateRel parameter input table hstate)

theorem relTriple_permissiveRootAwareHashContinue_of_stateRel
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (table : OtsSecretIndex → HashOutput)
    (hrecursive : ∀ output candidates rightCandidates left right fuel cache,
      candidates = rightCandidates → PermissiveStateRel left right →
      RelTriple
        (permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret (next output)
          candidates left fuel table cache)
        (permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret (next output)
          rightCandidates right fuel table cache)
        (EqRel (Option Probe)))
    (candidates : List Probe)
    (left right : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache)
    (hstate : PermissiveStateRel left right) :
    RelTriple
      (permissiveRootAwareHashContinue ordinal parameter input
        (fun output laterCandidates nextState remaining laterTable nextCache =>
          permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret (next output)
            laterCandidates nextState remaining laterTable nextCache)
        candidates left fuel table cache)
      (permissiveRootAwareHashContinue ordinal parameter input
        (fun output laterCandidates nextState remaining laterTable nextCache =>
          permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret (next output)
            laterCandidates nextState remaining laterTable nextCache)
        candidates right fuel table cache)
      (EqRel (Option Probe)) := by
  unfold permissiveRootAwareHashContinue
  have hcandidates := permissiveRootAwareCandidates_eq_of_stateRel parameter input table
    candidates hstate
  have haction := permissiveRootAwarePublicAction_eq_of_stateRel parameter input table cache
    hstate
  have hrun : RelTriple
      (runPermissiveFromTable left fuel table
        (permissiveRootAwarePublicAction parameter input table left cache))
      (runPermissiveFromTable right fuel table
        (permissiveRootAwarePublicAction parameter input table right cache))
      PermissiveCleanRel := by
    rw [haction]
    exact relTriple_runPermissiveFromTable_of_stateRel _ left right fuel table hstate
  let observe : LazyRevealProbe.State Coordinate → Nat → HashOutput →
      SplitHashCache → List Probe → ProbComp (Option Probe) :=
    fun nextState remaining output nextCache laterCandidates ↦
      permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret
        (next output) laterCandidates nextState remaining table nextCache
  apply relTriple_bind hrun
  intro leftResult rightResult hresult
  apply relTriple_finishPermissivePrivateOrdinalSelection_eq observe observe
    (permissiveRootAwareCandidates parameter input table left candidates)
    (permissiveRootAwareCandidates parameter input table right candidates)
    leftResult rightResult hresult
  intro nextLeft nextRight hnext
  rcases hnext with ⟨hnextState, hremaining, hvalue, htable⟩
  simpa only [observe, hremaining, hvalue] using
    hrecursive nextLeft.value.1
      (permissiveRootAwareCandidates parameter input table left candidates)
      (permissiveRootAwareCandidates parameter input table right candidates)
      nextLeft.state nextRight.state nextLeft.remaining nextLeft.value.2 hcandidates hnextState

set_option maxHeartbeats 400000 in
set_option maxRecDepth 10000 in
theorem relTriple_permissiveRootAwareHashStep_of_stateRel
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (table : OtsSecretIndex → HashOutput)
    (hrecursive : ∀ output candidates rightCandidates left right fuel cache,
      candidates = rightCandidates → PermissiveStateRel left right →
      RelTriple
        (permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret (next output)
          candidates left fuel table cache)
        (permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret (next output)
          rightCandidates right fuel table cache)
        (EqRel (Option Probe)))
    (candidates : List Probe)
    (left right : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache)
    (hstate : PermissiveStateRel left right) :
    RelTriple
      (permissiveRootAwareHashStep ordinal parameter input
        (fun output laterCandidates nextState remaining laterTable nextCache =>
          permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret (next output)
            laterCandidates nextState remaining laterTable nextCache)
        candidates left fuel table cache)
      (permissiveRootAwareHashStep ordinal parameter input
        (fun output laterCandidates nextState remaining laterTable nextCache =>
          permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret (next output)
            laterCandidates nextState remaining laterTable nextCache)
        candidates right fuel table cache)
      (EqRel (Option Probe)) := by
  unfold permissiveRootAwareHashStep
  apply relTriple_selectPermissiveOrdinal ordinal
    (permissiveRootAwareCandidates parameter input table left candidates)
    (permissiveRootAwareCandidates parameter input table right candidates)
  · exact permissiveRootAwareCandidates_eq_of_stateRel parameter input table candidates hstate
  · exact relTriple_permissiveRootAwareHashContinue_of_stateRel ordinal parameter root
      ftsSecret input next table hrecursive candidates left right fuel cache hstate

theorem relTriple_permissiveRootAwareOrdinalSelection_hash
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (table : OtsSecretIndex → HashOutput)
    (hrecursive : ∀ output candidates rightCandidates left right fuel cache,
      candidates = rightCandidates → PermissiveStateRel left right →
      RelTriple
        (permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret (next output)
          candidates left fuel table cache)
        (permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret (next output)
          rightCandidates right fuel table cache)
        (EqRel (Option Probe)))
    (candidates : List Probe)
    (left right : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache)
    (hstate : PermissiveStateRel left right) :
    RelTriple
      (permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        candidates left fuel table cache)
      (permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        candidates right fuel table cache)
      (EqRel (Option Probe)) := by
  rw [permissiveRootAwareOrdinalSelection, OracleComp.construct_query_bind,
    permissiveRootAwareOrdinalSelection, OracleComp.construct_query_bind]
  by_cases hselected : ordinal < candidates.length
  · simp only [hselected, ↓reduceDIte]
    exact relTriple_pure_pure rfl
  · simp only [hselected, ↓reduceDIte]
    exact relTriple_permissiveRootAwareHashStep_of_stateRel ordinal parameter root ftsSecret
      input next table hrecursive candidates left right fuel cache hstate

set_option maxHeartbeats 400000 in
set_option maxRecDepth 2000 in
theorem relTriple_permissiveRootAwareOrdinalSelection_of_stateRel_aux
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates rightCandidates : List Probe)
    (left right : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcandidates : candidates = rightCandidates)
    (hstate : PermissiveStateRel left right) :
    RelTriple
      (permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
        candidates left fuel table cache)
      (permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
        rightCandidates right fuel table cache)
      (EqRel (Option Probe)) := by
  induction computation using OracleComp.inductionOn generalizing
      candidates rightCandidates left right fuel cache with
  | pure value =>
      subst rightCandidates
      simp only [permissiveRootAwareOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length <;>
        simp only [hselected, ↓reduceDIte] <;> exact relTriple_pure_pure rfl
  | query_bind query next ih =>
      subst rightCandidates
      rw [permissiveRootAwareOrdinalSelection, OracleComp.construct_query_bind,
        permissiveRootAwareOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure rfl
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                let leftObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe → ProbComp (Option Probe) :=
                  fun nextState remaining output nextCache laterCandidates ↦
                    permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret
                      (next output) laterCandidates nextState remaining table nextCache
                let rightObserve := leftObserve
                apply relTriple_bind
                  (relTriple_runPermissiveFromTable_of_stateRel
                    ((splitUniformImpl n).run cache) left right fuel table hstate)
                intro leftResult rightResult hresult
                apply relTriple_finishPermissivePrivateOrdinalSelection_eq leftObserve
                  rightObserve candidates candidates leftResult rightResult hresult
                intro nextLeft nextRight hnext
                rcases hnext with ⟨hnextState, hremaining, hvalue, htable⟩
                simpa only [leftObserve, rightObserve, hremaining, hvalue] using
                  ih nextLeft.value.1 candidates candidates nextLeft.state nextRight.state
                    nextLeft.remaining nextLeft.value.2 rfl hnextState
            | inr input =>
                simpa only [permissiveRootAwareOrdinalSelection,
                  OracleComp.construct_query_bind, hselected, ↓reduceDIte] using
                  relTriple_permissiveRootAwareOrdinalSelection_hash ordinal parameter root
                    ftsSecret input next table ih candidates left right fuel cache hstate
        | inr message =>
            let observe : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe → ProbComp (Option Probe) :=
              fun nextState remaining output nextCache laterCandidates ↦
                permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret
                  (next output) laterCandidates nextState remaining table nextCache
            apply relTriple_bind
              (relTriple_runPermissiveFromTable_of_stateRel
                ((maskedSign parameter root ftsSecret message).run cache)
                left right fuel table hstate)
            intro leftResult rightResult hresult
            apply relTriple_finishPermissivePrivateOrdinalSelection_eq observe observe candidates
              candidates leftResult rightResult hresult
            intro nextLeft nextRight hnext
            rcases hnext with ⟨hnextState, hremaining, hvalue, htable⟩
            simpa only [observe, hremaining, hvalue] using
              ih nextLeft.value.1 candidates candidates nextLeft.state nextRight.state
                nextLeft.remaining nextLeft.value.2 rfl hnextState

noncomputable def permissiveRootAwareSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (rootResult : CleanRunResult (Digest × SplitHashCache)) : ProbComp (Option Probe) :=
  permissiveRootAwareOrdinalSelection ordinal parameter rootResult.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    rootResult.state rootResult.remaining rootResult.table rootResult.value.2

noncomputable def permissiveRootAwareOrdinalSelectionExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) : ProbComp (Option Probe) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure none
  | some result =>
      permissiveRootAwareSelectionAfterRootResult ordinal adversary parameter ftsSecret result

noncomputable def optionalProbeLayerRootPosition? : Option Probe → Option Position
  | none => none
  | some candidate => candidateLayerRootPosition? candidate

def MaterializedPermissiveSelectionRel
    (target : Position) : Option Probe → Option Probe → Prop :=
  fun materialized permissive =>
    materializedOrdinalSelectionAt target materialized →
      materializedOrdinalSelectionAt target permissive

theorem relTriple_none_any_materializedPermissiveSelection
    (target : Position) (right : ProbComp (Option Probe)) :
    RelTriple (pure none : ProbComp (Option Probe)) right
      (MaterializedPermissiveSelectionRel target) := by
  have hbase := relTriple_true (pure none : ProbComp (Option Probe)) right
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun value => value = none) (by
        intro value hvalue
        simpa using hvalue)
  apply relTriple_post_mono hsupported
  intro left right hrelation
  rw [hrelation.2]
  simp [MaterializedPermissiveSelectionRel, materializedOrdinalSelectionAt]

theorem relTriple_finishMaterializedPermissiveSelection
    (target : Position)
    (leftObserve : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp (Option Probe))
    (rightObserve : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp (Option Probe))
    (candidates : List Probe)
    (left right : Option (CleanRunResult (α × SplitHashCache)))
    (hrelation : CleanPermissiveRel left right)
    (hrecursive : ∀ result : CleanRunResult (α × SplitHashCache),
      RelTriple
        (leftObserve result.state result.remaining result.value.1 result.value.2 candidates)
        (rightObserve result.state result.remaining result.value.1 result.value.2 candidates)
        (MaterializedPermissiveSelectionRel target)) :
    RelTriple
      (finishMaterializedPrivateOrdinalSelection
        (continueMaterializedPrivateOrdinalSelection target leftObserve) candidates left)
      (finishPermissivePrivateOrdinalSelection rightObserve candidates right)
      (MaterializedPermissiveSelectionRel target) := by
  cases left with
  | none => exact relTriple_none_any_materializedPermissiveSelection target _
  | some left =>
      have hright : right = some left := hrelation
      subst right
      by_cases hrevealed : Coordinate.position target ∈ left.state.revealed
      · simp only [finishMaterializedPrivateOrdinalSelection,
          continueMaterializedPrivateOrdinalSelection, finishPermissivePrivateOrdinalSelection,
          hrevealed, ↓reduceIte]
        exact relTriple_none_any_materializedPermissiveSelection target _
      · simp only [finishMaterializedPrivateOrdinalSelection,
          continueMaterializedPrivateOrdinalSelection, finishPermissivePrivateOrdinalSelection,
          hrevealed, ↓reduceIte]
        exact hrecursive left

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_materializedRootAware_permissiveRootAwareOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    RelTriple
      (materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot target
        leftRoot rightRoot ftsSecret computation candidates state fuel table cache)
      (permissiveRootAwareOrdinalSelection ordinal parameter publicRoot ftsSecret computation
        candidates state fuel table cache)
      (MaterializedPermissiveSelectionRel target) := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      simp only [materializedActualRootAwareAvoidingOrdinalSelection,
        materializedRootAwareAvoidingOrdinalSelection,
        permissiveRootAwareOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length <;>
        simp only [hselected, ↓reduceDIte] <;>
        exact relTriple_pure_pure (fun h => h)
  | query_bind query next ih =>
      rw [materializedActualRootAwareAvoidingOrdinalSelection,
        materializedRootAwareAvoidingOrdinalSelection, OracleComp.construct_query_bind,
        permissiveRootAwareOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure (fun h => h)
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                let leftObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe → ProbComp (Option Probe) :=
                  fun nextState remaining output nextCache laterCandidates =>
                    materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter
                      publicRoot target leftRoot rightRoot ftsSecret (next output) laterCandidates
                      nextState remaining table nextCache
                let rightObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe → ProbComp (Option Probe) :=
                  fun nextState remaining output nextCache laterCandidates =>
                    permissiveRootAwareOrdinalSelection ordinal parameter publicRoot ftsSecret
                      (next output) laterCandidates nextState remaining table nextCache
                apply relTriple_bind
                  (relTriple_runCleanFromTable_runPermissiveFromTable
                    ((splitUniformImpl n).run cache) state fuel table)
                intro leftResult rightResult hresult
                apply relTriple_finishMaterializedPermissiveSelection target leftObserve
                  rightObserve candidates leftResult rightResult hresult
                intro result
                simpa [leftObserve, rightObserve] using
                  ih result.value.1 candidates result.state result.remaining result.value.2
            | inr input =>
                simp only [permissiveRootAwareHashStep, selectPermissiveOrdinal,
                  permissiveRootAwareHashContinue, permissiveRootAwareCandidates,
                  permissiveRootAwarePublicAction, permissiveRootAwarePublicActionWithPlan,
                  permissiveRootAwarePlan]
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
                  exact relTriple_pure_pure (fun h => h)
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
                    let leftObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe → ProbComp (Option Probe) :=
                      fun nextState remaining output nextCache laterCandidates =>
                        materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter
                          publicRoot target leftRoot rightRoot ftsSecret (next output)
                          laterCandidates nextState remaining table nextCache
                    let rightObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe → ProbComp (Option Probe) :=
                      fun nextState remaining output nextCache laterCandidates =>
                        permissiveRootAwareOrdinalSelection ordinal parameter publicRoot ftsSecret
                          (next output) laterCandidates nextState remaining table nextCache
                    let inner :=
                      (probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                        plan).run cache
                    apply relTriple_bind
                      (relTriple_runCleanFromTable_runPermissiveFromTable inner state fuel table)
                    intro leftResult rightResult hresult
                    apply relTriple_finishMaterializedPermissiveSelection target leftObserve
                      rightObserve nextCandidates leftResult rightResult hresult
                    intro result
                    simpa [leftObserve, rightObserve] using
                      ih result.value.1 nextCandidates result.state result.remaining result.value.2
                  · have hsafeActual : ¬RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    exact relTriple_none_any_materializedPermissiveSelection target _
        | inr message =>
            let leftObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe → ProbComp (Option Probe) :=
              fun nextState remaining output nextCache laterCandidates =>
                materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot
                  target leftRoot rightRoot ftsSecret (next output) laterCandidates nextState
                  remaining table nextCache
            let rightObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe → ProbComp (Option Probe) :=
              fun nextState remaining output nextCache laterCandidates =>
                permissiveRootAwareOrdinalSelection ordinal parameter publicRoot ftsSecret
                  (next output) laterCandidates nextState remaining table nextCache
            let inner := (maskedSign parameter publicRoot ftsSecret message).run cache
            apply relTriple_bind
              (relTriple_runCleanFromTable_runPermissiveFromTable inner state fuel table)
            intro leftResult rightResult hresult
            apply relTriple_finishMaterializedPermissiveSelection target leftObserve rightObserve
              candidates leftResult rightResult hresult
            intro result
            simpa [leftObserve, rightObserve] using
              ih result.value.1 candidates result.state result.remaining result.value.2

noncomputable def sampledHighInstalledPermissiveRootAwareSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Digest × Option Probe) := do
  let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
  let leftRoot ← ($ᵗ Digest : ProbComp Digest)
  let output := fun root => rootOutputOfParts root high
  let context : DeferredContext := directDeferredContext rootResult.state
  let rootContext :=
    { context with values := context.values.install target (output leftRoot) }
  let selection ← permissiveRootAwareOrdinalSelection ordinal parameter rootResult.value.1
    ftsSecret (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (materializedDeferredState rootContext) rootResult.remaining rootResult.table
    (rootInstalledCache target output rootResult.value.2 leftRoot)
  pure (leftRoot, selection)

theorem relTriple_sampledHigh_materializedRootAwareProduction_installedPermissive
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    RelTriple
      (sampledHighMaterializedRootAwareSelectionProductionAfterRootResult ordinal adversary
        parameter ftsSecret target rootResult)
      (sampledHighInstalledPermissiveRootAwareSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult)
      (fun left right => left.1 = right.1 ∧
        MaterializedPermissiveSelectionRel target left.2 right.2) := by
  unfold sampledHighMaterializedRootAwareSelectionProductionAfterRootResult
    sampledHighInstalledPermissiveRootAwareSelectionAfterRootResult
  apply relTriple_bind (relTriple_refl ($ᵗ RootOutputHigh : ProbComp RootOutputHigh))
  intro leftHigh rightHigh hhigh
  subst rightHigh
  apply relTriple_bind (relTriple_refl ($ᵗ Digest : ProbComp Digest))
  intro leftRoot rightRoot hroot
  subst rightRoot
  let output := fun root => rootOutputOfParts root leftHigh
  let context : DeferredContext := directDeferredContext rootResult.state
  let rootContext :=
    { context with values := context.values.install target (output leftRoot) }
  apply relTriple_bind
    (relTriple_materializedRootAware_permissiveRootAwareOrdinalSelection ordinal parameter
      rootResult.value.1 target leftRoot leftRoot ftsSecret
      (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
      (materializedDeferredState rootContext) rootResult.remaining rootResult.table
      (rootInstalledCache target output rootResult.value.2 leftRoot))
  intro leftSelection rightSelection hselection
  exact relTriple_pure_pure ⟨rfl, hselection⟩

theorem probEvent_materializedRootAwareProduction_le_installedPermissive
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    Pr[fun result => materializedOrdinalSelectionAt target result.2 |
        sampledHighMaterializedRootAwareSelectionProductionAfterRootResult ordinal adversary
          parameter ftsSecret target rootResult] ≤
      Pr[fun result => materializedOrdinalSelectionAt target result.2 |
        sampledHighInstalledPermissiveRootAwareSelectionAfterRootResult ordinal adversary
          parameter ftsSecret target rootResult] := by
  apply probEvent_le_of_relTriple
    (relTriple_sampledHigh_materializedRootAwareProduction_installedPermissive ordinal adversary
      parameter ftsSecret target rootResult)
  intro left right hrelation hleft
  exact hrelation.2 hleft

noncomputable def directDetailedRootAwarePrivateOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option PrivateOrdinalSelection) := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List Probe → DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        SplitHashCache → ProbComp (Option PrivateOrdinalSelection))
    (fun _value candidates context _fuel _table _cache =>
      pure (selectedPrivateOrdinal? ordinal candidates context))
    (fun query _next recursivelyRun candidates context fuel table cache =>
      if hselected : ordinal < candidates.length then
        pure (some ⟨candidates.get ⟨ordinal, hselected⟩, context, candidates⟩)
      else
        match query with
        | .inl (.inl n) =>
            runDirectResolvedWitnessFromTable context fuel table ((splitUniformImpl n).run cache) >>=
              finishDirectPrivateOrdinalSelection
                (canonicalizeDirectPrivateOrdinalSelection table
                  (fun nextContext remaining value laterCandidates =>
                    recursivelyRun value.1 laterCandidates nextContext remaining table value.2))
                candidates
        | .inl (.inr input) =>
            let plan := purePlanProbingHashQuery parameter input context.state
            let nextCandidates := appendPlannedCandidate candidates
              (rootAwareCandidateForPlan? parameter input plan)
            if hnextSelected : ordinal < nextCandidates.length then
              pure (some ⟨nextCandidates.get ⟨ordinal, hnextSelected⟩, context,
                nextCandidates⟩)
            else
              runDirectResolvedWitnessFromTable context fuel table
                  ((probingHashQueryAfterRootAwarePlan parameter input plan).run cache) >>=
                finishDirectPrivateOrdinalSelection
                  (canonicalizeDirectPrivateOrdinalSelection table
                    (fun nextContext remaining value laterCandidates =>
                      recursivelyRun value.1 laterCandidates nextContext remaining table value.2))
                  nextCandidates
        | .inr message =>
            runDirectResolvedWitnessFromTable context fuel table
                ((maskedSign parameter root ftsSecret message).run cache) >>=
              finishDirectPrivateOrdinalSelection
                (canonicalizeDirectPrivateOrdinalSelection table
                  (fun nextContext remaining value laterCandidates =>
                    recursivelyRun value.1 laterCandidates nextContext remaining table value.2))
                candidates)
    computation candidates context fuel table cache

theorem directDetailedRootAwarePrivateOrdinalSelection_eq_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hselected : ordinal < candidates.length) :
    directDetailedRootAwarePrivateOrdinalSelection ordinal parameter root ftsSecret computation
        candidates context fuel table cache =
      pure (some ⟨candidates.get ⟨ordinal, hselected⟩, context, candidates⟩) := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedRootAwarePrivateOrdinalSelection, OracleComp.construct_pure]
      simp [selectedPrivateOrdinal?, hselected]
  | query_bind query next ih =>
      rw [directDetailedRootAwarePrivateOrdinalSelection, OracleComp.construct_query_bind]
      simp only [hselected, ↓reduceDIte]

noncomputable def directRootAwareSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Option PrivateOrdinalSelection) :=
  directDetailedRootAwarePrivateOrdinalSelection ordinal parameter rootResult.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (canonicalizeMaterializedValues rootResult.table
      (directDeferredContext rootResult.state))
    rootResult.remaining rootResult.table rootResult.value.2

noncomputable def directRootAwareOrdinalSelectionExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (Option PrivateOrdinalSelection) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure none
  | some result =>
      directRootAwareSelectionAfterRootResult ordinal adversary parameter ftsSecret result

noncomputable def privateOrdinalSelectionLayerRootPosition? :
    Option PrivateOrdinalSelection → Option Position
  | none => none
  | some selection => candidateLayerRootPosition? selection.candidate

noncomputable def privateOrdinalSelectionUnrevealedLayerRootPosition? :
    Option PrivateOrdinalSelection → Option Position
  | none => none
  | some selection =>
      match candidateLayerRootPosition? selection.candidate with
      | none => none
      | some target =>
          if Coordinate.position target ∈ selection.context.state.revealed then none
          else some target

theorem materializedOrdinalSelectionAt_iff_layerRootPosition
    (target : Position) (hroot : IsLayerRoot target)
    (selection : Option PrivateOrdinalSelection) :
    materializedOrdinalSelectionAt target (selection.map PrivateOrdinalSelection.candidate) ↔
      privateOrdinalSelectionLayerRootPosition? selection = some target := by
  cases selection with
  | none => simp [materializedOrdinalSelectionAt, privateOrdinalSelectionLayerRootPosition?]
  | some selection =>
      simp only [Option.map_some, privateOrdinalSelectionLayerRootPosition?]
      rw [candidateLayerRootPosition?_eq_some_iff]
      simp [materializedOrdinalSelectionAt, hroot]

theorem privateOrdinalSelectionUnrevealedLayerRootPosition?_eq_some_iff
    (target : Position) (selection : Option PrivateOrdinalSelection) :
    privateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target ↔
      ∃ selected, selection = some selected ∧
        candidateLayerRootPosition? selected.candidate = some target ∧
        Coordinate.position target ∉ selected.context.state.revealed := by
  cases selection with
  | none => simp [privateOrdinalSelectionUnrevealedLayerRootPosition?]
  | some selected =>
      simp only [privateOrdinalSelectionUnrevealedLayerRootPosition?]
      cases hposition : candidateLayerRootPosition? selected.candidate with
      | none => simp [hposition]
      | some position =>
          by_cases hrevealed : Coordinate.position position ∈ selected.context.state.revealed
          · simp only [hrevealed, ↓reduceIte]
            constructor
            · intro hnone
              contradiction
            · rintro ⟨other, heq, htarget, hunrevealed⟩
              cases heq
              have hpositionTarget : position = target := by
                rw [hposition] at htarget
                exact Option.some.inj htarget
              subst target
              exact False.elim (hunrevealed hrevealed)
          · simp only [hrevealed, ↓reduceIte, Option.some.injEq]
            constructor
            · intro heq
              subst position
              exact ⟨selected, rfl, hposition, hrevealed⟩
            · rintro ⟨other, heq, htarget, hunrevealed⟩
              cases heq
              rw [hposition] at htarget
              exact Option.some.inj htarget

theorem privateOrdinalSelectionUnrevealedLayerRootPosition?_eq_some_of_candidate
    {target : Position} {selection : PrivateOrdinalSelection}
    (hcandidate : ∃ root, selection.candidate = ⟨.position target, root⟩)
    (hroot : IsLayerRoot target)
    (hunrevealed : Coordinate.position target ∉ selection.context.state.revealed) :
    privateOrdinalSelectionUnrevealedLayerRootPosition? (some selection) = some target := by
  rw [privateOrdinalSelectionUnrevealedLayerRootPosition?_eq_some_iff]
  refine ⟨selection, rfl, ?_, hunrevealed⟩
  rw [candidateLayerRootPosition?_eq_some_iff]
  obtain ⟨root, hcandidate⟩ := hcandidate
  exact ⟨congrArg Probe.coordinate hcandidate, hroot⟩

theorem probEvent_of_rootAware_selection_position_fibers
    (run : ProbComp (Option PrivateOrdinalSelection)) (event : Option PrivateOrdinalSelection → Prop)
    (epsilon : ENNReal)
    (hnone : ∀ selection, event selection →
      privateOrdinalSelectionUnrevealedLayerRootPosition? selection ≠ none)
    (hfiber : ∀ target,
      Pr[fun selection => event selection ∧
          privateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target | run] ≤
        Pr[fun selection =>
          privateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target | run] *
            epsilon) :
    Pr[event | run] ≤ epsilon := by
  apply probEvent_le_of_uniform_weighted_fibers run event
    privateOrdinalSelectionUnrevealedLayerRootPosition? epsilon
  intro target?
  cases target? with
  | none =>
      have hzero : Pr[fun selection => event selection ∧
          privateOrdinalSelectionUnrevealedLayerRootPosition? selection = none | run] = 0 := by
        apply probEvent_eq_zero
        intro selection _hselection hevent
        exact hnone selection hevent.1 hevent.2
      rw [hzero]
      exact zero_le
  | some target => exact hfiber target

end SphincsSecurity.Concrete.OtsProbeSimulation
