import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionInitial

/-!
# Root-selection boundary

The failure-retaining materialized prefix is averaged over the same top-root result and root-output
parts as the exchangeable optional prefix. Its selected branch projects to that optional prefix,
while its failure branch remains explicit for the shared clean-finalization charge.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

set_option maxRecDepth 100000 in
theorem pending_subset_of_done_runRaw_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state finalState : LazyRevealProbe.State Coordinate) (fuel remaining : Nat)
    (value : α)
    (hprobeFree : computation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining value ∈
      support (LazyRevealProbe.runRaw state fuel computation)) :
    finalState.pending ⊆ state.pending := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure output =>
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl⟩
      exact Finset.Subset.rfl
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hprobeFree
      cases query with
      | uniform n =>
          rw [LazyRevealProbe.runRaw_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output state fuel (hprobeFree.2 output) htail
      | hashOutput =>
          rw [LazyRevealProbe.runRaw_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output state fuel (hprobeFree.2 output) htail
      | ensure coordinate =>
          rw [LazyRevealProbe.runRaw_ensure_query_bind] at hresult
          exact ih () (state.ensure coordinate) fuel (hprobeFree.2 ()) hresult
      | probe coordinate candidate =>
          simp [LazyRevealProbe.IsProbe] at hprobeFree
      | peek coordinate =>
          rw [LazyRevealProbe.runRaw_peek_query_bind] at hresult
          exact ih (state.values coordinate) state fuel (hprobeFree.2 _) hresult
      | publish coordinate =>
          rw [LazyRevealProbe.runRaw_publish_query_bind] at hresult
          exact ih () (state.publish coordinate) fuel (hprobeFree.2 ()) hresult
      | reveal coordinate =>
          rw [LazyRevealProbe.runRaw_reveal_query_bind] at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              simp only [hvalue] at hresult
              exact ih output state fuel (hprobeFree.2 output) hresult
          | none =>
              simp only [hvalue, mem_support_bind_iff] at hresult
              obtain ⟨output, _houtput, htail⟩ := hresult
              by_cases hhit : state.hitAt coordinate output
              · simp [hhit] at htail
              · simp only [hhit, ↓reduceIte] at htail
                exact (ih output (state.materialize coordinate output) fuel
                  (hprobeFree.2 output) htail).trans (Finset.filter_subset _ _)

attribute [local irreducible] maskedPublishedTreeRoot

theorem pending_eq_empty_of_mem_runCleanFromTable_maskedPublishedTreeRoot
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : CleanRunResult (Digest × SplitHashCache))
    (hresult : some result ∈ support
      (runCleanFromTable (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    result.state.pending = ∅ := by
  have hraw := mem_support_runRaw_done_of_mem_runCleanFromTable_some
    (maskedPublishedTreeRoot.run emptySplitHashCache)
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table result hresult
  have hsubset := pending_subset_of_done_runRaw_of_probeFree
    (maskedPublishedTreeRoot.run emptySplitHashCache)
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) result.state fuel
    result.remaining result.value (maskedPublishedTreeRoot_probeFree emptySplitHashCache) hraw
  simpa [LazyRevealProbe.State.empty] using hsubset

theorem rootContext_invariants_of_mem_runCleanFromTable
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (high : RootOutputHigh) (leftRoot : Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : CleanRunResult (Digest × SplitHashCache))
    (hresult : some result ∈ support
      (runCleanFromTable (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    let context : DeferredContext :=
      { directDeferredContext result.state with
        values := (directDeferredContext result.state).values.install target
          (rootOutputOfParts leftRoot high) }
    context.Valid ∧ DeferredCompletable result.table context ∧ PublishedValues result.state := by
  let output := rootOutputOfParts leftRoot high
  let context : DeferredContext :=
    { directDeferredContext result.state with
      values := (directDeferredContext result.state).values.install target output }
  have hpending := pending_eq_empty_of_mem_runCleanFromTable_maskedPublishedTreeRoot
    fuel table result hresult
  have habsent := target_absent_of_mem_runCleanFromTable_maskedPublishedTreeRoot target hroot
    hparent fuel table result hresult
  have hvalid : context.Valid := by
    constructor
    · intro position existing hvalue
      by_cases heq : position = target
      · subst position
        have hvalue' : result.state.values (.position target) = some existing := by
          simpa [context, directDeferredContext] using hvalue
        rw [habsent.1] at hvalue'
        contradiction
      · simpa [context, directDeferredContext, directDeferredValues,
          DeferredStructuralValues.install, heq] using hvalue
    · intro coordinate existing hvalue
      exact not_hitAt_of_pending_eq_empty context coordinate existing (by
        simpa [context, directDeferredContext] using hpending)
  have hstartsResult := startTableAgrees_of_mem_runCleanFromTable
    (maskedPublishedTreeRoot.run emptySplitHashCache)
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (startTableAgrees_empty table) result hresult
  have hprivate : ¬PrivateStructuralHit context := by
    rintro ⟨position, existing, _hhidden, _hvalue, hhit⟩
    exact not_hitAt_of_pending_eq_empty context (.position position) existing (by
      simpa [context, directDeferredContext] using hpending) hhit
  have hstart : ¬MissingChainStartHit table context := by
    rintro ⟨index, _hvalue, hhit⟩
    exact not_hitAt_of_pending_eq_empty context index.coordinate (table index) (by
      simpa [context, directDeferredContext] using hpending) hhit
  have hcard : context.state.pending.card < Fintype.card Digest := by
    rw [show context.state.pending = ∅ by simpa [context, directDeferredContext] using hpending]
    simp
  have hcompletable : DeferredCompletable result.table context := by
    rw [hstartsResult.1]
    exact deferredCompletable_of_valid_of_no_boundary_hit table context hvalid hstartsResult.2
      hprivate hstart hcard
  have hraw := mem_support_runRaw_done_of_mem_runCleanFromTable_some
    (maskedPublishedTreeRoot.run emptySplitHashCache)
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table result hresult
  have hpublished : PublishedValues result.state :=
    preservesPublishedValues_maskedPublishedTreeRoot
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) emptySplitHashCache fuel
      result.state result.remaining result.value.1 result.value.2 publishedValues_empty hraw
  exact ⟨hvalid, hcompletable, hpublished⟩

noncomputable def directRootSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (high : RootOutputHigh)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (leftRoot _rightRoot : Digest) : ProbComp (Option PrivateOrdinalSelection) :=
  let output := fun root => rootOutputOfParts root high
  let context : DeferredContext := directDeferredContext rootResult.state
  let rootContext :=
    { context with values := context.values.install target (output leftRoot) }
  directDetailedBoundaryPrivateOrdinalSelection ordinal parameter rootResult.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (canonicalizeMaterializedValues rootResult.table rootContext) rootResult.remaining
    rootResult.table (rootInstalledCache target output rootResult.value.2 leftRoot)

noncomputable def materializedRootSelectionOutcomeAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (high : RootOutputHigh)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (leftRoot rightRoot : Digest) : ProbComp MaterializedSelectionOutcome :=
  let output := fun root => rootOutputOfParts root high
  let context : DeferredContext := directDeferredContext rootResult.state
  let rootContext :=
    { context with values := context.values.install target (output leftRoot) }
  materializedActualRootAvoidingOrdinalSelectionOutcome ordinal parameter rootResult.value.1 target
    leftRoot rightRoot ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (materializedDeferredState rootContext) rootResult.remaining rootResult.table
    (rootInstalledCache target output rootResult.value.2 leftRoot)

set_option maxRecDepth 100000 in
theorem relTriple_directRootSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (high : RootOutputHigh)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (leftRoot rightRoot : Digest)
    (hvalid :
      ({ directDeferredContext rootResult.state with
        values := (directDeferredContext rootResult.state).values.install target
          (rootOutputOfParts leftRoot high) } : DeferredContext).Valid)
    (hcompletable : DeferredCompletable rootResult.table
      { directDeferredContext rootResult.state with
        values := (directDeferredContext rootResult.state).values.install target
          (rootOutputOfParts leftRoot high) })
    (hpublished : PublishedValues rootResult.state) :
    RelTriple
      (directRootSelectionAfterRootResult ordinal adversary parameter ftsSecret target high
        rootResult leftRoot rightRoot)
      (materializedRootSelectionOutcomeAfterRootResult ordinal adversary parameter ftsSecret
        target high rootResult leftRoot rightRoot)
      (RootSelectionBridgeRel target (rootOutputOfParts leftRoot high) rightRoot ordinal) := by
  let output := fun root => rootOutputOfParts root high
  let rootContext : DeferredContext :=
    { directDeferredContext rootResult.state with
      values := (directDeferredContext rootResult.state).values.install target (output leftRoot) }
  let materializedContext := materializedDeferredContext rootContext
  have hbase : FinalizationContextLE rootResult.table rootContext materializedContext :=
    finalizationContextLE_materializedDeferredContext hvalid hcompletable
  have hcontext : FinalizationContextLE rootResult.table
      (canonicalizeMaterializedValues rootResult.table rootContext) materializedContext :=
    hbase.canonicalize_left
  have hvalues : LazyRevealProbe.ValuesLE
      (canonicalizeMaterializedValues rootResult.table rootContext).state
      materializedContext.state :=
    (valuesLE_canonicalizeMaterializedValues_left rootResult.table rootContext
      hbase.view.leftStarts hpublished).trans
        (valuesLE_materializedDeferredState rootContext)
  have hrel := relTriple_directRootSelection_materializedOutcome ordinal parameter
    rootResult.value.1 target (output leftRoot) rightRoot ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (canonicalizeMaterializedValues rootResult.table rootContext) materializedContext
    rootResult.remaining rootResult.remaining rootResult.table
    (rootInstalledCache target output rootResult.value.2 leftRoot)
    (rootInstalledCache target output rootResult.value.2 leftRoot)
    hcontext le_rfl rfl rfl hvalues hpublished.to_canonicalizedMaterializedValues rfl
    (canonicalizeMaterializedValues_canonical rootResult.table rootContext
      hvalid.valuesConsistent)
    (CandidatesAvoidRoots.nil target (truncateHash (output leftRoot)) rightRoot)
  simpa [directRootSelectionAfterRootResult,
    materializedRootSelectionOutcomeAfterRootResult, output, rootContext, materializedContext,
    materializedDeferredContext, directDeferredContext]
    using hrel

noncomputable def sampledHighDirectRootSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (HashOutput × Digest × Option PrivateOrdinalSelection) := do
  let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
  let leftRoot ← ($ᵗ Digest : ProbComp Digest)
  let rightRoot ← ($ᵗ Digest : ProbComp Digest)
  let selection ← directRootSelectionAfterRootResult ordinal adversary parameter ftsSecret
    target high rootResult leftRoot rightRoot
  pure (rootOutputOfParts leftRoot high, rightRoot, selection)

theorem relTriple_materializedRootSelectionOutcomeAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (high : RootOutputHigh)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (leftRoot rightRoot : Digest) :
    RelTriple
      (materializedRootSelectionOutcomeAfterRootResult ordinal adversary parameter ftsSecret
        target high rootResult leftRoot rightRoot)
      (materializedRootSelectionAfterRootResult ordinal adversary parameter ftsSecret target high
        rootResult leftRoot rightRoot)
      (MaterializedOutcomeOptionRel target leftRoot) := by
  unfold materializedRootSelectionOutcomeAfterRootResult
    materializedRootSelectionAfterRootResult
  exact relTriple_materializedActualOutcome_optionalSelection ordinal parameter rootResult.value.1
    target leftRoot rightRoot ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (materializedDeferredState
      { directDeferredContext rootResult.state with
        values := (directDeferredContext rootResult.state).values.install target
          (rootOutputOfParts leftRoot high) })
    rootResult.remaining rootResult.table
    (rootInstalledCache target (fun root => rootOutputOfParts root high) rootResult.value.2 leftRoot)

noncomputable def sampledHighMaterializedRootSelectionOutcomeAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Digest × Digest × MaterializedSelectionOutcome) := do
  let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
  let leftRoot ← ($ᵗ Digest : ProbComp Digest)
  let rightRoot ← ($ᵗ Digest : ProbComp Digest)
  let outcome ← materializedRootSelectionOutcomeAfterRootResult ordinal adversary parameter
    ftsSecret target high rootResult leftRoot rightRoot
  pure (leftRoot, rightRoot, outcome)

set_option maxRecDepth 100000 in
theorem relTriple_sampledHigh_directRootSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hresult : some rootResult ∈ support
      (runCleanFromTable (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    RelTriple
      (sampledHighDirectRootSelectionAfterRootResult ordinal adversary parameter ftsSecret target
        rootResult)
      (sampledHighMaterializedRootSelectionOutcomeAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult)
      (fun left right =>
        truncateHash left.1 = right.1 ∧ left.2.1 = right.2.1 ∧
          RootSelectionBridgeRel target left.1 left.2.1 ordinal left.2.2 right.2.2) := by
  unfold sampledHighDirectRootSelectionAfterRootResult
    sampledHighMaterializedRootSelectionOutcomeAfterRootResult
  apply relTriple_bind (relTriple_refl ($ᵗ RootOutputHigh : ProbComp RootOutputHigh))
  intro leftHigh rightHigh hhigh
  subst rightHigh
  apply relTriple_bind (relTriple_refl ($ᵗ Digest : ProbComp Digest))
  intro leftRoot rightRoot hleftRoot
  subst rightRoot
  apply relTriple_bind (relTriple_refl ($ᵗ Digest : ProbComp Digest))
  intro leftComparison rightComparison hcomparison
  subst rightComparison
  obtain ⟨hvalid, hcompletable, hpublished⟩ :=
    rootContext_invariants_of_mem_runCleanFromTable target hroot hparent leftHigh leftRoot fuel
      table rootResult hresult
  apply relTriple_bind
    (relTriple_directRootSelectionAfterRootResult ordinal adversary parameter ftsSecret target
      leftHigh rootResult leftRoot leftComparison hvalid hcompletable hpublished)
  intro leftSelection rightOutcome hselection
  exact relTriple_pure_pure
    ⟨truncateHash_rootOutputOfParts leftRoot leftHigh, rfl, hselection⟩

set_option maxRecDepth 100000 in
theorem relTriple_sampledHigh_materializedRootSelectionOutcomeAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    RelTriple
      (sampledHighMaterializedRootSelectionOutcomeAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult)
      (sampledHighMaterializedRootSelectionAfterRootResult ordinal adversary parameter ftsSecret
        target rootResult)
      (fun left right =>
        left.1 = right.1 ∧ left.2.1 = right.2.1 ∧
          MaterializedOutcomeOptionRel target left.1 left.2.2 right.2.2) := by
  unfold sampledHighMaterializedRootSelectionOutcomeAfterRootResult
    sampledHighMaterializedRootSelectionAfterRootResult
  apply relTriple_bind (relTriple_refl ($ᵗ RootOutputHigh : ProbComp RootOutputHigh))
  intro leftHigh rightHigh hhigh
  subst rightHigh
  apply relTriple_bind (relTriple_refl ($ᵗ Digest : ProbComp Digest))
  intro leftRoot rightRoot hroot
  subst rightRoot
  apply relTriple_bind (relTriple_refl ($ᵗ Digest : ProbComp Digest))
  intro leftComparison rightComparison hcomparison
  subst rightComparison
  apply relTriple_bind
    (relTriple_materializedRootSelectionOutcomeAfterRootResult ordinal adversary parameter
      ftsSecret target leftHigh rootResult leftRoot leftComparison)
  intro leftOutcome rightSelection hselection
  exact relTriple_pure_pure ⟨rfl, rfl, hselection⟩

theorem probEvent_sampledHigh_materializedRootSelectionOutcome_match_le
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    Pr[fun result => result.2.2.Matches target result.1 |
        sampledHighMaterializedRootSelectionOutcomeAfterRootResult ordinal adversary parameter
          ftsSecret target rootResult] ≤
      Pr[fun result => materializedOrdinalSelectionMatches target result.1 result.2.2 |
        sampledHighMaterializedRootSelectionAfterRootResult ordinal adversary parameter ftsSecret
          target rootResult] := by
  apply probEvent_le_of_relTriple
    (relTriple_sampledHigh_materializedRootSelectionOutcomeAfterRootResult ordinal adversary
      parameter ftsSecret target rootResult)
  intro left right hrel hmatch
  rw [← hrel.1]
  exact hrel.2.2 hmatch

noncomputable def materializedRootOrdinalOutcomeExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (Digest × Digest × MaterializedSelectionOutcome) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure (0, 0, .failed)
  | some result =>
      sampledHighMaterializedRootSelectionOutcomeAfterRootResult ordinal adversary parameter
        ftsSecret target result

noncomputable def directRootOrdinalSelectionExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (HashOutput × Digest × Option PrivateOrdinalSelection) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure (hashOutputOfDigest 0, 0, none)
  | some result =>
      sampledHighDirectRootSelectionAfterRootResult ordinal adversary parameter ftsSecret target
        result

set_option maxRecDepth 100000 in
theorem relTriple_directRootOrdinalSelectionExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (directRootOrdinalSelectionExperimentAfterTable ordinal adversary parameter ftsSecret target
        fuel table)
      (materializedRootOrdinalOutcomeExperimentAfterTable ordinal adversary parameter ftsSecret
        target fuel table)
      (fun left right =>
        truncateHash left.1 = right.1 ∧ left.2.1 = right.2.1 ∧
          RootSelectionBridgeRel target left.1 left.2.1 ordinal left.2.2 right.2.2) := by
  unfold directRootOrdinalSelectionExperimentAfterTable
    materializedRootOrdinalOutcomeExperimentAfterTable
  let rootRun := runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  have hbase := relTriple_refl rootRun
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => result ∈ support rootRun) (fun result hresult => hresult)
  apply relTriple_bind hsupported
  intro leftRootResult rightRootResult hrootResult
  have heq : leftRootResult = rightRootResult := hrootResult.1
  rw [← heq]
  cases leftRootResult with
  | none =>
      exact relTriple_pure_pure ⟨truncateHash_hashOutputOfDigest 0, rfl,
        rootSelectionBridgeRel_none_left target (hashOutputOfDigest 0) 0 ordinal .failed⟩
  | some result =>
      exact relTriple_sampledHigh_directRootSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target hroot hparent fuel table result hrootResult.2

set_option maxRecDepth 100000 in
theorem relTriple_materializedRootOrdinalOutcomeExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (materializedRootOrdinalOutcomeExperimentAfterTable ordinal adversary parameter ftsSecret
        target fuel table)
      (materializedRootOrdinalMatchExperimentAfterTable ordinal adversary parameter ftsSecret
        target fuel table)
      (fun left right =>
        left.1 = right.1 ∧ left.2.1 = right.2.1 ∧
          MaterializedOutcomeOptionRel target left.1 left.2.2 right.2.2) := by
  unfold materializedRootOrdinalOutcomeExperimentAfterTable
    materializedRootOrdinalMatchExperimentAfterTable
  apply relTriple_bind (relTriple_refl
    (runCleanFromTable
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache)))
  intro leftRootResult rightRootResult hrootResult
  subst rightRootResult
  cases leftRootResult with
  | none =>
      exact relTriple_pure_pure ⟨rfl, rfl, fun hmatch => False.elim hmatch⟩
  | some result =>
      exact relTriple_sampledHigh_materializedRootSelectionOutcomeAfterRootResult ordinal
        adversary parameter ftsSecret target result

theorem probEvent_materializedRootOrdinalOutcome_match_le
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun result => result.2.2.Matches target result.1 |
        materializedRootOrdinalOutcomeExperimentAfterTable ordinal adversary parameter ftsSecret
          target fuel table] ≤
      Pr[fun result => materializedOrdinalSelectionAt target result.2 |
          materializedRootOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target fuel table] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[fun result => materializedOrdinalSelectionMatches target result.1 result.2.2 |
          materializedRootOrdinalMatchExperimentAfterTable ordinal adversary parameter ftsSecret
            target fuel table] := by
      apply probEvent_le_of_relTriple
        (relTriple_materializedRootOrdinalOutcomeExperimentAfterTable ordinal adversary parameter
          ftsSecret target fuel table)
      intro left right hrel hmatch
      rw [← hrel.1]
      exact hrel.2.2 hmatch
    _ ≤ _ := probEvent_materializedRootOrdinalMatchExperimentAfterTable_le_mul ordinal
      adversary parameter ftsSecret target hroot hparent fuel table

end SphincsSecurity.Concrete.OtsProbeSimulation
