import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHiddenRiskBound

/-!
# Local freshness steps

Canonicalization preserves candidate freshness, and a uniform outer query leaves the deferred
context unchanged. These discharge the uniform premise of the one-unit hidden ordinal theorem.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

theorem CandidatePositionsFresh.canonicalize
    {context : DeferredContext} (hfresh : CandidatePositionsFresh context)
    (table : OtsSecretIndex → HashOutput) :
    CandidatePositionsFresh (canonicalizeMaterializedValues table context) := by
  intro position parent hparent hhidden
  have horiginalHidden : Coordinate.position position ∉ context.state.revealed := by
    simpa [canonicalizeMaterializedValues_revealed] using hhidden
  have hpositionFresh := hfresh position parent hparent horiginalHidden
  constructor
  · unfold canonicalizeMaterializedValues publicMaterializedValues
    simp [horiginalHidden]
  · exact hpositionFresh.2

theorem candidatePositionsFresh_uniformStep
    (n : Nat) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Fin (n + 1) × SplitHashCache))
    (hfresh : CandidatePositionsFresh context)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table
        ((splitUniformImpl n).run cache))) :
    CandidatePositionsFresh (canonicalizeMaterializedValues table result.context) := by
  unfold splitUniformImpl at hresult
  rw [StateT.run_liftM, LazyRevealProbe.uniformQuery,
    runDirectResolvedWitnessFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
  obtain ⟨output, _houtput, htail⟩ := hresult
  simp [runDirectResolvedWitnessFromTable] at htail
  subst result
  exact hfresh.canonicalize table

def CoordinateMaterializedPublished
    (coordinate : Coordinate) (state : LazyRevealProbe.State Coordinate) : Prop :=
  state.values coordinate ≠ none → coordinate ∈ state.revealed

def PreservesCoordinateMaterializedPublished
    (coordinate : Coordinate)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache,
    CoordinateMaterializedPublished coordinate state →
    LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
    CoordinateMaterializedPublished coordinate finalState

theorem PreservesCoordinate.to_materializedPublished
    {coordinate : Coordinate}
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (hpreserves : PreservesCoordinate coordinate computation) :
    PreservesCoordinateMaterializedPublished coordinate computation := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  have hsame := hpreserves state cache fuel finalState remaining value finalCache hresult
  intro hvalue
  apply hsame.2.mpr
  apply hvalid
  rwa [hsame.1] at hvalue

theorem PreservesCoordinateMaterializedPublished.bind
    {coordinate : Coordinate}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : PreservesCoordinateMaterializedPublished coordinate left)
    (hnext : ∀ value, PreservesCoordinateMaterializedPublished coordinate (next value)) :
    PreservesCoordinateMaterializedPublished coordinate (left >>= next) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun leftResult => (next leftResult.1).run leftResult.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining leftResult =>
      exact hnext leftResult.1 middleState leftResult.2 middleRemaining finalState remaining
        value finalCache (hleft state cache fuel middleState middleRemaining leftResult.1
          leftResult.2 hvalid hraw) hrest

theorem preservesCoordinateMaterializedPublished_revealOutput_publish
    (coordinate : Coordinate) :
    PreservesCoordinateMaterializedPublished coordinate (do
      let output ← revealCoordinateOutput coordinate
      publishCoordinate coordinate
      pure output) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨revealRaw, hreveal, hrest⟩ := hresult
  cases revealRaw with
  | stopped hit => simp at hrest
  | done revealState revealRemaining revealResult =>
      change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
        support (LazyRevealProbe.runRaw revealState revealRemaining
          ((publishCoordinate coordinate).run revealResult.2 >>= fun publishResult =>
            pure (revealResult.1, publishResult.2))) at hrest
      rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
      obtain ⟨publishRaw, hpublish, hreturn⟩ := hrest
      cases publishRaw with
      | stopped hit => simp at hreturn
      | done publishState publishRemaining publishResult =>
          change LazyRevealProbe.RawResult.done publishState publishRemaining publishResult ∈
            support (LazyRevealProbe.runRaw revealState revealRemaining
              (LazyRevealProbe.publishQuery coordinate >>= fun result =>
                pure (result, revealResult.2))) at hpublish
          rw [LazyRevealProbe.publishQuery,
            LazyRevealProbe.runRaw_publish_query_bind] at hpublish
          simp [LazyRevealProbe.runRaw] at hpublish
          rcases hpublish with ⟨rfl, rfl, rfl, rfl⟩
          simp [LazyRevealProbe.runRaw] at hreturn
          rcases hreturn with ⟨rfl, rfl, rfl, rfl⟩
          intro _hvalue
          simp [LazyRevealProbe.State.publish]

theorem preservesCoordinateMaterializedPublished_resolveKnownInput
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput) :
    PreservesCoordinateMaterializedPublished coordinate
      (resolveKnownInput parameter coordinate input) := by
  unfold resolveKnownInput
  apply ((rawReadOnly_peekTableInput parameter coordinate).preservesCoordinate
    coordinate).to_materializedPublished.bind
  intro known
  cases known with
  | none =>
      exact (preservesCoordinate_splitHashQuery coordinate (.ordinary input)).to_materializedPublished
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        have hpreserves :=
          (preservesCoordinateMaterializedPublished_revealOutput_publish coordinate).bind
            fun output => (preservesCoordinate_modify coordinate fun cache =>
              Function.update cache (.ordinary input)
                (some output)).to_materializedPublished.bind
                fun _ => (preservesCoordinate_pure coordinate output).to_materializedPublished
        simpa only [bind_assoc, pure_bind] using hpreserves
      · simp only [heq, ↓reduceIte]
        exact (preservesCoordinate_splitHashQuery coordinate
          (.ordinary input)).to_materializedPublished

theorem preservesCoordinateMaterializedPublished_executeCandidate
    (coordinate : Coordinate) : ∀ candidate? : Option Probe,
    PreservesCoordinateMaterializedPublished coordinate (executeCandidate? candidate?)
  | none => (preservesCoordinate_pure coordinate ()).to_materializedPublished
  | some candidate => (preservesCoordinate_probe coordinate candidate).to_materializedPublished

theorem preservesCoordinateMaterializedPublished_probingHashQueryAfterPlan
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (coordinate : Coordinate) :
    PreservesCoordinateMaterializedPublished coordinate
      (probingHashQueryAfterPlan parameter input plan) := by
  unfold probingHashQueryAfterPlan executePlannedHashQuery
  apply (preservesCoordinateMaterializedPublished_executeCandidate coordinate
    plan.candidate?).bind
  intro _
  cases plan.action with
  | ordinary => exact (preservesCoordinate_splitHashQuery coordinate
      (.ordinary input)).to_materializedPublished
  | resolve resolved =>
      by_cases heq : coordinate = resolved
      · subst resolved
        exact preservesCoordinateMaterializedPublished_resolveKnownInput parameter coordinate input
      · exact (preservesCoordinate_resolveKnownInput_of_ne parameter coordinate resolved input
          heq).to_materializedPublished

theorem CandidatePositionsFresh.childValuesPublished
    {context : DeferredContext} (hfresh : CandidatePositionsFresh context) :
    ChildValuesPublished context.state := by
  intro position parent hparent hvalue
  by_contra hhidden
  exact hvalue (hfresh position parent hparent hhidden).1

theorem candidatePositionsFresh_hashStep
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (hfresh : CandidatePositionsFresh context)
    (hpublished : PublishedValues context.state)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table
        ((probingHashQueryAfterPlan parameter input plan).run cache))) :
    CandidatePositionsFresh (canonicalizeMaterializedValues table result.context) := by
  let computation := (probingHashQueryAfterPlan parameter input plan).run cache
  have hdetailed : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation) := by
    rw [← map_erase_runDirectResolvedWitnessFromTable computation context fuel table,
      support_map]
    exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
  have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed computation context fuel
    table result hdetailed
  have hraw := raw_done_of_mem_runDirectResolvedFromTable computation context fuel table result
    hdirect
  have hchildren : ChildValuesPublished result.context.state := by
    intro position parent hparent
    exact preservesCoordinateMaterializedPublished_probingHashQueryAfterPlan parameter input plan
      (.position position) context.state cache fuel result.context.state result.remaining
        result.value.1 result.value.2
        (hfresh.childValuesPublished position parent hparent) hraw
  exact candidatePositionsFresh_canonicalize_of_done computation context fuel table result hfresh
    hpublished hresult hchildren

end SphincsSecurity.Concrete.OtsProbeSimulation
