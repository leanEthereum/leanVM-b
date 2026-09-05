import SphincsSecurity.Proof.OtsProbeNativeRootState

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

def NativeRootSameRel
    (target : Position) (leftOutput rightOutput : HashOutput) :
    Option (ResolvedRunResult (α × SplitHashCache)) →
      Option (ResolvedRunResult (α × SplitHashCache)) → Prop
  | some left, some right =>
      NativeRootContextRel target leftOutput rightOutput left.context right.context ∧
        left.remaining = right.remaining ∧ left.table = right.table ∧
        left.value.1 = right.value.1 ∧
        RootHiddenCacheRel target leftOutput rightOutput left.value.2 right.value.2
  | none, none => True
  | _, _ => False

def NativeRootRelates
    (target : Position) (leftOutput rightOutput : HashOutput)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftState rightState,
    NativeRootContextRel target leftOutput rightOutput leftState rightState →
    ∀ fuel table leftCache rightCache,
      RootHiddenCacheRel target leftOutput rightOutput leftCache rightCache →
      RelTriple
        (runResolvedFromTable leftState fuel table (left.run leftCache))
        (runResolvedFromTable rightState fuel table (right.run rightCache))
        (NativeRootSameRel target leftOutput rightOutput)

theorem nativeRootRelates_pure
    (target : Position) (leftOutput rightOutput : HashOutput) (value : α) :
    NativeRootRelates target leftOutput rightOutput
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α)
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  simp only [StateT.run_pure, runResolvedFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl, hcache⟩

theorem NativeRootRelates.bind
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {leftNext rightNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hfirst : NativeRootRelates target leftOutput rightOutput left right)
    (hnext : ∀ leftValue rightValue, leftValue = rightValue →
      NativeRootRelates target leftOutput rightOutput
        (leftNext leftValue) (rightNext rightValue)) :
    NativeRootRelates target leftOutput rightOutput
      (left >>= leftNext) (right >>= rightNext) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  rw [StateT.run_bind, StateT.run_bind, runResolvedFromTable_bind,
    runResolvedFromTable_bind]
  apply relTriple_bind
    (hfirst leftState rightState hstate fuel table leftCache rightCache hcache)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [NativeRootSameRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [NativeRootSameRel] at hresult
      | some rightResult =>
          rcases hresult with ⟨hnextState, hremaining, htable, hvalue, hnextCache⟩
          simp only
          rw [← hremaining, ← htable, ← hvalue]
          exact hnext leftResult.value.1 leftResult.value.1 rfl
            leftResult.context rightResult.context hnextState leftResult.remaining
              leftResult.table leftResult.value.2 rightResult.value.2 hnextCache

theorem nativeRootRelates_splitUniformImpl
    (target : Position) (leftOutput rightOutput : HashOutput) (n : Nat) :
    NativeRootRelates target leftOutput rightOutput
      (splitUniformImpl n) (splitUniformImpl n) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  unfold splitUniformImpl LazyRevealProbe.uniformQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runResolvedFromTable_uniform_query_bind, runResolvedFromTable_uniform_query_bind]
  apply relTriple_bind
    (relTriple_refl (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
  intro leftValue rightValue hvalue
  subst rightValue
  simp only [runResolvedFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl, hcache⟩

theorem nativeRootRelates_splitHashQuery_ordinary
    (target : Position) (leftOutput rightOutput : HashOutput)
    (input : HashInput) :
    NativeRootRelates target leftOutput rightOutput
      (splitHashQuery (.ordinary input)) (splitHashQuery (.ordinary input)) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  have hlookup := hcache.ordinary input
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  cases hleft : leftCache (.ordinary input) with
  | some output =>
      have hright : rightCache (.ordinary input) = some output := by
        rw [← hlookup]
        exact hleft
      simp only [hright, runResolvedFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl, hcache⟩
  | none =>
      have hright : rightCache (.ordinary input) = none := by
        rw [← hlookup]
        exact hleft
      simp only [hright]
      unfold LazyRevealProbe.hashOutputQuery
      rw [runResolvedFromTable_hashOutput_query_bind,
        runResolvedFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftSample rightSample hsample
      subst rightSample
      simp only [runResolvedFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl,
        hcache.update_same_ordinary input leftSample⟩

theorem nativeRootRelates_ensureCoordinate
    (target : Position) (before after : HashOutput) (coordinate : Coordinate) :
    NativeRootRelates target before after (ensureCoordinate coordinate) (ensureCoordinate coordinate) := by
  intro left right hstate fuel table leftCache rightCache hcache
  change RelTriple
    (runResolvedFromTable left fuel table (LazyRevealProbe.ensureQuery coordinate >>= fun value => pure (value, leftCache)))
    (runResolvedFromTable right fuel table (LazyRevealProbe.ensureQuery coordinate >>= fun value => pure (value, rightCache))) _
  rw [LazyRevealProbe.ensureQuery, runResolvedFromTable_ensure_query_bind, runResolvedFromTable_ensure_query_bind]
  simp only [runResolvedFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨hstate.ensure coordinate, rfl, rfl, rfl, hcache⟩

theorem nativeRootRelates_revealCoordinate_of_ne
    (target : Position) (before after : HashOutput) (coordinate : Coordinate)
    (hne : coordinate ≠ .position target) :
    NativeRootRelates target before after (revealCoordinate coordinate) (revealCoordinate coordinate) := by
  intro left right hstate fuel table leftCache rightCache hcache
  unfold revealCoordinate
  rw [StateT.run_bind, StateT.run_bind, runResolvedFromTable_bind, runResolvedFromTable_bind]
  apply relTriple_bind
    (relTriple_nativeRoot_revealCoordinateOutput target before after coordinate left right hstate
      fuel table leftCache rightCache hcache)
  intro leftResult rightResult hrel
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => contradiction
  | some leftResult =>
      cases rightResult with
      | none => contradiction
      | some rightResult =>
          rcases hrel with ⟨hcontext, hfuel, htable, houtput, _, hnextCache⟩
          have heq : rightResult.value.1 = leftResult.value.1 := by simpa [hne] using houtput
          simp only [StateT.run_pure, runResolvedFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure ⟨hcontext, hfuel, htable, congrArg truncateHash heq.symm, hnextCache⟩

theorem nativeRootRelates_revealPosition_of_ne
    (target : Position) (before after : HashOutput) (position : Position)
    (hne : position ≠ target) :
    NativeRootRelates target before after (revealPosition position) (revealPosition position) :=
  nativeRootRelates_revealCoordinate_of_ne target before after (.position position) (by simpa using hne)

theorem nativeRootRelates_publishCoordinate
    (target : Position) (before after : HashOutput) (coordinate : Coordinate) :
    NativeRootRelates target before after (publishCoordinate coordinate) (publishCoordinate coordinate) := by
  intro left right hstate fuel table leftCache rightCache hcache
  unfold publishCoordinate LazyRevealProbe.publishQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runResolvedFromTable_publish_query_bind, runResolvedFromTable_publish_query_bind]
  simp only [runResolvedFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨hstate.publish coordinate, rfl, rfl, rfl, hcache⟩

theorem nativeRootRelates_revealPublishedCoordinate_of_ne
    (target : Position) (before after : HashOutput) (coordinate : Coordinate)
    (hne : coordinate ≠ .position target) :
    NativeRootRelates target before after
      (revealPublishedCoordinate coordinate) (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  apply (nativeRootRelates_revealCoordinate_of_ne target before after coordinate hne).bind
  intro leftValue rightValue heq
  subst rightValue
  exact (nativeRootRelates_publishCoordinate target before after coordinate).bind fun _ _ _ =>
    nativeRootRelates_pure target before after leftValue

def NativeRootTargetRevealRel (target : Position) (before after : HashOutput) :
    Option (ResolvedRunResult (Digest × SplitHashCache)) →
      Option (ResolvedRunResult (Digest × SplitHashCache)) → Prop
  | some left, some right =>
      NativeRootContextRel target before after left.context right.context ∧
        left.remaining = right.remaining ∧ left.table = right.table ∧
        left.value.1 = truncateHash before ∧ right.value.1 = truncateHash after ∧
        RootHiddenCacheRel target before after left.value.2 right.value.2
  | none, none => True
  | _, _ => False

theorem relTriple_nativeRoot_revealPosition_target
    (target : Position) (before after : HashOutput)
    (left right : DeferredContext) (hstate : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target before after leftCache rightCache) :
    RelTriple
      (runResolvedFromTable left fuel table ((revealPosition target).run leftCache))
      (runResolvedFromTable right fuel table ((revealPosition target).run rightCache))
      (NativeRootTargetRevealRel target before after) := by
  unfold revealPosition revealCoordinate
  rw [StateT.run_bind, StateT.run_bind, runResolvedFromTable_bind, runResolvedFromTable_bind]
  apply relTriple_bind
    (relTriple_nativeRoot_revealCoordinateOutput target before after (.position target) left right hstate
      fuel table leftCache rightCache hcache)
  intro leftResult rightResult hrel
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => contradiction
  | some leftResult =>
      cases rightResult with
      | none => contradiction
      | some rightResult =>
          rcases hrel with ⟨hcontext, hfuel, htable, hright, hleft, hnextCache⟩
          have hrightValue : rightResult.value.1 = after := by simpa using hright
          simp only [StateT.run_pure, runResolvedFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure ⟨hcontext, hfuel, htable, congrArg truncateHash (hleft rfl),
            congrArg truncateHash hrightValue, hnextCache⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
