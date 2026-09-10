import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootCache
import SphincsSecurity.Proof.OtsProbeResolvedSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

def OrdinarySplitCacheEq (left right : SplitHashCache) : Prop :=
  ∀ input, left (.ordinary input) = right (.ordinary input)

theorem OrdinarySplitCacheEq.update {left right : SplitHashCache}
    (h : OrdinarySplitCacheEq left right) (key : SplitHashKey) (output : HashOutput) :
    OrdinarySplitCacheEq (Function.update left key (some output)) (Function.update right key (some output)) := by
  intro input
  by_cases heq : SplitHashKey.ordinary input = key
  · simp [heq]
  · simp [Function.update_of_ne heq, h input]

def OrdinaryCacheNativeSameRel :
    Option (ResolvedRunResult (α × SplitHashCache)) →
      Option (ResolvedRunResult (α × SplitHashCache)) → Prop
  | some left, some right =>
      left.context = right.context ∧ left.remaining = right.remaining ∧
        left.table = right.table ∧ left.value.1 = right.value.1 ∧
        OrdinarySplitCacheEq left.value.2 right.value.2
  | none, none => True
  | _, _ => False

def OrdinaryCacheNativeCouples
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftCache rightCache,
    OrdinarySplitCacheEq leftCache rightCache →
    ∀ state fuel table,
      RelTriple
        (runResolvedFromTable state fuel table (computation.run leftCache))
        (runResolvedFromTable state fuel table (computation.run rightCache))
        OrdinaryCacheNativeSameRel

theorem ordinaryCacheNativeCouples_pure
    (value : α) :
    OrdinaryCacheNativeCouples
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro leftCache rightCache hcache state fuel table
  simp only [StateT.run_pure, runResolvedFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem ordinaryCacheNativeCouples_ensureCoordinate
    (coordinate : Coordinate) :
    OrdinaryCacheNativeCouples
      (ensureCoordinate coordinate) := by
  intro leftCache rightCache hcache state fuel table
  change RelTriple
    (runResolvedFromTable state fuel table (LazyRevealProbe.ensureQuery coordinate >>= fun value => pure (value, leftCache)))
    (runResolvedFromTable state fuel table (LazyRevealProbe.ensureQuery coordinate >>= fun value => pure (value, rightCache))) _
  rw [LazyRevealProbe.ensureQuery, runResolvedFromTable_ensure_query_bind, runResolvedFromTable_ensure_query_bind]
  simp only [runResolvedFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem OrdinaryCacheNativeCouples.bind
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : OrdinaryCacheNativeCouples left)
    (hnext : ∀ value,
      OrdinaryCacheNativeCouples (next value)) :
    OrdinaryCacheNativeCouples (left >>= next) := by
  intro leftCache rightCache hcache state fuel table
  rw [StateT.run_bind, StateT.run_bind, runResolvedFromTable_bind,
    runResolvedFromTable_bind]
  apply relTriple_bind (hleft leftCache rightCache hcache state fuel table)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [OrdinaryCacheNativeSameRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [OrdinaryCacheNativeSameRel] at hresult
      | some rightResult =>
          rcases hresult with ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
          simp only
          rw [← hstate, ← hremaining, ← htable, ← hvalue]
          exact hnext leftResult.value.1 leftResult.value.2 rightResult.value.2 hnextCache
            leftResult.context leftResult.remaining leftResult.table

theorem ordinaryCacheNativeCouples_sequenceFin
    {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index,
      OrdinaryCacheNativeCouples (computation index)) :
    OrdinaryCacheNativeCouples
      (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact ordinaryCacheNativeCouples_pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun _ =>
        (ih (fun index : Fin n => computation index.succ)
          (fun index => hcomponent index.succ)).bind fun _ =>
            ordinaryCacheNativeCouples_pure _

theorem ordinaryCacheNativeCouples_ensureChainPrefix
    (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    OrdinaryCacheNativeCouples
      (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (ordinaryCacheNativeCouples_sequenceFin _
    fun step => by
      by_cases hstep : step.val < digit.val
      · rw [if_pos hstep]
        exact ordinaryCacheNativeCouples_ensureCoordinate _
      · rw [if_neg hstep]
        exact ordinaryCacheNativeCouples_pure ()).bind fun _ =>
          ordinaryCacheNativeCouples_pure ()

theorem ordinaryCacheNativeCouples_worldStep
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (finish : α → SplitHashCache → β × SplitHashCache)
    (hfinish : ∀ output leftCache rightCache,
      OrdinarySplitCacheEq leftCache rightCache →
      (finish output leftCache).1 = (finish output rightCache).1 ∧
        OrdinarySplitCacheEq
          (finish output leftCache).2 (finish output rightCache).2) :
    OrdinaryCacheNativeCouples
      (fun cache => computation >>= fun output => pure (finish output cache)) := by
  intro leftCache rightCache hcache context fuel table
  change RelTriple
    (runResolvedFromTable context fuel table (computation >>= fun output => pure (finish output leftCache)))
    (runResolvedFromTable context fuel table (computation >>= fun output => pure (finish output rightCache))) _
  rw [runResolvedFromTable_bind, runResolvedFromTable_bind]
  apply relTriple_bind (relTriple_refl (runResolvedFromTable context fuel table computation))
  intro leftResult rightResult heq
  subst rightResult
  cases leftResult with
  | none => exact relTriple_pure_pure trivial
  | some result =>
      simp only [runResolvedFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, hfinish result.value leftCache rightCache hcache⟩

theorem ordinaryCacheNativeCouples_revealCoordinateOutput (coordinate : Coordinate) :
    OrdinaryCacheNativeCouples (revealCoordinateOutput coordinate) := by
  have heq : revealCoordinateOutput coordinate =
      (fun cache : SplitHashCache => LazyRevealProbe.revealQuery coordinate >>= fun output =>
        pure (output, Function.update cache (.hidden coordinate) (some output))) := by
    funext cache
    exact revealCoordinateOutput_run_eq coordinate cache
  rw [heq]
  exact ordinaryCacheNativeCouples_worldStep _ _ fun output left right h => ⟨rfl, h.update _ output⟩

theorem ordinaryCacheNativeCouples_revealCoordinate (coordinate : Coordinate) :
    OrdinaryCacheNativeCouples (revealCoordinate coordinate) := by
  unfold revealCoordinate
  exact (ordinaryCacheNativeCouples_revealCoordinateOutput coordinate).bind fun output =>
    ordinaryCacheNativeCouples_pure (truncateHash output)

theorem ordinaryCacheNativeCouples_revealPosition (position : Position) :
    OrdinaryCacheNativeCouples (revealPosition position) :=
  ordinaryCacheNativeCouples_revealCoordinate (.position position)

theorem ordinaryCacheNativeCouples_publishCoordinate (coordinate : Coordinate) :
    OrdinaryCacheNativeCouples (publishCoordinate coordinate) := by
  unfold publishCoordinate
  exact ordinaryCacheNativeCouples_worldStep _ _ fun _ _ _ h => ⟨rfl, h⟩

theorem ordinaryCacheNativeCouples_peekCoordinate (coordinate : Coordinate) :
    OrdinaryCacheNativeCouples (peekCoordinate coordinate) := by
  intro left right h context fuel table
  rw [peekCoordinate_run_eq, peekCoordinate_run_eq, LazyRevealProbe.peekQuery,
    runResolvedFromTable_peek_query_bind, runResolvedFromTable_peek_query_bind]
  simp only [runResolvedFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, h⟩

theorem ordinaryCacheNativeCouples_probe (candidate : Probe) :
    OrdinaryCacheNativeCouples (probe candidate) := by
  unfold probe
  exact ordinaryCacheNativeCouples_worldStep _ _ fun _ _ _ h => ⟨rfl, h⟩

theorem ordinaryCacheNativeCouples_splitUniformImpl (n : Nat) :
    OrdinaryCacheNativeCouples (splitUniformImpl n) := by
  unfold splitUniformImpl
  exact ordinaryCacheNativeCouples_worldStep _ _ fun _ _ _ h => ⟨rfl, h⟩

theorem ordinaryCacheNativeCouples_splitHashQuery (input : HashInput) :
    OrdinaryCacheNativeCouples (splitHashQuery (.ordinary input)) := by
  intro left right h context fuel table
  have hlookup := h input
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  cases hleft : left (.ordinary input) with
  | some output =>
      have hright : right (.ordinary input) = some output := hlookup.symm.trans hleft
      simp only [hright, runResolvedFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, h⟩
  | none =>
      have hright : right (.ordinary input) = none := hlookup.symm.trans hleft
      simp only [hright]
      unfold LazyRevealProbe.hashOutputQuery
      rw [runResolvedFromTable_hashOutput_query_bind, runResolvedFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput heq
      subst rightOutput
      simp only [runResolvedFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, h.update _ leftOutput⟩

theorem ordinaryCacheNativeCouples_modifyOrdinary (input : HashInput) (output : HashOutput) :
    OrdinaryCacheNativeCouples
      (modify fun cache : SplitHashCache => Function.update cache (.ordinary input) (some output)) := by
  intro left right h context fuel table
  simp only [StateT.run_modify, runResolvedFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, h.update _ output⟩

theorem ordinaryCacheNativeCouples_simulateQ {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (himpl : ∀ query, OrdinaryCacheNativeCouples (impl query))
    (computation : OracleComp spec α) : OrdinaryCacheNativeCouples (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using ordinaryCacheNativeCouples_pure value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (himpl query).bind ih

theorem ordinaryCacheNativeCouples_ordinaryHash (computation : OracleComp HashSpec α) :
    OrdinaryCacheNativeCouples (simulateQ ordinaryHashImpl computation) :=
  ordinaryCacheNativeCouples_simulateQ ordinaryHashImpl ordinaryCacheNativeCouples_splitHashQuery computation

theorem ordinaryCacheNativeCouples_ordinaryRom (computation : OracleComp OracleWorld α) :
    OrdinaryCacheNativeCouples (simulateQ ordinaryRomImpl computation) := by
  apply ordinaryCacheNativeCouples_simulateQ
  intro query
  cases query with
  | inl n => exact ordinaryCacheNativeCouples_splitUniformImpl n
  | inr input => exact ordinaryCacheNativeCouples_splitHashQuery input

end SphincsSecurity.Concrete.OtsProbeSimulation
