import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp

attribute [local irreducible] maskedSignLayer

def ResolvedPreservesCoordinate (coordinate : Coordinate)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ context fuel table cache result,
    some result ∈ support
      (runResolvedFromTable context fuel table (computation.run cache)) →
    result.context.state.values coordinate = context.state.values coordinate ∧
      (coordinate ∈ result.context.state.revealed ↔
        coordinate ∈ context.state.revealed)

theorem ResolvedPreservesCoordinate.bind
    {coordinate : Coordinate}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : ResolvedPreservesCoordinate coordinate left)
    (hnext : ∀ value, ResolvedPreservesCoordinate coordinate (next value)) :
    ResolvedPreservesCoordinate coordinate (left >>= next) := by
  intro context fuel table cache result hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨leftOption, hleftSupport, hrest⟩ := hresult
  cases leftOption with
  | none => simp at hrest
  | some leftResult =>
      have hmiddle := hleft context fuel table cache leftResult hleftSupport
      have hfinal := hnext leftResult.value.1 leftResult.context leftResult.remaining
        leftResult.table leftResult.value.2 result hrest
      exact ⟨hfinal.1.trans hmiddle.1, hfinal.2.trans hmiddle.2⟩

theorem resolvedPreservesCoordinate_pure (coordinate : Coordinate) (value : α) :
    ResolvedPreservesCoordinate coordinate
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro context fuel table cache result hresult
  simp [runResolvedFromTable] at hresult
  subst result
  exact ⟨rfl, Iff.rfl⟩

theorem ResolvedPreservesPublished.of_preservesCoordinate
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (hpreserves : ∀ coordinate,
      ResolvedPreservesCoordinate coordinate computation) :
    ResolvedPreservesPublished computation := by
  intro context cache fuel table result hpublished hresult coordinate hrevealed
  have hcoordinate := hpreserves coordinate context fuel table cache result hresult
  rw [hcoordinate.1]
  exact hpublished coordinate (hcoordinate.2.mp hrevealed)

theorem resolvedPreservesCoordinate_modify (coordinate : Coordinate)
    (update : SplitHashCache → SplitHashCache) :
    ResolvedPreservesCoordinate coordinate
      (modify update : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) Unit) := by
  intro context fuel table cache result hresult
  simp [StateT.run_modify, runResolvedFromTable] at hresult
  subst result
  exact ⟨rfl, Iff.rfl⟩

theorem resolvedPreservesCoordinate_splitHashQuery
    (coordinate : Coordinate) (key : SplitHashKey) :
    ResolvedPreservesCoordinate coordinate (splitHashQuery key) := by
  intro context fuel table cache result hresult
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache key with
  | some output =>
      rw [hlookup] at hresult
      simp [runResolvedFromTable] at hresult
      subst result
      exact ⟨rfl, Iff.rfl⟩
  | none =>
      rw [hlookup] at hresult
      dsimp only at hresult
      change some result ∈ support (runResolvedFromTable context fuel table
        (LazyRevealProbe.hashOutputQuery >>= fun output =>
          pure (output, Function.update cache key (some output)))) at hresult
      rw [LazyRevealProbe.hashOutputQuery] at hresult
      rw [runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨output, _houtput, hdone⟩ := hresult
      simp [runResolvedFromTable] at hdone
      subst result
      exact ⟨rfl, Iff.rfl⟩

theorem resolvedPreservesCoordinate_ensure
    (coordinate ensured : Coordinate) :
    ResolvedPreservesCoordinate coordinate (ensureCoordinate ensured) := by
  intro context fuel table cache result hresult
  change some result ∈ support (runResolvedFromTable context fuel table
    (LazyRevealProbe.ensureQuery ensured >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.ensureQuery] at hresult
  rw [runResolvedFromTable_ensure_query_bind] at hresult
  simp [runResolvedFromTable, LazyRevealProbe.State.ensure] at hresult
  subst result
  exact ⟨rfl, Iff.rfl⟩

theorem resolvedPreservesCoordinate_probe
    (coordinate : Coordinate) (candidate : Probe) :
    ResolvedPreservesCoordinate coordinate (probe candidate) := by
  intro context fuel table cache result hresult
  change some result ∈ support (runResolvedFromTable context fuel table
    (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate >>= fun output =>
      pure (output, cache))) at hresult
  rw [LazyRevealProbe.probeQuery] at hresult
  rw [runResolvedFromTable_probe_query_bind] at hresult
  cases fuel with
  | zero => simp at hresult
  | succ remaining =>
      by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
      · simp only [hrevealed, ↓reduceIte] at hresult
        simp [runResolvedFromTable] at hresult
        subst result
        exact ⟨rfl, Iff.rfl⟩
      · simp only [hrevealed, ↓reduceIte] at hresult
        change some result ∈ support (runResolvedFromTable
          { context with state :=
              (context.state.addPending candidate.coordinate candidate.candidate) }
          remaining table (pure ((), cache))) at hresult
        simp [runResolvedFromTable, LazyRevealProbe.State.addPending] at hresult
        subst result
        exact ⟨rfl, Iff.rfl⟩

theorem resolvedPreservesCoordinate_peekCoordinate
    (coordinate observed : Coordinate) :
    ResolvedPreservesCoordinate coordinate (peekCoordinate observed) := by
  intro context fuel table cache result hresult
  change some result ∈ support (runResolvedFromTable context fuel table
    (LazyRevealProbe.peekQuery observed >>= fun output =>
      pure (truncateHash <$> output, cache))) at hresult
  rw [LazyRevealProbe.peekQuery, runResolvedFromTable_peek_query_bind] at hresult
  simp [runResolvedFromTable] at hresult
  subst result
  exact ⟨rfl, Iff.rfl⟩

theorem resolvedPreservesCoordinate_peekPositionValues
    (coordinate : Coordinate) : ∀ positions,
    ResolvedPreservesCoordinate coordinate (peekPositionValues positions)
  | [] => resolvedPreservesCoordinate_pure coordinate (some [])
  | position :: remaining => by
      rw [peekPositionValues]
      exact (resolvedPreservesCoordinate_peekCoordinate coordinate (.position position)).bind
        fun value => match value with
        | none => resolvedPreservesCoordinate_pure coordinate none
        | some value =>
            (resolvedPreservesCoordinate_peekPositionValues coordinate remaining).bind
              fun values => match values with
              | none => resolvedPreservesCoordinate_pure coordinate none
              | some values => resolvedPreservesCoordinate_pure coordinate
                  (some (value :: values))

theorem resolvedPreservesCoordinate_peekTableInput
    (parameter : PublicParameter) (coordinate : Coordinate) : ∀ target,
    ResolvedPreservesCoordinate coordinate (peekTableInput parameter target)
  | .chainStart _ _ _ _ => resolvedPreservesCoordinate_pure coordinate none
  | .position position => by
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput]
          by_cases hstep : step.val = 0
          · rw [if_pos hstep]
            exact (resolvedPreservesCoordinate_peekCoordinate coordinate
              (.chainStart lay tree leafIdx chainIdx)).bind fun value => match value with
              | none => resolvedPreservesCoordinate_pure coordinate none
              | some value => resolvedPreservesCoordinate_pure coordinate
                  (some (tweakableHashInput parameter
                    (Position.chain lay tree leafIdx chainIdx step).domain
                      (digestBytes value)))
          · rw [if_neg hstep]
            exact (resolvedPreservesCoordinate_peekPositionValues coordinate
              (Position.chain lay tree leafIdx chainIdx step).children).bind
                fun values => match values with
                | none => resolvedPreservesCoordinate_pure coordinate none
                | some values => resolvedPreservesCoordinate_pure coordinate
                    (some (tweakableHashInput parameter
                      (Position.chain lay tree leafIdx chainIdx step).domain
                        (values.flatMap digestBytes)))
      | leaf lay tree leafIdx =>
          simp only [peekTableInput]
          exact (resolvedPreservesCoordinate_peekPositionValues coordinate
            (Position.leaf lay tree leafIdx).children).bind fun values => match values with
            | none => resolvedPreservesCoordinate_pure coordinate none
            | some values => resolvedPreservesCoordinate_pure coordinate
                (some (tweakableHashInput parameter (Position.leaf lay tree leafIdx).domain
                  (values.flatMap digestBytes)))
      | node lay tree level nodeIdx =>
          simp only [peekTableInput]
          exact (resolvedPreservesCoordinate_peekPositionValues coordinate
            (Position.node lay tree level nodeIdx).children).bind fun values => match values with
            | none => resolvedPreservesCoordinate_pure coordinate none
            | some values => resolvedPreservesCoordinate_pure coordinate
                (some (tweakableHashInput parameter
                  (Position.node lay tree level nodeIdx).domain
                    (values.flatMap digestBytes)))
      | ftsLeaf index tree leafIdx =>
          simp only [peekTableInput]
          exact (resolvedPreservesCoordinate_peekPositionValues coordinate
            (Position.ftsLeaf index tree leafIdx).children).bind fun values => match values with
            | none => resolvedPreservesCoordinate_pure coordinate none
            | some values => resolvedPreservesCoordinate_pure coordinate
                (some (tweakableHashInput parameter (Position.ftsLeaf index tree leafIdx).domain
                  (values.flatMap digestBytes)))
      | ftsNode index tree level nodeIdx =>
          simp only [peekTableInput]
          exact (resolvedPreservesCoordinate_peekPositionValues coordinate
            (Position.ftsNode index tree level nodeIdx).children).bind fun values => match values with
            | none => resolvedPreservesCoordinate_pure coordinate none
            | some values => resolvedPreservesCoordinate_pure coordinate
                (some (tweakableHashInput parameter
                  (Position.ftsNode index tree level nodeIdx).domain
                    (values.flatMap digestBytes)))
      | ftsRoots index =>
          simp only [peekTableInput]
          exact (resolvedPreservesCoordinate_peekPositionValues coordinate
            (Position.ftsRoots index).children).bind fun values => match values with
            | none => resolvedPreservesCoordinate_pure coordinate none
            | some values => resolvedPreservesCoordinate_pure coordinate
                (some (tweakableHashInput parameter (Position.ftsRoots index).domain
                  (values.flatMap digestBytes)))

theorem resolvedPreservesCoordinate_publish_of_ne
    (coordinate published : Coordinate) (hne : coordinate ≠ published) :
    ResolvedPreservesCoordinate coordinate (publishCoordinate published) := by
  intro context fuel table cache result hresult
  change some result ∈ support (runResolvedFromTable context fuel table
    (LazyRevealProbe.publishQuery published >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.publishQuery, runResolvedFromTable_publish_query_bind] at hresult
  simp [runResolvedFromTable] at hresult
  subst result
  simp [LazyRevealProbe.State.publish, hne]

theorem resolvedPreservesCoordinate_revealCoordinateOutput_of_ne
    (coordinate revealed : Coordinate) (hne : coordinate ≠ revealed) :
    ResolvedPreservesCoordinate coordinate (revealCoordinateOutput revealed) := by
  intro context fuel table cache result hresult
  rw [runResolvedFromTable_revealCoordinateOutput] at hresult
  cases revealed with
  | chainStart lay tree leafIdx chainIdx =>
      cases hresolve : resolveDeferredChainStart table
          ⟨lay, tree, leafIdx, chainIdx⟩ context with
      | none => simp [hresolve] at hresult
      | some resolved =>
          simp [hresolve] at hresult
          subst result
          simp [LazyRevealProbe.State.materialize, Function.update, hne]
  | position position =>
      rw [mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, _hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          simp at hrest
          subst result
          simp [LazyRevealProbe.State.materialize, Function.update, hne]

end SphincsSecurity.Concrete.OtsProbeSimulation
