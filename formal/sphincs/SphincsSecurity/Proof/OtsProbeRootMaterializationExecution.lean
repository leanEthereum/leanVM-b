import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeCanonicalPending
import SphincsSecurity.Proof.OtsProbeNativeRootMaterialization
import SphincsSecurity.Proof.OtsProbeResolvedComputedExecution

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def RootMaterializationPreserving
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ context fuel table cache result,
    LayerRootsMaterialized context → DeferredComputationsClosed context →
    some result ∈ support (runResolvedFromTable context fuel table (computation.run cache)) →
    LayerRootsMaterialized result.context

theorem RootMaterializationPreserving.pure (value : α) :
    RootMaterializationPreserving (pure value) := by
  intro context fuel table cache result hmat _ hresult
  simp [runResolvedFromTable] at hresult
  subst result
  exact hmat

theorem RootMaterializationPreserving.bind
    {left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : RootMaterializationPreserving left) (hnext : ∀ value, RootMaterializationPreserving (next value)) :
    RootMaterializationPreserving (left >>= next) := by
  intro context fuel table cache result hmat hclosed hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨middle, hmiddle, hrest⟩ := hresult
  cases middle with
  | none => simp at hrest
  | some middle =>
      exact hnext middle.value.1 middle.context middle.remaining middle.table middle.value.2 result
        (hleft context fuel table cache middle hmat hclosed hmiddle)
        (hclosed.of_mem_runResolved _ context fuel table middle hmiddle) hrest

theorem RootMaterializationPreserving.of_administrative
    {computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α} {value : α}
    (h : ResolvedAdministrative computation value) : RootMaterializationPreserving computation := by
  intro context fuel table cache result hmat _ hresult
  obtain ⟨finalContext, hrun, _, hstate, hvalues⟩ := h context cache fuel table
  rw [hrun] at hresult
  simp only [mem_support_pure_iff, Option.some.injEq] at hresult
  subst result
  exact hmat.of_values_eq hstate hvalues

theorem rootMaterializationPreserving_publishCoordinate (coordinate : Coordinate) :
    RootMaterializationPreserving (publishCoordinate coordinate) :=
  .of_administrative (resolvedAdministrative_publishCoordinate coordinate)

theorem rootMaterializationPreserving_modify (f : SplitHashCache → SplitHashCache) :
    RootMaterializationPreserving (modify f) := by
  intro context fuel table cache result hmat _ hresult
  simp [StateT.run_modify, runResolvedFromTable] at hresult
  subst result
  exact hmat

theorem rootMaterializationPreserving_splitHashQuery (input : SplitHashKey) :
    RootMaterializationPreserving (splitHashQuery input) := by
  intro context fuel table cache result hmat _ hresult
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache input with
  | some output =>
      simp [hlookup, runResolvedFromTable] at hresult
      subst result
      exact hmat
  | none =>
      simp only [hlookup] at hresult
      rw [LazyRevealProbe.hashOutputQuery, runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨output, _, hreturn⟩ := hresult
      simp [runResolvedFromTable] at hreturn
      subst result
      exact hmat

theorem rootMaterializationPreserving_peekCoordinate (coordinate : Coordinate) :
    RootMaterializationPreserving (peekCoordinate coordinate) := by
  intro context fuel table cache result hmat _ hresult
  rw [runResolvedFromTable_peekCoordinate] at hresult
  simp only [mem_support_pure_iff, Option.some.injEq] at hresult
  subst result
  exact hmat

theorem rootMaterializationPreserving_probe (candidate : Probe) :
    RootMaterializationPreserving (probe candidate) := by
  intro context fuel table cache result hmat _ hresult
  unfold probe at hresult
  rw [StateT.run_liftM, LazyRevealProbe.probeQuery, runResolvedFromTable_probe_query_bind] at hresult
  cases fuel with
  | zero => simp at hresult
  | succ remaining =>
      split_ifs at hresult <;> simp [runResolvedFromTable] at hresult <;> subst result <;> exact hmat

theorem LayerRootsMaterialized.materialize_chainStart
    {context : DeferredContext} (hmat : LayerRootsMaterialized context)
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex) (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    LayerRootsMaterialized (materializeResolvedChainStart context index result) := by
  intro target hroot haux
  change result.values target ≠ none at haux
  rw [resolveDeferredChainStart_deferred_values_eq table index context result hresult] at haux
  have hbefore := hmat target hroot haux
  simpa [materializeResolvedChainStart, LazyRevealProbe.State.materialize, OtsSecretIndex.coordinate] using hbefore

theorem rootMaterializationPreserving_revealCoordinateOutput_bounded (coordinate : Coordinate)
    (hbounded : ∀ position, coordinate = .position position → LayerBoundedPosition position) :
    RootMaterializationPreserving (revealCoordinateOutput coordinate) := by
  intro context fuel table cache result hmat _ hresult
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      rw [runResolvedFromTable_revealCoordinateOutput] at hresult
      simp only [pure_bind] at hresult
      cases hresolved : resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context with
      | none => simp [hresolved] at hresult
      | some resolved =>
          simp only [hresolved, mem_support_pure_iff, Option.some.injEq] at hresult
          subst result
          exact hmat.materialize_chainStart table ⟨lay, tree, leafIdx, chainIdx⟩ resolved hresolved
  | position position =>
      rw [runResolvedFromTable_revealCoordinateOutput, mem_support_bind_iff] at hresult
      obtain ⟨resolved, hresolved, hreturn⟩ := hresult
      cases resolved with
      | none => simp at hreturn
      | some resolved =>
          simp only [mem_support_pure_iff, Option.some.injEq] at hreturn
          subst result
          exact hmat.of_resolveReveal_bounded table position resolved (hbounded position rfl) hresolved

theorem rootMaterializationPreserving_revealCoordinate_bounded (coordinate : Coordinate)
    (hbounded : ∀ position, coordinate = .position position → LayerBoundedPosition position) :
    RootMaterializationPreserving (revealCoordinate coordinate) :=
  (rootMaterializationPreserving_revealCoordinateOutput_bounded coordinate hbounded).bind (fun _ => .pure _)

theorem rootMaterializationPreserving_revealPosition (position : Position) (hbounded : LayerBoundedPosition position) :
    RootMaterializationPreserving (revealPosition position) :=
  rootMaterializationPreserving_revealCoordinate_bounded (.position position)
    (fun _ heq => Coordinate.position.inj heq ▸ hbounded)

theorem rootMaterializationPreserving_sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ i, RootMaterializationPreserving (computation i)) :
    RootMaterializationPreserving (sequenceFin computation) := by
  induction n with
  | zero => simpa [sequenceFin] using (RootMaterializationPreserving.pure (α := Fin 0 → α) Fin.elim0)
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind (fun _ => (ih _ (fun i => hcomponent i.succ)).bind (fun _ => .pure _))

theorem rootMaterializationPreserving_splitUniformImpl (n : Nat) :
    RootMaterializationPreserving (splitUniformImpl n) := by
  intro context fuel table cache result hmat _ hresult
  change some result ∈ support (runResolvedFromTable context fuel table
    (LazyRevealProbe.uniformQuery n >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.uniformQuery, runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
  obtain ⟨output, _, hreturn⟩ := hresult
  simp [runResolvedFromTable] at hreturn
  subst result
  exact hmat

theorem rootMaterializationPreserving_simulateQ {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (himpl : ∀ input, RootMaterializationPreserving (impl input)) (computation : OracleComp spec α) :
    RootMaterializationPreserving (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact .pure value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact (himpl query).bind ih

theorem rootMaterializationPreserving_ordinaryHash (computation : OracleComp HashSpec α) :
    RootMaterializationPreserving (simulateQ ordinaryHashImpl computation) :=
  rootMaterializationPreserving_simulateQ _ (fun input => rootMaterializationPreserving_splitHashQuery (.ordinary input)) computation

theorem rootMaterializationPreserving_ordinaryRom (computation : OracleComp OracleWorld α) :
    RootMaterializationPreserving (simulateQ ordinaryRomImpl computation) := by
  apply rootMaterializationPreserving_simulateQ _ _ computation
  intro input
  cases input with
  | inl n => exact rootMaterializationPreserving_splitUniformImpl n
  | inr input => exact rootMaterializationPreserving_splitHashQuery (.ordinary input)

end SphincsSecurity.Concrete.OtsProbeSimulation
