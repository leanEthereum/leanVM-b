import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveObserver
import SphincsSecurity.Proof.OtsProbeStartHistorySupport

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedSignLayer
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

theorem resolvedPreservesCoordinate_sequenceFin (coordinate : Coordinate) {n : Nat}
    (computation : Fin n → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index, ResolvedPreservesCoordinate coordinate (computation index)) :
    ResolvedPreservesCoordinate coordinate (sequenceFin computation) := by
  induction n with
  | zero => simpa [sequenceFin] using resolvedPreservesCoordinate_pure coordinate Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun _ =>
        (ih (fun index : Fin n => computation index.succ) (fun index => hcomponent index.succ)).bind
          fun _ => resolvedPreservesCoordinate_pure coordinate _

theorem resolvedPreservesCoordinate_simulateQ_ordinaryHashImpl (coordinate : Coordinate)
    (computation : OracleComp HashSpec α) :
    ResolvedPreservesCoordinate coordinate (simulateQ ordinaryHashImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact resolvedPreservesCoordinate_pure coordinate value
  | query_bind input next ih =>
      rw [simulateQ_query_bind]
      exact (resolvedPreservesCoordinate_splitHashQuery coordinate (.ordinary input)).bind ih

theorem resolvedPreservesCoordinate_revealCoordinate_of_ne
    (coordinate revealed : Coordinate) (hne : coordinate ≠ revealed) :
    ResolvedPreservesCoordinate coordinate (revealCoordinate revealed) := by
  unfold revealCoordinate
  exact (resolvedPreservesCoordinate_revealCoordinateOutput_of_ne coordinate revealed hne).bind fun _ =>
    resolvedPreservesCoordinate_pure coordinate _

theorem resolvedPreservesCoordinate_ensureFullChain
    (coordinate : Coordinate) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ResolvedPreservesCoordinate coordinate (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (resolvedPreservesCoordinate_sequenceFin coordinate _ fun _ =>
    resolvedPreservesCoordinate_ensure coordinate _).bind fun _ => resolvedPreservesCoordinate_pure coordinate ()

theorem resolvedPreservesCoordinate_ensureOtsLeaf
    (coordinate : Coordinate) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ResolvedPreservesCoordinate coordinate (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (resolvedPreservesCoordinate_sequenceFin coordinate _ fun chainIdx =>
    resolvedPreservesCoordinate_ensureFullChain coordinate lay tree leafIdx chainIdx).bind fun _ =>
      resolvedPreservesCoordinate_ensure coordinate _

theorem resolvedPreservesCoordinate_ensureTreeNode
    (coordinate : Coordinate) (lay : Layer) (tree : TreeIndex) : ∀ level nodeIdx,
    ResolvedPreservesCoordinate coordinate (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => by
      rw [ensureTreeNode]
      exact resolvedPreservesCoordinate_ensureOtsLeaf coordinate lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (resolvedPreservesCoordinate_ensureTreeNode coordinate lay tree level (2 * nodeIdx)).bind fun _ =>
        (resolvedPreservesCoordinate_ensureTreeNode coordinate lay tree level (2 * nodeIdx + 1)).bind fun _ => by
          split
          · exact resolvedPreservesCoordinate_ensure coordinate _
          · exact resolvedPreservesCoordinate_pure coordinate ()

theorem resolvedPreservesCoordinate_ensureChainPrefix
    (coordinate : Coordinate) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) :
    ResolvedPreservesCoordinate coordinate (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (resolvedPreservesCoordinate_sequenceFin coordinate _ fun _ => by
    split
    · exact resolvedPreservesCoordinate_ensure coordinate _
    · exact resolvedPreservesCoordinate_pure coordinate ()).bind fun _ => resolvedPreservesCoordinate_pure coordinate ()

theorem resolvedPreservesCoordinate_maskedOtsSignFrom
    (coordinate : Coordinate) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) : ∀ attempts counter,
    ResolvedPreservesCoordinate coordinate (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, _ => resolvedPreservesCoordinate_pure coordinate none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      exact (resolvedPreservesCoordinate_simulateQ_ordinaryHashImpl coordinate _).bind fun encoded =>
        match encoded with
        | none => resolvedPreservesCoordinate_maskedOtsSignFrom coordinate parameter lay tree leafIdx message
            attempts (counter + 1)
        | some encoding =>
            (resolvedPreservesCoordinate_sequenceFin coordinate _ fun chainIdx =>
              resolvedPreservesCoordinate_ensureChainPrefix coordinate lay tree leafIdx chainIdx (encoding chainIdx)).bind
                fun _ => resolvedPreservesCoordinate_pure coordinate _

theorem resolvedPreservesCoordinate_ensureTreePath
    (coordinate : Coordinate) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ResolvedPreservesCoordinate coordinate (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (resolvedPreservesCoordinate_sequenceFin coordinate _ fun _ => by
    split
    · exact resolvedPreservesCoordinate_ensureTreeNode coordinate lay tree _ _
    · exact resolvedPreservesCoordinate_pure coordinate ()).bind fun _ => resolvedPreservesCoordinate_pure coordinate ()

def ResolvedPreservesCoordinateWhen (coordinate : Coordinate)
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (condition : α → Prop) : Prop :=
  ∀ context fuel table cache result,
    some result ∈ support (runResolvedFromTable context fuel table (computation.run cache)) →
    condition result.value.1 → result.context.state.values coordinate = context.state.values coordinate

theorem resolvedPreservesCoordinateWhen_sequenceFin (coordinate : Coordinate) {n : Nat}
    (computation : Fin n → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (condition : Fin n → α → Prop)
    (hcomponent : ∀ index, ResolvedPreservesCoordinateWhen coordinate (computation index) (condition index)) :
    ResolvedPreservesCoordinateWhen coordinate (sequenceFin computation) (fun values => ∀ index, condition index (values index)) := by
  induction n with
  | zero =>
      intro context fuel table cache result hresult _
      simp [sequenceFin, runResolvedFromTable] at hresult
      subst result
      rfl
  | succ n ih =>
      intro context fuel table cache result hresult hcondition
      rw [sequenceFin, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
      obtain ⟨headOption, hhead, hrest⟩ := hresult
      cases headOption with
      | none => simp at hrest
      | some head =>
          dsimp only at hrest
          rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hrest
          obtain ⟨tailOption, htail, hreturn⟩ := hrest
          cases tailOption with
          | none => simp at hreturn
          | some tail =>
              simp [runResolvedFromTable] at hreturn
              subst result
              have hheadPreserved := hcomponent 0 context fuel table cache head hhead (hcondition 0)
              have htailPreserved := ih (fun index : Fin n => computation index.succ)
                (fun index value => condition index.succ value) (fun index => hcomponent index.succ)
                head.context head.remaining head.table head.value.2 tail htail (fun index => hcondition index.succ)
              exact htailPreserved.trans hheadPreserved

def ResolvedPublishes (coordinate : Coordinate)
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ context fuel table cache result,
    some result ∈ support (runResolvedFromTable context fuel table (computation.run cache)) →
      coordinate ∈ result.context.state.revealed

theorem ResolvedPublishes.bind_left
    {coordinate : Coordinate}
    {left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (next : α → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) β)
    (hleft : ResolvedPublishes coordinate left) : ResolvedPublishes coordinate (left >>= next) := by
  intro context fuel table cache result hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨option, hleftSupport, hrest⟩ := hresult
  cases option with
  | none => simp at hrest
  | some middle =>
      exact (revealed_subset_of_mem_runResolvedFromTable _ middle.context middle.remaining middle.table result hrest)
        (hleft context fuel table cache middle hleftSupport)

theorem ResolvedPublishes.bind_right
    {coordinate : Coordinate}
    (left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    {next : α → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hnext : ∀ value, ResolvedPublishes coordinate (next value)) : ResolvedPublishes coordinate (left >>= next) := by
  intro context fuel table cache result hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨option, _hleft, hrest⟩ := hresult
  cases option with
  | none => simp at hrest
  | some middle =>
      exact hnext middle.value.1 middle.context middle.remaining middle.table middle.value.2 result hrest

theorem resolvedPublishes_publishCoordinate (coordinate : Coordinate) :
    ResolvedPublishes coordinate (publishCoordinate coordinate) := by
  intro context fuel table cache result hresult
  change some result ∈ support (runResolvedFromTable context fuel table
    (LazyRevealProbe.publishQuery coordinate >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.publishQuery, runResolvedFromTable_publish_query_bind] at hresult
  simp [runResolvedFromTable] at hresult
  subst result
  simp [LazyRevealProbe.State.publish]

theorem resolvedPublishes_revealPublishedCoordinate (coordinate : Coordinate) :
    ResolvedPublishes coordinate (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact ResolvedPublishes.bind_right _ fun _ => (resolvedPublishes_publishCoordinate coordinate).bind_left _

theorem resolvedPublishes_sequenceFin (coordinate : Coordinate) {n : Nat}
    (computation : Fin n → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (index : Fin n) (hcomponent : ResolvedPublishes coordinate (computation index)) :
    ResolvedPublishes coordinate (sequenceFin computation) := by
  induction n with
  | zero => exact index.elim0
  | succ n ih =>
      rw [sequenceFin]
      cases index using Fin.cases with
      | zero => exact hcomponent.bind_left _
      | succ index =>
          exact ResolvedPublishes.bind_right _ fun _ =>
            (ih (fun index : Fin n => computation index.succ) index hcomponent).bind_left _

theorem resolvedPublishes_revealLayerValues (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) (chainIdx : ChainIndex) :
    ResolvedPublishes
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx (encoding chainIdx))
      (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (resolvedPublishes_sequenceFin _ _ chainIdx (resolvedPublishes_revealPublishedCoordinate _)).bind_left _

theorem resolvedPreservesCoordinate_revealPublishedCoordinate_of_ne
    (coordinate published : Coordinate) (hne : coordinate ≠ published) :
    ResolvedPreservesCoordinate coordinate (revealPublishedCoordinate published) := by
  unfold revealPublishedCoordinate
  exact (resolvedPreservesCoordinate_revealCoordinate_of_ne coordinate published hne).bind fun _ =>
    (resolvedPreservesCoordinate_publish_of_ne coordinate published hne).bind fun _ =>
      resolvedPreservesCoordinate_pure coordinate _

theorem resolvedPreservesCoordinate_splitUniformImpl (coordinate : Coordinate) (n : Nat) :
    ResolvedPreservesCoordinate coordinate (splitUniformImpl n) := by
  intro context fuel table cache result hresult
  change some result ∈ support (runResolvedFromTable context fuel table
    (LazyRevealProbe.uniformQuery n >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.uniformQuery, runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
  obtain ⟨output, _houtput, hreturn⟩ := hresult
  simp [runResolvedFromTable] at hreturn
  subst result
  exact ⟨rfl, Iff.rfl⟩

theorem resolvedPreservesCoordinate_simulateQ_ordinaryRomImpl (coordinate : Coordinate)
    (computation : OracleComp OracleWorld α) :
    ResolvedPreservesCoordinate coordinate (simulateQ ordinaryRomImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact resolvedPreservesCoordinate_pure coordinate value
  | query_bind input next ih =>
      rw [simulateQ_query_bind]
      apply ResolvedPreservesCoordinate.bind ?_ ih
      cases input with
      | inl n => exact resolvedPreservesCoordinate_splitUniformImpl coordinate n
      | inr input => exact resolvedPreservesCoordinate_splitHashQuery coordinate (.ordinary input)

end SphincsSecurity.Concrete.OtsProbeSimulation
