import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveObserver

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot

def MaterializedValuesPublished (state : LazyRevealProbe.State Coordinate) : Prop :=
  ∀ coordinate output, state.values coordinate = some output → coordinate ∈ state.revealed

def ResolvedPreservesPublicMaterialization
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ context cache fuel table result, MaterializedValuesPublished context.state →
    some result ∈ support (runResolvedFromTable context fuel table (computation.run cache)) →
      MaterializedValuesPublished result.context.state

theorem ResolvedPreservesPublicMaterialization.of_preservesCoordinate
    {computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (hpreserves : ∀ coordinate, ResolvedPreservesCoordinate coordinate computation) :
    ResolvedPreservesPublicMaterialization computation := by
  intro context cache fuel table result hpublic hresult coordinate output hvalue
  have hcoordinate := hpreserves coordinate context fuel table cache result hresult
  exact hcoordinate.2.mpr (hpublic coordinate output (hcoordinate.1.symm.trans hvalue))

theorem ResolvedPreservesPublicMaterialization.pure (value : α) :
    ResolvedPreservesPublicMaterialization (pure value) :=
  .of_preservesCoordinate fun coordinate => resolvedPreservesCoordinate_pure coordinate value

theorem ResolvedPreservesPublicMaterialization.bind
    {left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : ResolvedPreservesPublicMaterialization left)
    (hnext : ∀ value, ResolvedPreservesPublicMaterialization (next value)) :
    ResolvedPreservesPublicMaterialization (left >>= next) := by
  intro context cache fuel table result hpublic hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨leftOption, hleftSupport, hrest⟩ := hresult
  cases leftOption with
  | none => simp at hrest
  | some leftResult =>
      exact hnext leftResult.value.1 leftResult.context leftResult.value.2 leftResult.remaining
        leftResult.table result (hleft context cache fuel table leftResult hpublic hleftSupport) hrest

theorem resolvedPreservesPublicMaterialization_reveal_publish (coordinate : Coordinate) :
    ResolvedPreservesPublicMaterialization (do
      let output ← revealCoordinateOutput coordinate
      publishCoordinate coordinate
      pure output) := by
  intro context cache fuel table result hpublic hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨revealOption, hreveal, hrest⟩ := hresult
  cases revealOption with
  | none => simp at hrest
  | some revealResult =>
      simp only at hrest
      rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hrest
      obtain ⟨publishOption, hpublish, hreturn⟩ := hrest
      cases publishOption with
      | none => simp at hreturn
      | some publishResult =>
          simp [runResolvedFromTable] at hreturn
          subst result
          change some publishResult ∈ support (runResolvedFromTable revealResult.context
            revealResult.remaining revealResult.table
            (LazyRevealProbe.publishQuery coordinate >>= fun output => pure (output, revealResult.value.2))) at hpublish
          rw [LazyRevealProbe.publishQuery, runResolvedFromTable_publish_query_bind] at hpublish
          simp [runResolvedFromTable] at hpublish
          subst publishResult
          intro other output hvalue
          by_cases heq : other = coordinate
          · subst other
            simp [LazyRevealProbe.State.publish]
          · have hpreserved := resolvedPreservesCoordinate_revealCoordinateOutput_of_ne other coordinate heq
              context fuel table cache revealResult hreveal
            have hbefore : context.state.values other = some output := by
              rw [← hpreserved.1]
              exact hvalue
            have hrevealed := hpreserved.2.mpr (hpublic other output hbefore)
            simpa [LazyRevealProbe.State.publish, heq] using hrevealed

theorem resolvedPreservesPublicMaterialization_sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index, ResolvedPreservesPublicMaterialization (computation index)) :
    ResolvedPreservesPublicMaterialization (sequenceFin computation) := by
  induction n with
  | zero => simpa [sequenceFin] using ResolvedPreservesPublicMaterialization.pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun _ =>
        (ih (fun index : Fin n => computation index.succ) (fun index => hcomponent index.succ)).bind fun _ => .pure _

theorem resolvedPreservesPublicMaterialization_ensureOtsLeaf
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ResolvedPreservesPublicMaterialization (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  apply (resolvedPreservesPublicMaterialization_sequenceFin _ fun chainIdx => ?_).bind fun _ =>
    ResolvedPreservesPublicMaterialization.of_preservesCoordinate fun other => resolvedPreservesCoordinate_ensure other _
  unfold ensureFullChain
  exact (resolvedPreservesPublicMaterialization_sequenceFin _ fun _ =>
    ResolvedPreservesPublicMaterialization.of_preservesCoordinate fun other =>
      resolvedPreservesCoordinate_ensure other _).bind fun _ => .pure ()

theorem resolvedPreservesPublicMaterialization_ensureTreeNode
    (lay : Layer) (tree : TreeIndex) : ∀ level nodeIdx,
    ResolvedPreservesPublicMaterialization (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => by
      rw [ensureTreeNode]
      exact resolvedPreservesPublicMaterialization_ensureOtsLeaf lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (resolvedPreservesPublicMaterialization_ensureTreeNode lay tree level (2 * nodeIdx)).bind fun _ =>
        (resolvedPreservesPublicMaterialization_ensureTreeNode lay tree level (2 * nodeIdx + 1)).bind fun _ => by
          split
          · exact .of_preservesCoordinate fun other => resolvedPreservesCoordinate_ensure other _
          · exact .pure ()

theorem resolvedPreservesPublicMaterialization_revealPublishedCoordinate (coordinate : Coordinate) :
    ResolvedPreservesPublicMaterialization (revealPublishedCoordinate coordinate) := by
  have hpreserves := (resolvedPreservesPublicMaterialization_reveal_publish coordinate).bind fun output =>
    ResolvedPreservesPublicMaterialization.pure (truncateHash output)
  simpa only [revealPublishedCoordinate, revealCoordinate, bind_assoc, pure_bind] using hpreserves

end SphincsSecurity.Concrete.OtsProbeSimulation
