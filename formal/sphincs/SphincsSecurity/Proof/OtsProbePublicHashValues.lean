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

theorem resolvedPreservesPublicMaterialization_resolveKnownInput
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput) :
    ResolvedPreservesPublicMaterialization (resolveKnownInput parameter coordinate input) := by
  unfold resolveKnownInput
  apply (ResolvedPreservesPublicMaterialization.of_preservesCoordinate fun other =>
    resolvedPreservesCoordinate_peekTableInput parameter other coordinate).bind
  intro known
  cases known with
  | none => exact .of_preservesCoordinate fun other => resolvedPreservesCoordinate_splitHashQuery other (.ordinary input)
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        have hpreserves := (resolvedPreservesPublicMaterialization_reveal_publish coordinate).bind fun output =>
          (ResolvedPreservesPublicMaterialization.of_preservesCoordinate fun other =>
            resolvedPreservesCoordinate_modify other fun cache =>
              Function.update cache (.ordinary input) (some output)).bind fun _ =>
                ResolvedPreservesPublicMaterialization.pure output
        simpa only [bind_assoc, pure_bind] using hpreserves
      · simp only [heq, ↓reduceIte]
        exact .of_preservesCoordinate fun other => resolvedPreservesCoordinate_splitHashQuery other (.ordinary input)

theorem resolvedPreservesPublicMaterialization_probeFirstMissingInputCoordinate
    (input : HashInput) : ∀ slot coordinates,
    ResolvedPreservesPublicMaterialization (probeFirstMissingInputCoordinate input slot coordinates)
  | _, [] => .pure ()
  | slot, coordinate :: remaining => by
      rw [probeFirstMissingInputCoordinate]
      exact (ResolvedPreservesPublicMaterialization.of_preservesCoordinate fun other =>
        resolvedPreservesCoordinate_peekCoordinate other coordinate).bind fun value =>
          match value with
          | none => .of_preservesCoordinate fun other =>
              resolvedPreservesCoordinate_probe other ⟨coordinate, slotDigest slot input⟩
          | some _ => resolvedPreservesPublicMaterialization_probeFirstMissingInputCoordinate input (slot + 1) remaining

theorem resolvedPreservesPublicMaterialization_prepareLeafInputProbe
    (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ResolvedPreservesPublicMaterialization (prepareLeafInputProbe input candidate lay tree leafIdx) := by
  unfold prepareLeafInputProbe
  apply (ResolvedPreservesPublicMaterialization.of_preservesCoordinate fun other =>
    resolvedPreservesCoordinate_peekCoordinate other candidate.coordinate).bind
  intro value
  cases value with
  | none => exact .of_preservesCoordinate fun other => resolvedPreservesCoordinate_probe other candidate
  | some output =>
      exact resolvedPreservesPublicMaterialization_probeFirstMissingInputCoordinate input 0
        ((Position.leaf lay tree leafIdx).children.map Coordinate.position)

theorem resolvedPreservesPublicMaterialization_probingHashQuery
    (parameter : PublicParameter) (input : HashInput) :
    ResolvedPreservesPublicMaterialization (probingHashQuery parameter input) := by
  unfold probingHashQuery
  cases decodeProbe? parameter input with
  | some candidate =>
      cases decodePosition? parameter input with
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              exact (resolvedPreservesPublicMaterialization_prepareLeafInputProbe input candidate lay tree leafIdx).bind
                fun _ => resolvedPreservesPublicMaterialization_resolveKnownInput parameter candidate.outputCoordinate input
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              exact (ResolvedPreservesPublicMaterialization.of_preservesCoordinate fun other =>
                resolvedPreservesCoordinate_probe other candidate).bind fun _ =>
                  resolvedPreservesPublicMaterialization_resolveKnownInput parameter candidate.outputCoordinate input
      | none =>
          exact (ResolvedPreservesPublicMaterialization.of_preservesCoordinate fun other =>
            resolvedPreservesCoordinate_probe other candidate).bind fun _ =>
              resolvedPreservesPublicMaterialization_resolveKnownInput parameter candidate.outputCoordinate input
  | none =>
      cases decodePosition? parameter input with
      | none => exact .of_preservesCoordinate fun other => resolvedPreservesCoordinate_splitHashQuery other (.ordinary input)
      | some position =>
          cases position with
          | chain | leaf => exact resolvedPreservesPublicMaterialization_resolveKnownInput parameter _ input
          | node lay tree level nodeIdx =>
              exact (resolvedPreservesPublicMaterialization_probeFirstMissingInputCoordinate input 0
                ((Position.node lay tree level nodeIdx).children.map Coordinate.position)).bind fun _ =>
                  resolvedPreservesPublicMaterialization_resolveKnownInput parameter _ input
          | ftsLeaf | ftsNode | ftsRoots =>
              exact .of_preservesCoordinate fun other => resolvedPreservesCoordinate_splitHashQuery other (.ordinary input)

theorem resolvedPreservesPublicMaterialization_splitUniformImpl (n : Nat) :
    ResolvedPreservesPublicMaterialization (splitUniformImpl n) := by
  intro context cache fuel table result hpublic hresult
  change some result ∈ support (runResolvedFromTable context fuel table
    (LazyRevealProbe.uniformQuery n >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.uniformQuery, runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
  obtain ⟨output, _houtput, hdone⟩ := hresult
  simp [runResolvedFromTable] at hdone
  subst result
  exact hpublic

theorem resolvedPreservesPublicMaterialization_probingRomImpl
    (parameter : PublicParameter) (query : OracleWorld.Domain) :
    ResolvedPreservesPublicMaterialization (probingRomImpl parameter query) := by
  cases query with
  | inl n => exact resolvedPreservesPublicMaterialization_splitUniformImpl n
  | inr input => exact resolvedPreservesPublicMaterialization_probingHashQuery parameter input

theorem MaterializedValuesPublished.of_canonical
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcanonical : CanonicalMaterializedValues table context) : MaterializedValuesPublished context.state := by
  intro coordinate output hvalue
  rw [hcanonical] at hvalue
  by_contra hnot
  simp [publicMaterializedValues, hnot] at hvalue

theorem canonicalMaterializedValues_of_public
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hpublic : MaterializedValuesPublished context.state)
    (hpublished : PublishedValues context.state) (hstarts : StartTableAgrees context.state table) :
    CanonicalMaterializedValues table context := by
  funext coordinate
  cases hvalue : context.state.values coordinate with
  | none =>
      have hnot : coordinate ∉ context.state.revealed := fun h => hpublished coordinate h hvalue
      simp [publicMaterializedValues, hnot]
  | some output =>
      have hrevealed := hpublic coordinate output hvalue
      simp only [publicMaterializedValues, hrevealed, ↓reduceIte]
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          have heq := hstarts ⟨lay, tree, leafIdx, chainIdx⟩ output hvalue
          simp [resolvedCompletionValue, heq]
      | position position => simp [resolvedCompletionValue, DeferredContext.positionValue, hvalue]

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

theorem canonicalMaterializedValues_of_mem_maskedPublishedTreeRoot
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) (fuel : Nat)
    (result : ResolvedRunResult (Digest × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable
      { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
      fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    CanonicalMaterializedValues table result.context := by
  have hpreserves : ResolvedPreservesPublicMaterialization maskedPublishedTreeRoot := by
    unfold maskedPublishedTreeRoot
    exact (resolvedPreservesPublicMaterialization_ensureTreeNode topLayer rootTree (layerHeight topLayer) 0).bind
      fun _ => resolvedPreservesPublicMaterialization_revealPublishedCoordinate _
  have hpublic := hpreserves _ emptySplitHashCache fuel table result (by
    intro coordinate output hvalue
    simp [LazyRevealProbe.State.empty] at hvalue) hresult
  have hcore := resolvedCore_of_mem_runResolved_maskedPublishedTreeRoot parameter table fuel result hresult
  have hpubPreserves : ResolvedPreservesPublished maskedPublishedTreeRoot := by
    unfold maskedPublishedTreeRoot
    exact (resolvedPreservesPublishedValues_ensureTreeNode topLayer rootTree (layerHeight topLayer) 0).bind
      fun _ => resolvedPreservesPublishedValues_revealPublishedCoordinate _
  have hpublished := hpubPreserves _ emptySplitHashCache fuel table result publishedValues_empty hresult
  exact canonicalMaterializedValues_of_public hpublic hpublished hcore.2.2

end SphincsSecurity.Concrete.OtsProbeSimulation
