import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeEnsuredInitialization
import SphincsSecurity.Proof.OtsProbeNativeMaterializedCandidate
import SphincsSecurity.Proof.OtsProbePublicHashValues

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem MaterializedChainsPublished.of_public
    {context : DeferredContext} (hpublic : MaterializedValuesPublished context.state) :
    MaterializedChainsPublished context := by
  intro coordinate _ hknown
  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hknown
  exact hpublic coordinate output houtput

theorem materializedChainsPublished_of_mem_initializedRoot
    (targets : Finset Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult (Digest × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable (ensuredInitialContext targets) fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache))) : MaterializedChainsPublished result.context := by
  have hpreserves : ResolvedPreservesPublicMaterialization maskedPublishedTreeRoot := by
    unfold maskedPublishedTreeRoot
    exact (resolvedPreservesPublicMaterialization_ensureTreeNode topLayer rootTree (layerHeight topLayer) 0).bind
      fun _ => resolvedPreservesPublicMaterialization_revealPublishedCoordinate _
  apply MaterializedChainsPublished.of_public
  apply hpreserves _ emptySplitHashCache fuel table result _ hresult
  intro coordinate output hvalue
  simp [ensuredInitialContext, LazyRevealProbe.State.empty] at hvalue

def ResolvedPreservesChainMaterialization
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ context cache fuel table result, MaterializedChainsPublished context →
    some result ∈ support (runResolvedFromTable context fuel table (computation.run cache)) →
      MaterializedChainsPublished result.context

theorem ResolvedPreservesChainMaterialization.of_preservesCoordinate
    {computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (hpreserves : ∀ coordinate, ResolvedPreservesCoordinate coordinate computation) :
    ResolvedPreservesChainMaterialization computation := by
  intro context cache fuel table result hpublic hresult coordinate hchain hvalue
  have hcoordinate := hpreserves coordinate context fuel table cache result hresult
  exact hcoordinate.2.mpr (hpublic coordinate hchain (by rwa [hcoordinate.1] at hvalue))

theorem ResolvedPreservesChainMaterialization.pure (value : α) :
    ResolvedPreservesChainMaterialization (pure value) :=
  .of_preservesCoordinate fun coordinate => resolvedPreservesCoordinate_pure coordinate value

theorem ResolvedPreservesChainMaterialization.bind
    {left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : ResolvedPreservesChainMaterialization left)
    (hnext : ∀ value, ResolvedPreservesChainMaterialization (next value)) :
    ResolvedPreservesChainMaterialization (left >>= next) := by
  intro context cache fuel table result hpublic hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨leftOption, hleftSupport, hrest⟩ := hresult
  cases leftOption with
  | none => simp at hrest
  | some leftResult =>
      exact hnext leftResult.value.1 leftResult.context leftResult.value.2 leftResult.remaining
        leftResult.table result (hleft context cache fuel table leftResult hpublic hleftSupport) hrest

theorem resolvedPreservesChainMaterialization_reveal_publish (coordinate : Coordinate) :
    ResolvedPreservesChainMaterialization (do
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
          intro other hchain hvalue
          by_cases heq : other = coordinate
          · subst other
            simp [LazyRevealProbe.State.publish]
          · have hpreserved := resolvedPreservesCoordinate_revealCoordinateOutput_of_ne other coordinate heq
              context fuel table cache revealResult hreveal
            have hbefore : context.state.values other ≠ none := by
              rw [← hpreserved.1]
              exact hvalue
            have hrevealed := hpreserved.2.mpr (hpublic other hchain hbefore)
            simpa [LazyRevealProbe.State.publish, heq] using hrevealed

theorem resolvedPreservesChainMaterialization_resolveKnownInput
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput) :
    ResolvedPreservesChainMaterialization (resolveKnownInput parameter coordinate input) := by
  unfold resolveKnownInput
  apply (ResolvedPreservesChainMaterialization.of_preservesCoordinate fun other =>
    resolvedPreservesCoordinate_peekTableInput parameter other coordinate).bind
  intro known
  cases known with
  | none => exact .of_preservesCoordinate fun other => resolvedPreservesCoordinate_splitHashQuery other (.ordinary input)
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        have hpreserves := (resolvedPreservesChainMaterialization_reveal_publish coordinate).bind fun output =>
          (ResolvedPreservesChainMaterialization.of_preservesCoordinate fun other =>
            resolvedPreservesCoordinate_modify other fun cache =>
              Function.update cache (.ordinary input) (some output)).bind fun _ =>
                ResolvedPreservesChainMaterialization.pure output
        simpa only [bind_assoc, pure_bind] using hpreserves
      · simp only [heq, ↓reduceIte]
        exact .of_preservesCoordinate fun other => resolvedPreservesCoordinate_splitHashQuery other (.ordinary input)

theorem resolvedPreservesChainMaterialization_probingHashQuery
    (parameter : PublicParameter) (input : HashInput) :
    ResolvedPreservesChainMaterialization (probingHashQuery parameter input) := by
  intro context cache fuel table result hpublic hresult
  rw [runResolved_probingHashQuery_eq_afterPlan] at hresult
  let plan := purePlanProbingHashQuery parameter input context.state
  have hcandidate : ResolvedPreservesChainMaterialization (executeCandidate? plan.candidate?) := by
    cases plan.candidate? with
    | none => exact .pure ()
    | some candidate => exact .of_preservesCoordinate fun other => resolvedPreservesCoordinate_probe other candidate
  have haction : ResolvedPreservesChainMaterialization (probingHashQueryAfterPlan parameter input plan) := by
    unfold probingHashQueryAfterPlan executePlannedHashQuery
    apply hcandidate.bind
    intro _
    cases plan.action with
    | ordinary => exact .of_preservesCoordinate fun other => resolvedPreservesCoordinate_splitHashQuery other (.ordinary input)
    | resolve coordinate => exact resolvedPreservesChainMaterialization_resolveKnownInput parameter coordinate input
  exact haction context cache fuel table result hpublic hresult

end SphincsSecurity.Concrete.OtsProbeSimulation
