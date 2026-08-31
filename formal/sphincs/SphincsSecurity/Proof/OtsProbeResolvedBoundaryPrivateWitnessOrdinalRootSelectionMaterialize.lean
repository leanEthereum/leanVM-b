import SphincsSecurity.Proof.OtsProbeResolvedBoundaryOrdinarySigner
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionSigner

/-!
# Materialized shadow of a deferred boundary

Only structural outputs already present in `DeferredContext.values` are copied into the shadow
state. No missing output is sampled. The shadow therefore gives the existing directional signer
coupling a fully materialized right context while preserving the completed value at every
coordinate.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def materializedDeferredState (context : DeferredContext) :
    LazyRevealProbe.State Coordinate :=
  { context.state with
    values := fun coordinate =>
      match coordinate with
      | .chainStart lay tree leafIdx chainIdx =>
          context.state.values (.chainStart lay tree leafIdx chainIdx)
      | .position position => context.positionValue position }

def materializedDeferredContext (context : DeferredContext) : DeferredContext :=
  directDeferredContext (materializedDeferredState context)

@[simp] theorem materializedDeferredState_pending (context : DeferredContext) :
    (materializedDeferredState context).pending = context.state.pending := rfl

@[simp] theorem materializedDeferredState_revealed (context : DeferredContext) :
    (materializedDeferredState context).revealed = context.state.revealed := rfl

@[simp] theorem materializedDeferredState_ensured (context : DeferredContext) :
    (materializedDeferredState context).ensured = context.state.ensured := rfl

@[simp] theorem materializedDeferredState_chainStart
    (context : DeferredContext) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    (materializedDeferredState context).values
        (.chainStart lay tree leafIdx chainIdx) =
      context.state.values (.chainStart lay tree leafIdx chainIdx) := rfl

@[simp] theorem materializedDeferredState_position
    (context : DeferredContext) (position : Position) :
    (materializedDeferredState context).values (.position position) =
      context.positionValue position := rfl

theorem resolvedCompletionValue_materializedDeferredContext
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) :
    resolvedCompletionValue table (materializedDeferredContext context) =
      resolvedCompletionValue table context := by
  funext coordinate
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx => rfl
  | position position =>
      change (match context.positionValue position with
        | some output => some output
        | none => context.positionValue position) = context.positionValue position
      cases context.positionValue position <;> rfl

theorem valuesLE_materializedDeferredState (context : DeferredContext) :
    LazyRevealProbe.ValuesLE context.state (materializedDeferredState context) := by
  intro coordinate output hvalue
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx => exact hvalue
  | position position =>
      simp only [materializedDeferredState_position]
      simp [DeferredContext.positionValue, hvalue]

theorem clean_of_deferredCompletion
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hcompletion : DeferredCompletion table context completion) :
    ∀ coordinate output,
      resolvedCompletionValue table context coordinate = some output →
      ¬context.state.hitAt coordinate output := by
  intro coordinate output hvalue hhit
  have hcompletionValue := hcompletion.eq_resolvedCompletionValue coordinate output hvalue
  unfold LazyRevealProbe.State.hitAt at hhit
  rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
  exact hcompletion.2.2.1 coordinate (truncateHash output) hhit
    (by rw [hcompletionValue])

theorem deferredCompletion_materializedDeferredContext
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hcompletion : DeferredCompletion table context completion) :
    DeferredCompletion table (materializedDeferredContext context) completion := by
  refine ⟨?_, ?_, ?_, hcompletion.2.2.2⟩
  · intro coordinate output hvalue
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx =>
        apply hcompletion.1 (.chainStart lay tree leafIdx chainIdx) output
        exact hvalue
    | position position =>
        have hresolved : resolvedCompletionValue table context (.position position) =
            some output := by
          simpa [materializedDeferredContext, directDeferredContext,
            materializedDeferredState, resolvedCompletionValue] using hvalue
        exact hcompletion.eq_resolvedCompletionValue (.position position) output hresolved
  · intro position output hvalue
    have hresolved : resolvedCompletionValue table context (.position position) =
        some output := by
      simpa [materializedDeferredContext, directDeferredContext, directDeferredValues,
        materializedDeferredState, resolvedCompletionValue] using hvalue
    exact hcompletion.eq_resolvedCompletionValue (.position position) output hresolved
  · intro coordinate candidate hmember
    exact hcompletion.2.2.1 coordinate candidate hmember

theorem valid_materializedDeferredContext
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    (materializedDeferredContext context).Valid := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  refine ⟨?_, ?_⟩
  · intro position output hvalue
    exact hvalue
  · intro coordinate output hvalue
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx =>
        apply hvalid.2 (.chainStart lay tree leafIdx chainIdx) output
        simpa [materializedDeferredContext, directDeferredContext,
          materializedDeferredState] using hvalue
    | position position =>
        apply clean_of_deferredCompletion hcompletion (.position position) output
        simpa [materializedDeferredContext, directDeferredContext,
          materializedDeferredState, resolvedCompletionValue] using hvalue

theorem finalizationContextLE_materializedDeferredContext
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    FinalizationContextLE table context (materializedDeferredContext context) := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  have hclean := clean_of_deferredCompletion hcompletion
  refine
    { view :=
        { leftConsistent := hvalid.valuesConsistent
          rightConsistent :=
            (valid_materializedDeferredContext hvalid ⟨completion, hcompletion⟩).valuesConsistent
          leftStarts := ?_
          rightStarts := ?_
          valueEq := resolvedCompletionValue_materializedDeferredContext table context |>.symm
          leftClean := hclean
          rightClean := ?_
          pendingLE := ?_ }
      leftValid := hvalid
      rightValid := valid_materializedDeferredContext hvalid ⟨completion, hcompletion⟩
      rightCompletable :=
        ⟨completion, deferredCompletion_materializedDeferredContext hcompletion⟩ }
  · intro index output hvalue
    exact (hcompletion.1 index.coordinate output hvalue).symm.trans
      (hcompletion.2.2.2 index)
  · intro index output hvalue
    rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
    have hleftValue : context.state.values (.chainStart lay tree leafIdx chainIdx) =
        some output := by
      simpa [materializedDeferredContext, directDeferredContext,
        materializedDeferredState, OtsSecretIndex.coordinate] using hvalue
    exact (hcompletion.1 (.chainStart lay tree leafIdx chainIdx) output hleftValue).symm.trans
      (hcompletion.2.2.2
        (⟨lay, tree, leafIdx, chainIdx⟩ : OtsSecretIndex))
  · intro coordinate output hvalue
    apply clean_of_deferredCompletion
      (deferredCompletion_materializedDeferredContext hcompletion) coordinate output hvalue
  · intro coordinate _hvalue candidate hcandidate
    exact hcandidate

theorem RootDeferredContextRel.materialized
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : DeferredContext}
    (hrel : RootDeferredContextRel target leftOutput rightOutput left right) :
    RootMaterializedContextRel target leftOutput rightOutput
      (materializedDeferredContext left) (materializedDeferredContext right) := by
  have hstate : RootHiddenStateRel target leftOutput rightOutput
      (materializedDeferredState left) (materializedDeferredState right) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hrel.state]
    · simp [hrel.state]
    · simp [hrel.state]
    · simpa using hrel.target_private
    · simp [hrel.positionValue_target.1]
    · simp [hrel.positionValue_target.2]
    · intro coordinate hne
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          simpa [materializedDeferredState] using congrArg
            (fun state => state.values (.chainStart lay tree leafIdx chainIdx)) hrel.state
      | position position =>
          have hposition : position ≠ target := by
            intro heq
            apply hne
            rw [heq]
          exact hrel.positionValue_other position hposition
  refine ⟨hstate, ?_, ?_, ?_⟩
  · simp [materializedDeferredContext, directDeferredContext,
      directDeferredValues, hrel.positionValue_target.1]
  · simp [materializedDeferredContext, directDeferredContext,
      directDeferredValues, hrel.positionValue_target.2]
  · intro position hne
    simp only [materializedDeferredContext, directDeferredContext,
      directDeferredValues, materializedDeferredState_position]
    exact hrel.positionValue_other position hne

theorem RootHiddenStateRel.directContext
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : RootHiddenStateRel target leftOutput rightOutput left right) :
    RootMaterializedContextRel target leftOutput rightOutput
      (directDeferredContext left) (directDeferredContext right) := by
  refine ⟨hrel, ?_, ?_, ?_⟩
  · simpa [directDeferredContext, directDeferredValues] using hrel.left_target
  · simpa [directDeferredContext, directDeferredValues] using hrel.right_target
  · intro position hne
    apply hrel.other_values (.position position)
    simpa using hne

end SphincsSecurity.Concrete.OtsProbeSimulation
