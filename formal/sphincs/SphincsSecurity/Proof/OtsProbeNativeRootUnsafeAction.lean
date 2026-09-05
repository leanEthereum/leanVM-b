import SphincsSecurity.Proof.OtsProbeNativeRootOuterCutStop
import SphincsSecurity.Proof.OtsProbeNativeStoredRootStructuralCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem purePeekTableInput_node_some_atPosition
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight) (nodeIdx : LeafIndex) (input : HashInput)
    (hinput : purePeekTableInput parameter state (.position (.node lay tree level nodeIdx)) = some input) :
    AtPosition parameter input (.node lay tree level nodeIdx) := by
  simp only [purePeekTableInput] at hinput
  cases hvalues : purePeekPositionValues state (Position.node lay tree level nodeIdx).children with
  | none => simp [hvalues] at hinput
  | some values =>
      simp only [hvalues, Option.some.injEq] at hinput
      exact ⟨values.flatMap digestBytes, hinput.symm⟩

theorem nativeRootActionSafe_failure_exposure_or_structuralCharge
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target) (before after : HashOutput)
    (input : HashInput) (action : PlannedHashAction) (left right : DeferredContext)
    (hcontext : NativeRootContextRel target before after left right)
    (hhidden : .position target ∉ left.state.revealed)
    (hunsafe : ¬NativeRootActionSafe parameter target input left right action) :
    action = .resolve (.position target) ∨ KnownHiddenStructuralRootQuery parameter input left := by
  cases action with
  | ordinary => exact False.elim (hunsafe trivial)
  | resolve coordinate =>
      by_cases htarget : coordinate = .position target
      · exact Or.inl (congrArg PlannedHashAction.resolve htarget)
      · have hne : purePeekTableInput parameter left.state coordinate ≠ purePeekTableInput parameter right.state coordinate :=
          fun heq => hunsafe (Or.inl ⟨htarget, heq⟩)
        obtain ⟨parent, leftInput, rightInput, hcoordinate, hmem, hleft, hright⟩ :=
          hcontext.purePeekTableInput_ne_imp_known_child parameter coordinate hne
        subst coordinate
        obtain ⟨lay, tree, level, nodeIdx, hparent⟩ := exists_node_of_layerRoot_mem_children hroot hmem
        have hat : AtPosition parameter input parent := by
          by_cases hmatch : purePeekTableInput parameter left.state (.position parent) = some input
          · rw [hparent] at hmatch ⊢
            exact purePeekTableInput_node_some_atPosition parameter left.state lay tree level nodeIdx input hmatch
          · have hmatchRight : purePeekTableInput parameter right.state (.position parent) = some input := by
              by_contra hmiss
              exact hunsafe (Or.inr ⟨hmatch, hmiss⟩)
            rw [hparent] at hmatchRight ⊢
            exact purePeekTableInput_node_some_atPosition parameter right.state lay tree level nodeIdx input hmatchRight
        exact Or.inr ⟨parent, target, hat, hroot, hmem, hhidden, by rw [hleft]; simp⟩

theorem nativeRootHashSafe_failure_exposure_or_charged_query
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target) (before after : HashOutput)
    (input : HashInput) (context : DeferredContext) (h : NativePositionReplaceable target before after context)
    (hhidden : .position target ∉ context.state.revealed)
    (hunsafe : ¬NativeRootHashSafe parameter target before after input context) :
    (EncodingInputGuessesRoot parameter target (truncateHash before) input ∨
      EncodingInputGuessesRoot parameter target (truncateHash after) input) ∨
    (∃ candidate, (purePlanProbingHashQuery parameter input context.state).candidate? = some candidate ∧
      IsPrivateValueExposure target before after (.probe candidate.coordinate candidate.candidate)) ∨
    (purePlanProbingHashQuery parameter input context.state).action = .resolve (.position target) ∨
      KnownHiddenStructuralRootQuery parameter input context := by
  have hfailure := nativeRootHashSafe_failure_classify parameter target before after input context hunsafe
  rw [h.replace_self] at hfailure
  rcases hfailure with hencoding | hprobe | haction
  · apply Or.inl
    by_cases hleft : EncodingInputGuessesRoot parameter target (truncateHash before) input
    · exact Or.inl hleft
    · apply Or.inr
      by_contra hright
      exact hencoding ⟨hleft, hright⟩
  · exact Or.inr (Or.inl hprobe)
  · exact Or.inr (Or.inr (nativeRootActionSafe_failure_exposure_or_structuralCharge parameter target hroot before after input _
      context (replaceNativePosition target after context) ⟨h, rfl⟩ hhidden haction))

end SphincsSecurity.Concrete.OtsProbeSimulation
