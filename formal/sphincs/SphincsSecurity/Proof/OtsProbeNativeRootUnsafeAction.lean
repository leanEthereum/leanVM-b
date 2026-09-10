import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootHashAction
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

end SphincsSecurity.Concrete.OtsProbeSimulation
