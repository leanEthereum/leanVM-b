import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootStateHash

/-!
# Canonical deferred swapped roots

Between adaptive queries the selected layer root is absent from the visible lazy state and retained
only in the private structural table. The two executions therefore have equal public state and may
differ at exactly that deferred table cell.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

structure RootDeferredContextRel
    (target : Position) (leftOutput rightOutput : HashOutput)
    (left right : DeferredContext) : Prop where
  state : left.state = right.state
  target_hidden : left.state.values (.position target) = none
  target_private : Coordinate.position target ∉ left.state.revealed
  left_target : left.values target = some leftOutput
  right_target : right.values target = some rightOutput
  other_values : ∀ position, position ≠ target →
    left.values position = right.values position

theorem RootDeferredContextRel.symm
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : DeferredContext}
    (hrel : RootDeferredContextRel target leftOutput rightOutput left right) :
    RootDeferredContextRel target rightOutput leftOutput right left := by
  refine ⟨hrel.state.symm, ?_, ?_, hrel.right_target, hrel.left_target, ?_⟩
  · rw [← hrel.state]
    exact hrel.target_hidden
  · intro hmem
    apply hrel.target_private
    rwa [hrel.state]
  · intro position hne
    exact (hrel.other_values position hne).symm

theorem rootDeferredContextRel_install
    (target : Position) (leftOutput rightOutput : HashOutput)
    (context : DeferredContext)
    (hhidden : context.state.values (.position target) = none)
    (hprivate : Coordinate.position target ∉ context.state.revealed) :
    RootDeferredContextRel target leftOutput rightOutput
      { context with values := context.values.install target leftOutput }
      { context with values := context.values.install target rightOutput } := by
  refine ⟨rfl, hhidden, hprivate, ?_, ?_, ?_⟩
  · simp [DeferredStructuralValues.install]
  · simp [DeferredStructuralValues.install]
  · intro position hne
    simp [DeferredStructuralValues.install, Function.update_of_ne hne]

theorem RootDeferredContextRel.positionValue_other
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : DeferredContext}
    (hrel : RootDeferredContextRel target leftOutput rightOutput left right)
    (position : Position) (hne : position ≠ target) :
    left.positionValue position = right.positionValue position := by
  unfold DeferredContext.positionValue
  rw [hrel.state]
  cases right.state.values (.position position) with
  | some output => rfl
  | none => exact hrel.other_values position hne

theorem RootDeferredContextRel.positionValue_target
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : DeferredContext}
    (hrel : RootDeferredContextRel target leftOutput rightOutput left right) :
    left.positionValue target = some leftOutput ∧
      right.positionValue target = some rightOutput := by
  unfold DeferredContext.positionValue
  have hrightHidden : right.state.values (.position target) = none := by
    rw [← hrel.state]
    exact hrel.target_hidden
  rw [hrel.target_hidden, hrightHidden]
  exact ⟨hrel.left_target, hrel.right_target⟩

theorem RootDeferredContextRel.ensure
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : DeferredContext}
    (hrel : RootDeferredContextRel target leftOutput rightOutput left right)
    (coordinate : Coordinate) :
    RootDeferredContextRel target leftOutput rightOutput
      { left with state := left.state.ensure coordinate }
      { right with state := right.state.ensure coordinate } := by
  refine ⟨by simp [hrel.state], hrel.target_hidden, hrel.target_private,
    hrel.left_target, hrel.right_target, hrel.other_values⟩

theorem RootDeferredContextRel.addPending
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : DeferredContext}
    (hrel : RootDeferredContextRel target leftOutput rightOutput left right)
    (coordinate : Coordinate) (candidate : Digest) :
    RootDeferredContextRel target leftOutput rightOutput
      { left with state := left.state.addPending coordinate candidate }
      { right with state := right.state.addPending coordinate candidate } := by
  refine ⟨by simp [hrel.state], hrel.target_hidden, hrel.target_private,
    hrel.left_target, hrel.right_target, hrel.other_values⟩

theorem RootDeferredContextRel.publish_of_ne
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : DeferredContext}
    (hrel : RootDeferredContextRel target leftOutput rightOutput left right)
    (coordinate : Coordinate) (hne : coordinate ≠ .position target) :
    RootDeferredContextRel target leftOutput rightOutput
      { left with state := left.state.publish coordinate }
      { right with state := right.state.publish coordinate } := by
  refine ⟨by simp [hrel.state], hrel.target_hidden, ?_,
    hrel.left_target, hrel.right_target, hrel.other_values⟩
  simp [LazyRevealProbe.State.publish, hrel.target_private, Ne.symm hne]

theorem RootDeferredContextRel.canonicalize
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : DeferredContext}
    (hrel : RootDeferredContextRel target leftOutput rightOutput left right)
    (table : OtsSecretIndex → HashOutput) :
    RootDeferredContextRel target leftOutput rightOutput
      (canonicalizeMaterializedValues table left)
      (canonicalizeMaterializedValues table right) := by
  have hpublic : publicMaterializedValues table left = publicMaterializedValues table right := by
    funext coordinate
    unfold publicMaterializedValues
    have hreveal : left.state.revealed = right.state.revealed := congrArg _ hrel.state
    by_cases hrevealed : coordinate ∈ left.state.revealed
    · have hrightRevealed : coordinate ∈ right.state.revealed := by rwa [← hreveal]
      simp only [hrevealed, hrightRevealed, ↓reduceIte]
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          simp [resolvedCompletionValue]
      | position position =>
          have hne : position ≠ target := by
            intro heq
            subst position
            exact hrel.target_private hrevealed
          simp [resolvedCompletionValue, hrel.positionValue_other position hne]
    · have hrightRevealed : coordinate ∉ right.state.revealed := by
        intro hmem
        exact hrevealed (by rwa [hreveal])
      simp [hrevealed, hrightRevealed]
  refine ⟨?_, ?_, ?_, hrel.left_target, hrel.right_target, hrel.other_values⟩
  · unfold canonicalizeMaterializedValues
    simp [hrel.state, hpublic]
  · unfold canonicalizeMaterializedValues publicMaterializedValues
    simp [hrel.target_private]
  · simpa [canonicalizeMaterializedValues_revealed] using hrel.target_private

end SphincsSecurity.Concrete.OtsProbeSimulation
