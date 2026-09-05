import SphincsSecurity.Proof.OtsProbePrivateValueReplacement

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem DeferredCompletable.replacePrivatePosition
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcomplete : DeferredCompletable table context) (target : Position) (output : HashOutput)
    (hstate : context.state.values (.position target) = none) (hclean : ¬context.state.hitAt (.position target) output) :
    DeferredCompletable table (replacePrivatePosition target output context) := by
  obtain ⟨completion, hcompletion⟩ := hcomplete
  refine ⟨Function.update completion (.position target) output, ?_, ?_, ?_, ?_⟩
  · intro coordinate value hvalue
    change context.state.values coordinate = some value at hvalue
    by_cases heq : coordinate = .position target
    · subst coordinate
      simp [hstate] at hvalue
    · rw [Function.update_of_ne heq]
      exact hcompletion.1 coordinate value hvalue
  · intro position value hvalue
    change Function.update context.values target (some output) position = some value at hvalue
    by_cases heq : position = target
    · subst position
      simp only [Function.update_self, Option.some.injEq] at hvalue
      simp [hvalue]
    · rw [Function.update_of_ne heq] at hvalue
      rw [Function.update_of_ne (by simpa using heq)]
      exact hcompletion.2.1 position value hvalue
  · intro coordinate candidate hpending
    change (coordinate, candidate) ∈ context.state.pending at hpending
    by_cases heq : coordinate = .position target
    · subst coordinate
      rw [Function.update_self]
      intro hhit
      apply hclean
      change truncateHash output ∈ context.state.pendingAt (.position target)
      rw [LazyRevealProbe.State.mem_pendingAt_iff, hhit]
      exact hpending
    · rw [Function.update_of_ne heq]
      exact hcompletion.2.2.1 coordinate candidate hpending
  · intro index
    rw [Function.update_of_ne (by cases index; simp [OtsSecretIndex.coordinate])]
    exact hcompletion.2.2.2 index

theorem deferredCompletable_replacePrivatePosition_iff
    (target : Position) (before after : HashOutput) (context : DeferredContext) (table : OtsSecretIndex → HashOutput)
    (hreplaceable : PrivatePositionReplaceable target before after context) :
    DeferredCompletable table (replacePrivatePosition target after context) ↔ DeferredCompletable table context := by
  constructor
  · intro hcomplete
    have hback := hcomplete.replacePrivatePosition target before hreplaceable.1 hreplaceable.2.2.1
    have hupdate : Function.update context.values target (some before) = context.values := by
      rw [← hreplaceable.2.1]
      exact Function.update_eq_self _ _
    simpa only [replacePrivatePosition, DeferredStructuralValues.install, Function.update_idem, hupdate] using hback
  · intro hcomplete
    exact hcomplete.replacePrivatePosition target after hreplaceable.1 hreplaceable.2.2.2

end SphincsSecurity.Concrete.OtsProbeSimulation
