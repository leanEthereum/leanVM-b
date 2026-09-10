import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeValueReplacement

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem DeferredCompletable.of_replaceNativePosition
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcomplete : DeferredCompletable table context) (target : Position) (output : HashOutput)
    (hclean : ¬context.state.hitAt (.position target) output) :
    DeferredCompletable table (replaceNativePosition target output context) := by
  obtain ⟨completion, hcompletion⟩ := hcomplete
  refine ⟨Function.update completion (.position target) output, ?_, ?_, ?_, ?_⟩
  · intro coordinate value hvalue
    change Function.update context.state.values (.position target)
      ((context.state.values (.position target)).map fun _ => output) coordinate = some value at hvalue
    by_cases heq : coordinate = .position target
    · subst coordinate
      rw [Function.update_self] at hvalue
      have hsame : output = value := by
        cases hstate : context.state.values (.position target) <;> simp_all
      simpa using hsame
    · rw [Function.update_of_ne heq] at hvalue ⊢
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

theorem deferredCompletable_replaceNativePosition_iff
    (target : Position) (before after : HashOutput) (context : DeferredContext)
    (table : OtsSecretIndex → HashOutput)
    (h : NativePositionReplaceable target before after context) :
    DeferredCompletable table (replaceNativePosition target after context) ↔
      DeferredCompletable table context := by
  constructor
  · intro hcomplete
    have hback := hcomplete.of_replaceNativePosition target before h.beforeMiss
    simpa only [replaceNativePosition_inverse h] using hback
  · intro hcomplete
    exact hcomplete.of_replaceNativePosition target after h.afterMiss

theorem NativePositionReplaceable.reverse
    {target : Position} {before after : HashOutput} {context : DeferredContext}
    (h : NativePositionReplaceable target before after context) :
    NativePositionReplaceable target after before (replaceNativePosition target after context) :=
  ⟨replaceNativePosition_positionValue target after context,
    h.consistent.of_replaceNativePosition target after, h.afterMiss, h.beforeMiss⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
