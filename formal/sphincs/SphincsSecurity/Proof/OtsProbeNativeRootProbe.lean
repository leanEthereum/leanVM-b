import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootState
import SphincsSecurity.Proof.OtsProbePrivateValueExecution

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem NativePositionReplaceable.addPending
    {target : Position} {before after : HashOutput} {context : DeferredContext}
    (h : NativePositionReplaceable target before after context) (coordinate : Coordinate) (digest : Digest)
    (hsafe : ¬IsPrivateValueExposure target before after (.probe coordinate digest)) :
    NativePositionReplaceable target before after
      { context with state := context.state.addPending coordinate digest } := by
  refine ⟨h.known, h.consistent.addPending coordinate digest, ?_, ?_⟩
  all_goals
    intro hhit
    simp only [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff,
      LazyRevealProbe.State.addPending, Finset.mem_insert] at hhit
    rcases hhit with hhit | hhit
    · apply hsafe
      obtain ⟨hcoordinate, hdigest⟩ := Prod.mk.inj hhit
      exact ⟨hcoordinate.symm, by first | exact Or.inl hdigest.symm | exact Or.inr hdigest.symm⟩
    · first
      | apply h.beforeMiss
        simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] using hhit
      | apply h.afterMiss
        simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] using hhit

theorem NativeRootContextRel.addPending
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) (coordinate : Coordinate) (digest : Digest)
    (hsafe : ¬IsPrivateValueExposure target before after (.probe coordinate digest)) :
    NativeRootContextRel target before after
      { left with state := left.state.addPending coordinate digest }
      { right with state := right.state.addPending coordinate digest } := by
  refine ⟨h.replaceable.addPending coordinate digest hsafe, ?_⟩
  rw [h.right_eq]
  rfl

theorem NativeRootContextRel.revealed_eq
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) : left.state.revealed = right.state.revealed := by
  rw [h.right_eq]
  rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
