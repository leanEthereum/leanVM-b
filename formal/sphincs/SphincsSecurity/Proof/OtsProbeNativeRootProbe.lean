import SphincsSecurity.Proof.OtsProbeNativeRootInputObservation

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

theorem nativeRootRelates_probe_of_safe
    (target : Position) (before after : HashOutput) (candidate : Probe)
    (hsafe : ¬IsPrivateValueExposure target before after (.probe candidate.coordinate candidate.candidate)) :
    NativeRootRelates target before after (probe candidate) (probe candidate) := by
  intro left right hcontext fuel table leftCache rightCache hcache
  unfold probe
  rw [StateT.run_liftM, StateT.run_liftM]
  unfold LazyRevealProbe.probeQuery
  rw [runResolvedFromTable_probe_query_bind, runResolvedFromTable_probe_query_bind]
  cases fuel with
  | zero => exact relTriple_pure_pure trivial
  | succ fuel =>
      simp only
      rw [← hcontext.revealed_eq]
      by_cases hrevealed : candidate.coordinate ∈ left.state.revealed
      · rw [if_pos hrevealed, if_pos hrevealed]
        exact relTriple_pure_pure ⟨hcontext, rfl, rfl, rfl, hcache⟩
      · rw [if_neg hrevealed, if_neg hrevealed]
        exact relTriple_pure_pure ⟨hcontext.addPending candidate.coordinate candidate.candidate hsafe, rfl, rfl, rfl, hcache⟩

theorem nativeRootRelates_executeCandidate_of_safe
    (target : Position) (before after : HashOutput) (candidate : Option Probe)
    (hsafe : ∀ value, candidate = some value →
      ¬IsPrivateValueExposure target before after (.probe value.coordinate value.candidate)) :
    NativeRootRelates target before after (executeCandidate? candidate) (executeCandidate? candidate) := by
  cases candidate with
  | none => exact nativeRootRelates_pure target before after ()
  | some candidate => exact nativeRootRelates_probe_of_safe target before after candidate (hsafe candidate rfl)

end SphincsSecurity.Concrete.OtsProbeSimulation
