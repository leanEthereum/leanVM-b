import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveClean

/-!
# Structural boundary first fire

Canonical signer boundaries hide materialized values that were not published while retaining their
private structural copy. A later probe can make such a context impossible only by naming the
truncated private value. This file isolates that exact discrepancy from ordinary clean execution.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

def PrivateStructuralHit (context : DeferredContext) : Prop :=
  ∃ position output,
    context.state.values (.position position) = none ∧
      context.values position = some output ∧
      context.state.hitAt (.position position) output

theorem DeferredCompletion.not_privateStructuralHit
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hcompletion : DeferredCompletion table context completion) :
    ¬PrivateStructuralHit context := by
  rintro ⟨position, output, _hhidden, hprivate, hhit⟩
  have hcompletionOutput : completion (.position position) = output :=
    hcompletion.2.1 position output hprivate
  have hpending :
      (Coordinate.position position, truncateHash output) ∈ context.state.pending := by
    rw [← LazyRevealProbe.State.mem_pendingAt_iff]
    exact hhit
  have havoids := hcompletion.2.2.1 (.position position) (truncateHash output) hpending
  rw [hcompletionOutput] at havoids
  exact havoids rfl

theorem not_privateStructuralHit_of_deferredCompletable
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) :
    ¬PrivateStructuralHit context := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  exact hcompletion.not_privateStructuralHit

theorem privateStructuralHit_addPending_iff
    (context : DeferredContext) (position : Position) (output : HashOutput)
    (candidate : Digest)
    (hclean : ¬PrivateStructuralHit context)
    (hhidden : context.state.values (.position position) = none)
    (hprivate : context.values position = some output) :
    PrivateStructuralHit
        { context with
          state := context.state.addPending (.position position) candidate } ↔
      truncateHash output = candidate := by
  constructor
  · rintro ⟨other, otherOutput, hotherHidden, hotherPrivate, hotherHit⟩
    by_cases heq : other = position
    · subst other
      have houtput : otherOutput = output := by
        rw [hprivate] at hotherPrivate
        exact Option.some.inj hotherPrivate.symm
      subst otherOutput
      rw [hitAt_addPending_self_iff] at hotherHit
      exact hotherHit.resolve_left fun hold =>
        hclean ⟨position, output, hhidden, hprivate, hold⟩
    · have hcoordinate : Coordinate.position position ≠ .position other := by
        intro hcoordinate
        exact heq (Coordinate.position.inj hcoordinate).symm
      have holdHit : context.state.hitAt (.position other) otherOutput := by
        simpa only [hitAt_addPending_of_ne context.state (.position position)
          (.position other) candidate otherOutput hcoordinate] using hotherHit
      exact False.elim (hclean ⟨other, otherOutput, hotherHidden, hotherPrivate, holdHit⟩)
  · intro hcandidate
    refine ⟨position, output, hhidden, hprivate, ?_⟩
    exact (hitAt_addPending_self_iff context.state (.position position) candidate output).2
      (Or.inr hcandidate)

theorem deferredCompletable_addPending_position_iff
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (position : Position) (output : HashOutput) (candidate : Digest)
    (hcompletion : DeferredCompletion table context completion)
    (hprivate : context.values position = some output) :
    DeferredCompletable table
        { context with
          state := context.state.addPending (.position position) candidate } ↔
      truncateHash output ≠ candidate := by
  constructor
  · rintro ⟨nextCompletion, hnextCompletion⟩
    have hnextOutput : nextCompletion (.position position) = output :=
      hnextCompletion.2.1 position output hprivate
    have hpending : (Coordinate.position position, candidate) ∈
        (context.state.addPending (.position position) candidate).pending := by
      simp [LazyRevealProbe.State.addPending]
    have havoids :=
      hnextCompletion.2.2.1 (.position position) candidate hpending
    rwa [hnextOutput] at havoids
  · intro havoids
    refine ⟨completion, hcompletion.addPending_of_avoids (.position position) candidate ?_⟩
    have hcompletionOutput : completion (.position position) = output :=
      hcompletion.2.1 position output hprivate
    rwa [hcompletionOutput]

theorem not_deferredCompletable_addPending_position_iff_privateStructuralHit
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (position : Position) (output : HashOutput) (candidate : Digest)
    (hcompletion : DeferredCompletion table context completion)
    (hhidden : context.state.values (.position position) = none)
    (hprivate : context.values position = some output) :
    ¬DeferredCompletable table
        { context with
          state := context.state.addPending (.position position) candidate } ↔
      PrivateStructuralHit
        { context with
          state := context.state.addPending (.position position) candidate } := by
  rw [deferredCompletable_addPending_position_iff position output candidate hcompletion hprivate,
    privateStructuralHit_addPending_iff context position output candidate
      hcompletion.not_privateStructuralHit hhidden hprivate]
  simp

theorem privateStructuralHit_addPending_of_truncateHash_eq
    (context : DeferredContext) (position : Position) (output : HashOutput)
    (candidate : Digest)
    (hhidden : context.state.values (.position position) = none)
    (hprivate : context.values position = some output)
    (hcandidate : truncateHash output = candidate) :
    PrivateStructuralHit
      { context with
        state := context.state.addPending (.position position) candidate } := by
  refine ⟨position, output, hhidden, hprivate, ?_⟩
  exact (hitAt_addPending_self_iff context.state (.position position) candidate output).2
    (Or.inr hcandidate)

end SphincsSecurity.Concrete.OtsProbeSimulation
