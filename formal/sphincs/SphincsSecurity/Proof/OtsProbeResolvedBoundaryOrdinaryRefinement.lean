import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveFinalization
import SphincsSecurity.Proof.OtsProbeResolvedPrivateSampling

/-!
# One-sided ordinary boundary refinement

The canonical side can spend a probe at an unpublished structural value which the materialized
side can already read. A miss preserves finalization semantics while consuming one unit of fuel;
a hit is exactly the private structural outcome and imposes no ordinary-failure obligation.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem FinalizationViewEq.addPending_left_of_resolved
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right)
    (coordinate : Coordinate) (candidate : Digest) (output : HashOutput)
    (hvalue : resolvedCompletionValue table left coordinate = some output)
    (hmiss : truncateHash output ≠ candidate) :
    FinalizationViewEq table
      { left with state := left.state.addPending coordinate candidate } right := by
  refine
    { leftConsistent := hview.leftConsistent.addPending coordinate candidate
      rightConsistent := hview.rightConsistent
      leftStarts := hview.leftStarts.addPending coordinate candidate
      rightStarts := hview.rightStarts
      valueEq := hview.valueEq
      leftClean := ?_
      rightClean := hview.rightClean
      pendingEq := ?_ }
  · intro other otherOutput hotherValue hhit
    by_cases heq : other = coordinate
    · subst other
      have houtput : otherOutput = output := by
        change resolvedCompletionValue table left coordinate = some otherOutput at hotherValue
        rw [hvalue] at hotherValue
        exact (Option.some.inj hotherValue).symm
      subst otherOutput
      rw [hitAt_addPending_self_iff] at hhit
      exact hhit.elim (hview.leftClean coordinate output hvalue) hmiss
    · have hhitBase : left.state.hitAt other otherOutput := by
        rw [hitAt_addPending_of_ne left.state coordinate other candidate otherOutput (Ne.symm heq)]
          at hhit
        exact hhit
      exact hview.leftClean other otherOutput hotherValue hhitBase
  · intro other hnone
    have hne : other ≠ coordinate := by
      intro heq
      subst other
      change resolvedCompletionValue table left coordinate = none at hnone
      rw [hvalue] at hnone
      contradiction
    calc
      (left.state.addPending coordinate candidate).pendingAt other =
          left.state.pendingAt other := by
        ext digest
        simp [LazyRevealProbe.State.pendingAt, LazyRevealProbe.State.addPending, hne]
      _ = right.state.pendingAt other := hview.pendingEq other hnone

theorem FinalizationContextEq.addPending_left_of_resolved
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextEq table (some left) (some right))
    (coordinate : Coordinate) (candidate : Digest) (output : HashOutput)
    (hvalue : resolvedCompletionValue table left coordinate = some output)
    (hmiss : truncateHash output ≠ candidate) :
    FinalizationContextEq table
      (some { left with state := left.state.addPending coordinate candidate })
      (some right) := by
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  obtain ⟨completion, hcompletion⟩ := hleftCompletable
  have hcompletionOutput : completion coordinate = output :=
    hcompletion.eq_resolvedCompletionValue coordinate output hvalue
  have hcompletion' : DeferredCompletion table
      { left with state := left.state.addPending coordinate candidate } completion :=
    hcompletion.addPending_of_avoids coordinate candidate (by
      rwa [hcompletionOutput])
  have hleftCompletable' : DeferredCompletable table
      { left with state := left.state.addPending coordinate candidate } :=
    ⟨completion, hcompletion'⟩
  exact
    ⟨hview.addPending_left_of_resolved coordinate candidate output hvalue hmiss,
      hleftValid.addPending_of_completable coordinate candidate hleftCompletable',
      hrightValid, hleftCompletable'⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
