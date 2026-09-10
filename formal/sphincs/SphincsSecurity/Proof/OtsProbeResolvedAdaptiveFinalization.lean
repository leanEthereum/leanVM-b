import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedSchedule

/-!
# Finalization equivalence through adaptive execution

The chronological and delayed signers leave different coordinates materialized. This file tracks
their common clean completion semantics through the adaptive random-oracle handler, while treating
a context with no clean completion as terminally doomed.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem DeferredCompletion.addPending_of_avoids
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput} (coordinate : Coordinate)
    (candidate : Digest) (hcompletion : DeferredCompletion table context completion)
    (havoids : truncateHash (completion coordinate) ≠ candidate) :
    DeferredCompletion table
      { context with state := context.state.addPending coordinate candidate } completion := by
  refine ⟨hcompletion.1, hcompletion.2.1, ?_, hcompletion.2.2.2⟩
  intro other otherCandidate hmember
  simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hmember
  rcases hmember with hnew | hold
  · rcases hnew with ⟨rfl, rfl⟩
    exact havoids
  · exact hcompletion.2.2.1 other otherCandidate hold

theorem FinalizationViewEq.addPending_of_completable
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right) (coordinate : Coordinate)
    (candidate : Digest)
    (hleftCompletable : DeferredCompletable table
      { left with state := left.state.addPending coordinate candidate })
    (hrightCompletable : DeferredCompletable table
      { right with state := right.state.addPending coordinate candidate }) :
    FinalizationViewEq table
      { left with state := left.state.addPending coordinate candidate }
      { right with state := right.state.addPending coordinate candidate } := by
  refine ⟨hview.leftConsistent.addPending coordinate candidate,
    hview.rightConsistent.addPending coordinate candidate,
    hview.leftStarts.addPending coordinate candidate,
    hview.rightStarts.addPending coordinate candidate, hview.valueEq, ?_, ?_, ?_⟩
  · intro other output hvalue hhit
    obtain ⟨completion, hcompletion⟩ := hleftCompletable
    have houtput := hcompletion.eq_resolvedCompletionValue other output hvalue
    have havoids := hcompletion.2.2.1
    unfold LazyRevealProbe.State.hitAt at hhit
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
    exact havoids other (truncateHash output) hhit (by rw [houtput])
  · intro other output hvalue hhit
    obtain ⟨completion, hcompletion⟩ := hrightCompletable
    have houtput := hcompletion.eq_resolvedCompletionValue other output hvalue
    have havoids := hcompletion.2.2.1
    unfold LazyRevealProbe.State.hitAt at hhit
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
    exact havoids other (truncateHash output) hhit (by rw [houtput])
  · intro other hvalue
    have hvalueBase : resolvedCompletionValue table left other = none := hvalue
    ext digest
    rw [LazyRevealProbe.State.mem_pendingAt_iff,
      LazyRevealProbe.State.mem_pendingAt_iff]
    simp only [LazyRevealProbe.State.addPending, Finset.mem_insert]
    have hbase : (other, digest) ∈ left.state.pending ↔
        (other, digest) ∈ right.state.pending := by
      rw [← LazyRevealProbe.State.mem_pendingAt_iff,
        ← LazyRevealProbe.State.mem_pendingAt_iff,
        hview.pendingEq other hvalueBase]
    tauto

theorem deferredCompletable_addPending_iff_of_finalizationViewEq
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right) (coordinate : Coordinate)
    (candidate : Digest) :
    DeferredCompletable table
        { left with state := left.state.addPending coordinate candidate } ↔
      DeferredCompletable table
        { right with state := right.state.addPending coordinate candidate } := by
  constructor
  · rintro ⟨completion, hcompletion⟩
    have hleftBase := hcompletion.of_addPending coordinate candidate
    have hrightBase := (hview.deferredCompletion_iff completion).mp hleftBase
    have havoids := hcompletion.2.2.1 coordinate candidate (by
      simp [LazyRevealProbe.State.addPending])
    exact ⟨completion, hrightBase.addPending_of_avoids coordinate candidate havoids⟩
  · rintro ⟨completion, hcompletion⟩
    have hrightBase := hcompletion.of_addPending coordinate candidate
    have hleftBase := (hview.deferredCompletion_iff completion).mpr hrightBase
    have havoids := hcompletion.2.2.1 coordinate candidate (by
      simp [LazyRevealProbe.State.addPending])
    exact ⟨completion, hleftBase.addPending_of_avoids coordinate candidate havoids⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
