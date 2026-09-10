import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedSampling

/-!
# Pending-candidate trace invariant

Probe-free resolved computations can only preserve or remove pending candidates. This is the support invariant needed to show that every private structural stop is witnessed by a candidate already present in the proof-only plan trace.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def PendingCoveredBy (candidates : List Probe) (context : DeferredContext) : Prop :=
  ∀ entry ∈ context.state.pending,
    ∃ candidate ∈ candidates,
      candidate.coordinate = entry.1 ∧ candidate.candidate = entry.2

theorem pendingCoveredBy_empty :
    PendingCoveredBy []
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues } := by
  intro entry hentry
  simp [LazyRevealProbe.State.empty] at hentry

theorem PendingCoveredBy.of_subset
    {candidates : List Probe} {left right : DeferredContext}
    (hcovered : PendingCoveredBy candidates right)
    (hsubset : left.state.pending ⊆ right.state.pending) :
    PendingCoveredBy candidates left := by
  intro entry hentry
  exact hcovered entry (hsubset hentry)

theorem PendingCoveredBy.mono_candidates
    {prior later : List Probe} {context : DeferredContext}
    (hcovered : PendingCoveredBy prior context) (hsublist : prior.Sublist later) :
    PendingCoveredBy later context := by
  intro entry hentry
  obtain ⟨candidate, hcandidate, hcoordinate, hdigest⟩ := hcovered entry hentry
  exact ⟨candidate, hsublist.subset hcandidate, hcoordinate, hdigest⟩

theorem PendingCoveredBy.addPending_append
    (candidates : List Probe) (context : DeferredContext) (candidate : Probe)
    (hcovered : PendingCoveredBy candidates context) :
    PendingCoveredBy (candidates ++ [candidate])
      { context with
        state := context.state.addPending candidate.coordinate candidate.candidate } := by
  intro entry hentry
  simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hentry
  rcases hentry with hnew | hold
  · subst entry
    exact ⟨candidate, by simp, rfl, rfl⟩
  · obtain ⟨oldCandidate, holdCandidate, hcoordinate, hdigest⟩ := hcovered entry hold
    exact ⟨oldCandidate, by simp [holdCandidate], hcoordinate, hdigest⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
