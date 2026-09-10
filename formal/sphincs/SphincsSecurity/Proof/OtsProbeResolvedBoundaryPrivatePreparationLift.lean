import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateTraceInvariant

/-!
# Administrative preparation lift

The guarded finite preparation observer is insensitive to administrative changes of the ensured and published sets. These are the nonprobabilistic interpreter cases surrounding structural resolution.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable

theorem PendingCoveredBy.addPending_of_mem
    {candidates : List Probe} {context : DeferredContext} (added : Probe)
    (hcovered : PendingCoveredBy candidates context) (hmem : added ∈ candidates) :
    PendingCoveredBy candidates
      { context with
        state := context.state.addPending added.coordinate added.candidate } := by
  intro entry hentry
  simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hentry
  rcases hentry with rfl | hentry
  · exact ⟨added, hmem, rfl, rfl⟩
  · exact hcovered entry hentry

@[simp] theorem hitAt_setStateValue
    (state : LazyRevealProbe.State Coordinate) (updated coordinate : Coordinate)
    (updatedOutput output : HashOutput) :
    ({ state with values := Function.update state.values updated (some updatedOutput) }).hitAt
        coordinate output = state.hitAt coordinate output := rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
