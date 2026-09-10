import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePlannedCharge
import SphincsSecurity.Proof.OtsProbePrivateValueFirstAccess
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionMaterialize

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def PrivateTargetState (target : Position) (output : HashOutput) (pending : Finset Digest)
    (context : DeferredContext) : Prop :=
  context.state.values (.position target) = none ∧ context.values target = some output ∧
    .position target ∉ context.state.revealed ∧ context.state.pendingAt (.position target) = pending

theorem PrivateTargetState.probe_other
    {target : Position} {output : HashOutput} {pending : Finset Digest} {context : DeferredContext}
    (h : PrivateTargetState target output pending context) (coordinate : Coordinate) (digest : Digest)
    (hne : coordinate ≠ .position target) :
    PrivateTargetState target output pending { context with state := context.state.addPending coordinate digest } := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  rw [← h.2.2.2]
  ext candidate
  simp [LazyRevealProbe.State.mem_pendingAt_iff, LazyRevealProbe.State.addPending, Ne.symm hne]

theorem PrivateTargetState.publish_other
    {target : Position} {output : HashOutput} {pending : Finset Digest} {context : DeferredContext}
    (h : PrivateTargetState target output pending context) (coordinate : Coordinate) (hne : coordinate ≠ .position target) :
    PrivateTargetState target output pending { context with state := context.state.publish coordinate } := by
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  simpa [LazyRevealProbe.State.publish, Ne.symm hne] using h.2.2.1

theorem PrivateTargetState.materialize_other
    {target : Position} {output : HashOutput} {pending : Finset Digest} {context : DeferredContext}
    (h : PrivateTargetState target output pending context) (coordinate : Coordinate) (value : HashOutput)
    (values : DeferredStructuralValues) (hne : coordinate ≠ .position target) (hvalue : values target = some output) :
    PrivateTargetState target output pending { state := context.state.materialize coordinate value, values := values } := by
  refine ⟨?_, hvalue, h.2.2.1, ?_⟩
  · simpa [LazyRevealProbe.State.materialize, Function.update_of_ne (Ne.symm hne)] using h.1
  · rw [← h.2.2.2]
    ext candidate
    simp [LazyRevealProbe.State.mem_pendingAt_iff, LazyRevealProbe.State.materialize,
      LazyRevealProbe.State.pendingAway, Ne.symm hne]

theorem PrivateTargetState.materializedCandidateCharge_eq
    {target : Position} {output : HashOutput} {pending : Finset Digest} {context : DeferredContext}
    (h : PrivateTargetState target output pending context) (digest : Digest) :
    materializedCandidateCharge (materializedDeferredState context) (some ⟨.position target, digest⟩) =
      if digest ∈ pending then 0 else 1 := by
  have hpending : (.position target, digest) ∈ context.state.pending ↔ digest ∈ pending := by
    rw [← LazyRevealProbe.State.mem_pendingAt_iff, h.2.2.2]
  simp [materializedCandidateCharge, h.2.2.1, hpending, DeferredContext.positionValue, h.1, h.2.1]

noncomputable def privatePositionCutCharge (target : Position) :
    Option (ResolvedRunResult (PrivateValueCut α)) → ENNReal
  | none => 0
  | some result =>
      match privatePositionAccessCandidate target (some result.value) with
      | none => 0
      | some digest => materializedCandidateCharge (materializedDeferredState result.context) (some ⟨.position target, digest⟩)

end SphincsSecurity.Concrete.OtsProbeSimulation
