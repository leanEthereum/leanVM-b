import SphincsSecurity.Proof.JointProbeResolvedCompletionHistory
import SphincsSecurity.Proof.JointProbeOriginalRetainedFailure
import SphincsSecurity.Proof.OtsProbeNativeRootReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem step_computed
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Frame) (cache : QueryCache HashSpec) (hit : Bool)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context)
    (result) (hresult : result ∈ support (step exception parameter root otsTable ftsTable input (some frame) cache hit))
    (finalFrame : Frame) (hframe : result.1 = some finalFrame) :
    OtsProbeSimulation.DeferredComputationsClosed finalFrame.context := by
  have hs := (step_shared_support exception parameter root otsTable ftsTable input frame cache hit result hresult finalFrame hframe).1
  exact computed_of_mem_jointDetailed ftsTable _ frame.state finalFrame.state frame.ftsFuel frame.context frame.fuel otsTable _ hcomputed hs

theorem run_computed
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Frame) (cache : QueryCache HashSpec) (hit : Bool)
    (hvalid : frame.Valid parameter otsTable ftsTable cache)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash frame.ftsFuel)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context)
    (result) (hresult : result ∈ support (run exception parameter root otsTable ftsTable computation (some frame) cache hit))
    (finalFrame : Frame) (hframe : result.1 = some finalFrame) :
    OtsProbeSimulation.DeferredComputationsClosed finalFrame.context := by
  have hs := run_shared_support exception parameter root otsTable ftsTable computation frame cache hit hbound hvalid result hresult finalFrame hframe
  exact computed_of_mem_jointDetailed ftsTable _ frame.state finalFrame.state frame.ftsFuel frame.context frame.fuel otsTable _ hcomputed hs

theorem rootSupport_computed
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) (root : Digest) (frame : Frame)
    (hroot : RootSupport otsTable ftsTable q fuel root frame) :
    OtsProbeSimulation.DeferredComputationsClosed frame.context :=
  computed_of_mem_jointDetailed ftsTable _ AdaptiveRevealProbe.State.empty frame.state q
    (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable _ (OtsProbeSimulation.ensuredInitialContext_computed ∅) hroot.2

theorem initializeRoot_computed
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat)
    (result) (hresult : result ∈ support (initializeRoot parameter otsTable ftsTable q fuel))
    (frame : Frame) (hframe : result.1 = some frame) :
    OtsProbeSimulation.DeferredComputationsClosed frame.context :=
  rootSupport_computed otsTable ftsTable q fuel result.2.1 frame
    (initializeRoot_valid parameter otsTable ftsTable q fuel result hresult frame hframe).1

theorem runRetained_computed
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) (result) (hresult : result ∈ support (runRetained exception adversary parameter otsTable ftsTable q fuel))
    (finalFrame : Frame) (hframe : result.1 = some finalFrame) :
    OtsProbeSimulation.DeferredComputationsClosed finalFrame.context := by
  rw [runRetained, mem_support_bind_iff] at hresult
  obtain ⟨initial, hinitial, hrest⟩ := hresult
  cases hf : initial.1 with
  | none =>
      rw [hf, run_none, support_map] at hrest
      obtain ⟨actual, _, rfl⟩ := hrest
      contradiction
  | some frame =>
      have hv := initializeRoot_valid parameter otsTable ftsTable q fuel initial hinitial frame hf
      rw [hf] at hrest
      apply run_computed exception parameter initial.2.1 otsTable ftsTable _ frame initial.2.2 false hv.2 _
        (rootSupport_computed otsTable ftsTable q fuel initial.2.1 frame hv.1) result hrest finalFrame hframe
      rw [hv.1.1]
      exact retainedComputation_hashBound adversary parameter initial.2.1 q

theorem runRetainedWithFailure_computed
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) (result) (hresult : result ∈ support (runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel))
    (finalFrame : Frame) (hframe : result.1.1 = some finalFrame) :
    OtsProbeSimulation.DeferredComputationsClosed finalFrame.context :=
  runRetained_computed exception adversary parameter otsTable ftsTable q fuel result.1
    (runRetainedWithFailure_support_project exception adversary parameter otsTable ftsTable q fuel result hresult) finalFrame hframe

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
