import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootCandidateNormalization
import SphincsSecurity.Proof.OuterQueryCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeRootCutCandidate (parameter : PublicParameter) (target : Position)
    (context : DeferredContext) (cut : OuterQueryCut α) : Option Digest := do
  let input ← cut.input?
  match input with
  | .inl (.inr input) =>
      let candidate ← nativeRootCandidate? parameter input context
      if candidate.coordinate = .position target then some candidate.candidate else none
  | _ => none

theorem nativeRootCutCandidate_replaceNativePosition
    (parameter : PublicParameter) (target : Position) (output : HashOutput) (context : DeferredContext) (cut : OuterQueryCut α) :
    nativeRootCutCandidate parameter target context cut =
      nativeRootCutCandidate parameter target (replaceNativePosition target output context) cut := by
  unfold nativeRootCutCandidate
  apply congrArg (fun next => cut.input?.bind next)
  funext input
  cases input with
  | inl query =>
      cases query with
      | inl n => rfl
      | inr input =>
          simp only
          rw [nativeRootCandidate_replaceNativePosition parameter target output context input]
  | inr message => rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
