import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePreparationCommute

/-!
# Administrative preparation lift

The guarded finite preparation observer is insensitive to administrative changes of the ensured and published sets. These are the nonprobabilistic interpreter cases surrounding structural resolution.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable

set_option maxRecDepth 100000 in
theorem evalDist_prepareCandidateGroupsFails_ensure
    (fuel : Nat) (candidates : List Probe) (context : DeferredContext)
    (coordinate : Coordinate) :
    evalDist (prepareCandidateGroupsFails fuel candidates
      { context with state := context.state.ensure coordinate }) =
      evalDist (prepareCandidateGroupsFails fuel candidates context) := by
  induction fuel generalizing candidates context with
  | zero => simp [prepareCandidateGroupsFails, resolvedCandidateGroupsFire]
  | succ fuel ih =>
      cases candidates with
      | nil => simp [prepareCandidateGroupsFails, resolvedCandidateGroupsFire]
      | cons candidate remaining =>
          cases hcandidate : candidate.coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcandidate]
              exact ih remaining context
          | position target =>
              simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcandidate]
              rw [resolveDeferredPositionValue_ensure]
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply evalDist_bind_congr
              intro resolved _hresolved
              cases resolved with
              | none => rfl
              | some resolved =>
                  simp only [Function.comp_apply, pure_bind, Option.map_some,
                    DeferredResolution.ensure]
                  by_cases hhit : candidateListHits target (candidate :: remaining)
                      resolved.output
                  · simp [hhit]
                  · simp only [hhit, ↓reduceIte]
                    exact ih (removeTargetCandidates target (candidate :: remaining))
                      resolved.toDeferredContext

set_option maxRecDepth 100000 in
theorem evalDist_prepareCandidateGroupsFails_publish
    (fuel : Nat) (candidates : List Probe) (context : DeferredContext)
    (coordinate : Coordinate) :
    evalDist (prepareCandidateGroupsFails fuel candidates
      { context with state := context.state.publish coordinate }) =
      evalDist (prepareCandidateGroupsFails fuel candidates context) := by
  induction fuel generalizing candidates context with
  | zero => simp [prepareCandidateGroupsFails, resolvedCandidateGroupsFire]
  | succ fuel ih =>
      cases candidates with
      | nil => simp [prepareCandidateGroupsFails, resolvedCandidateGroupsFire]
      | cons candidate remaining =>
          cases hcandidate : candidate.coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcandidate]
              exact ih remaining context
          | position target =>
              simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcandidate]
              rw [resolveDeferredPositionValue_publish]
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply evalDist_bind_congr
              intro resolved _hresolved
              cases resolved with
              | none => rfl
              | some resolved =>
                  simp only [Function.comp_apply, pure_bind, Option.map_some,
                    DeferredResolution.publish]
                  by_cases hhit : candidateListHits target (candidate :: remaining)
                      resolved.output
                  · simp [hhit]
                  · simp only [hhit, ↓reduceIte]
                    exact ih (removeTargetCandidates target (candidate :: remaining))
                      resolved.toDeferredContext

theorem pendingCoveredBy_ensure
    (candidates : List Probe) (context : DeferredContext) (coordinate : Coordinate) :
    PendingCoveredBy candidates
        { context with state := context.state.ensure coordinate } ↔
      PendingCoveredBy candidates context := by
  rfl

theorem pendingCoveredBy_publish
    (candidates : List Probe) (context : DeferredContext) (coordinate : Coordinate) :
    PendingCoveredBy candidates
        { context with state := context.state.publish coordinate } ↔
      PendingCoveredBy candidates context := by
  rfl

theorem evalDist_guardedPreparationObserve_ensure
    (candidates : List Probe) (context : DeferredContext) (coordinate : Coordinate) :
    evalDist (guardedPreparationObserve candidates
      { context with state := context.state.ensure coordinate }) =
      evalDist (guardedPreparationObserve candidates context) := by
  unfold guardedPreparationObserve
  rw [pendingCoveredBy_ensure]
  by_cases hcovered : PendingCoveredBy candidates context
  · simp only [hcovered, ↓reduceIte]
    exact evalDist_prepareCandidateGroupsFails_ensure candidates.length candidates context
      coordinate
  · simp [hcovered]

theorem evalDist_guardedPreparationObserve_publish
    (candidates : List Probe) (context : DeferredContext) (coordinate : Coordinate) :
    evalDist (guardedPreparationObserve candidates
      { context with state := context.state.publish coordinate }) =
      evalDist (guardedPreparationObserve candidates context) := by
  unfold guardedPreparationObserve
  rw [pendingCoveredBy_publish]
  by_cases hcovered : PendingCoveredBy candidates context
  · simp only [hcovered, ↓reduceIte]
    exact evalDist_prepareCandidateGroupsFails_publish candidates.length candidates context
      coordinate
  · simp [hcovered]

end SphincsSecurity.Concrete.OtsProbeSimulation
