import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePlanNormalizedCount

/-!
# Candidate preparation across canonicalization

Canonicalization moves unpublished materialized structural outputs into the private table without changing their resolution semantics. The finite guarded preparation observer is therefore invariant under a canonical boundary.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_prepareCandidateGroupsFails_canonicalize
    (table : OtsSecretIndex → HashOutput)
    (fuel : Nat) (candidates : List Probe) (context : DeferredContext)
    (hconsistent : context.ValuesConsistent)
    (hpublished : PublishedValues context.state) :
    evalDist (prepareCandidateGroupsFails fuel candidates
      (canonicalizeMaterializedValues table context)) =
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
              exact ih remaining context hconsistent hpublished
          | position target =>
              simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcandidate]
              let continuation : Option DeferredResolution → ProbComp Bool
                | none => pure true
                | some resolved =>
                    if candidateListHits target (candidate :: remaining) resolved.output then
                      pure true
                    else
                      prepareCandidateGroupsFails fuel
                        (removeTargetCandidates target (candidate :: remaining))
                        resolved.toDeferredContext
              have hresolution := evalDist_resolveDeferredPositionValue_canonicalize table target
                context hconsistent hpublished
              calc
                _ = evalDist (((Option.map (canonicalizeDeferredResolution table)) <$>
                      resolveDeferredPositionValue target context) >>= continuation) :=
                  evalDist_bind_eq_of_evalDist_eq hresolution.symm continuation
                _ = evalDist (resolveDeferredPositionValue target context >>= continuation) := by
                  simp only [map_eq_bind_pure_comp, bind_assoc]
                  apply evalDist_bind_congr
                  intro resolved hresolved
                  cases resolved with
                  | none => rfl
                  | some resolved =>
                      simp only [Function.comp_apply, pure_bind, Option.map_some,
                        canonicalizeDeferredResolution]
                      by_cases hhit : candidateListHits target (candidate :: remaining)
                          resolved.output
                      · simp [continuation, hhit]
                      · simp only [continuation, hhit, ↓reduceIte]
                        have hnextConsistent :=
                          hconsistent.of_resolveDeferredPositionValue target resolved hresolved
                        have hnextPublished : PublishedValues resolved.state :=
                          (publishedValues_resolveDeferredPositionValue_iff target context resolved
                            hresolved).2 hpublished
                        exact ih (removeTargetCandidates target (candidate :: remaining))
                          resolved.toDeferredContext hnextConsistent hnextPublished
                _ = _ := rfl

theorem evalDist_prepareCandidateListFails_canonicalize
    (table : OtsSecretIndex → HashOutput) (candidates : List Probe)
    (context : DeferredContext) (hconsistent : context.ValuesConsistent)
    (hpublished : PublishedValues context.state) :
    evalDist (prepareCandidateListFails candidates
      (canonicalizeMaterializedValues table context)) =
      evalDist (prepareCandidateListFails candidates context) :=
  evalDist_prepareCandidateGroupsFails_canonicalize table candidates.length candidates context
    hconsistent hpublished

theorem pendingCoveredBy_canonicalize_iff
    (table : OtsSecretIndex → HashOutput) (candidates : List Probe)
    (context : DeferredContext) :
    PendingCoveredBy candidates (canonicalizeMaterializedValues table context) ↔
      PendingCoveredBy candidates context := by
  rfl

theorem evalDist_guardedPreparationObserve_canonicalize
    (table : OtsSecretIndex → HashOutput) (candidates : List Probe)
    (context : DeferredContext) (hconsistent : context.ValuesConsistent)
    (hpublished : PublishedValues context.state) :
    evalDist (guardedPreparationObserve candidates
      (canonicalizeMaterializedValues table context)) =
      evalDist (guardedPreparationObserve candidates context) := by
  unfold guardedPreparationObserve
  rw [pendingCoveredBy_canonicalize_iff table candidates context]
  by_cases hcovered : PendingCoveredBy candidates context
  · simp only [hcovered, ↓reduceIte]
    exact evalDist_prepareCandidateListFails_canonicalize table candidates context hconsistent
      hpublished
  · simp [hcovered]

end SphincsSecurity.Concrete.OtsProbeSimulation
