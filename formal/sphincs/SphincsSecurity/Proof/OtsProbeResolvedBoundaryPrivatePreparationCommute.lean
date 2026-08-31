import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePreparation

/-!
# Candidate preparation commutation

A structural position named by a fixed candidate list may be resolved before the all-miss preparation or at its grouped position in the list. The preparation-failure distribution is unchanged.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable

def TargetOccurs (target : Position) (candidates : List Probe) : Prop :=
  ∃ candidate ∈ candidates, candidate.coordinate = .position target

theorem targetOccurs_removeTarget_of_ne
    (target other : Position) (candidates : List Probe) (hne : target ≠ other)
    (hoccurs : TargetOccurs target candidates) :
    TargetOccurs target (removeTargetCandidates other candidates) := by
  obtain ⟨candidate, hcandidate, hcoordinate⟩ := hoccurs
  refine ⟨candidate, ?_, hcoordinate⟩
  unfold removeTargetCandidates
  apply List.mem_filter.mpr
  refine ⟨hcandidate, ?_⟩
  simp [candidateTargets, hcoordinate, hne]

noncomputable def prepareCandidateGroupsFails
    (fuel : Nat) (candidates : List Probe) (context : DeferredContext) : ProbComp Bool :=
  resolvedCandidateGroupsFire fuel candidates context

noncomputable def continuePreparationAfterRevealed
    (fuel : Nat) (target : Position) (candidates : List Probe) :
    Option RevealedResolution → ProbComp Bool
  | none => pure true
  | some resolved =>
      if candidateListHits target candidates resolved.output then
        pure true
      else
        prepareCandidateGroupsFails fuel (removeTargetCandidates target candidates)
          resolved.context

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_resolve_then_prepareCandidateGroupsFails
    (position : Position) (fuel : Nat) (candidates : List Probe)
    (context : DeferredContext) (hlength : candidates.length ≤ fuel)
    (hoccurs : TargetOccurs position candidates) :
    evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
      match resolved with
      | none => pure true
      | some resolved =>
          prepareCandidateGroupsFails fuel candidates resolved.toDeferredContext) =
      evalDist (prepareCandidateGroupsFails fuel candidates context) := by
  induction fuel generalizing candidates context with
  | zero =>
      have hcandidates : candidates = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst candidates
      simp [TargetOccurs] at hoccurs
  | succ fuel ih =>
      cases candidates with
      | nil => simp [TargetOccurs] at hoccurs
      | cons candidate remaining =>
          cases hcoordinate : candidate.coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcoordinate]
              exact ih remaining context (by simpa using hlength) (by
                obtain ⟨found, hfound, hfoundCoordinate⟩ := hoccurs
                simp only [List.mem_cons] at hfound
                rcases hfound with rfl | hfound
                · simp [hcoordinate] at hfoundCoordinate
                · exact ⟨found, hfound, hfoundCoordinate⟩)
          | position target =>
              by_cases heq : position = target
              · subst position
                simp only [prepareCandidateGroupsFails, resolvedCandidateGroupsFire, hcoordinate,
                  ]
                apply evalDist_bind_congr
                intro first hfirst
                cases first with
                | none => rfl
                | some first =>
                    change evalDist (resolveDeferredPositionValue target
                        first.toDeferredContext >>= fun second =>
                          match second with
                          | none => pure true
                          | some second =>
                              if candidateListHits target (candidate :: remaining)
                                  second.output then
                                pure true
                              else
                                prepareCandidateGroupsFails fuel
                                  (removeTargetCandidates target (candidate :: remaining))
                                  second.toDeferredContext) =
                      evalDist (if candidateListHits target (candidate :: remaining)
                          first.output then
                        pure true
                      else
                        prepareCandidateGroupsFails fuel
                          (removeTargetCandidates target (candidate :: remaining))
                          first.toDeferredContext)
                    rw [resolveDeferredPositionValue_of_resolved target context first hfirst]
                    rfl
              · let rest := removeTargetCandidates target (candidate :: remaining)
                have hrestOccurs : TargetOccurs position rest :=
                  targetOccurs_removeTarget_of_ne position target (candidate :: remaining) heq
                    hoccurs
                have hcommute := evalDist_resolvePositionValues_comm_of_ne position target
                  context heq
                let continuation := continuePreparationAfterRevealed fuel target
                  (candidate :: remaining)
                calc
                  _ = evalDist (resolvePositionValuesInOrder position target context >>=
                        continuation) := by
                    unfold resolvePositionValuesInOrder continuation
                      continuePreparationAfterRevealed prepareCandidateGroupsFails
                    simp only [resolvedCandidateGroupsFire, hcoordinate, bind_assoc]
                    apply evalDist_bind_congr
                    intro first _hfirst
                    cases first with
                    | none => rfl
                    | some first =>
                        simp only
                        rw [bind_assoc]
                        apply evalDist_bind_congr
                        intro second _hsecond
                        cases second <;> rfl
                  _ = evalDist (resolvePositionValuesSwapped position target context >>=
                        continuation) :=
                    evalDist_bind_eq_of_evalDist_eq hcommute continuation
                  _ = evalDist (prepareCandidateGroupsFails (fuel + 1)
                        (candidate :: remaining) context) := by
                    unfold resolvePositionValuesSwapped continuation
                      continuePreparationAfterRevealed prepareCandidateGroupsFails
                    simp only [resolvedCandidateGroupsFire, hcoordinate, bind_assoc]
                    apply evalDist_bind_congr
                    intro targetResolved htargetResolved
                    cases targetResolved with
                    | none => rfl
                    | some targetResolved =>
                        simp only
                        rw [bind_assoc]
                        by_cases hhit : candidateListHits target (candidate :: remaining)
                            targetResolved.output
                        · simp only [hhit, ↓reduceIte]
                          calc
                            _ = evalDist (resolveDeferredPositionValue position
                                  targetResolved.toDeferredContext >>= fun _ => pure true) := by
                              apply evalDist_bind_congr
                              intro first _hfirst
                              cases first <;> simp [hhit]
                            _ = evalDist (pure true : ProbComp Bool) :=
                              OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                                (resolveDeferredPositionValue position
                                  targetResolved.toDeferredContext)
                                (by simp [resolveDeferredPositionValue,
                                  LazyRevealProbe.sampleHashOutput]) (pure true)
                        · simp only [hhit, ↓reduceIte]
                          have hrestLength : rest.length ≤ fuel := by
                            have hheadTarget : candidateTargets target candidate = true := by
                              simp [candidateTargets, hcoordinate]
                            have hcountPositive : 1 ≤ candidateTargetCount target
                                (candidate :: remaining) := by
                              simp [candidateTargetCount, hheadTarget]
                            have hpartition :=
                              candidateTargetCount_add_removeTargetCandidates_length target
                                (candidate :: remaining)
                            dsimp only [rest]
                            omega
                          calc
                            _ = evalDist (resolveDeferredPositionValue position
                                  targetResolved.toDeferredContext >>= fun resolved =>
                                    match resolved with
                                    | none => pure true
                                    | some resolved =>
                                        prepareCandidateGroupsFails fuel rest
                                          resolved.toDeferredContext) := by
                              apply evalDist_bind_congr
                              intro first _hfirst
                              cases first <;> simp [hhit, prepareCandidateGroupsFails, rest]
                            _ = _ := ih rest targetResolved.toDeferredContext hrestLength
                              hrestOccurs

noncomputable def prepareCandidateListFails
    (candidates : List Probe) (context : DeferredContext) : ProbComp Bool :=
  resolvedCandidateListFire candidates context

theorem evalDist_resolve_then_prepareCandidateListFails
    (position : Position) (candidates : List Probe) (context : DeferredContext)
    (hoccurs : TargetOccurs position candidates) :
    evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
      match resolved with
      | none => pure true
      | some resolved => prepareCandidateListFails candidates resolved.toDeferredContext) =
      evalDist (prepareCandidateListFails candidates context) := by
  exact evalDist_resolve_then_prepareCandidateGroupsFails position candidates.length candidates
    context le_rfl hoccurs

end SphincsSecurity.Concrete.OtsProbeSimulation
