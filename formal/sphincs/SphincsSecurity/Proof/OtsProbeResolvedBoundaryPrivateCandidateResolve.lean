import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateCandidateGame

/-!
# Deferred resolution of a finite candidate list

This module realizes the abstract finite candidate game through the actual deferred structural resolver. It starts from a context fresh at every structural coordinate named by the list, samples each named coordinate only when its group is processed, and leaves unrelated coordinates untouched.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

def CandidateCoordinatesFresh (context : DeferredContext) (candidates : List Probe) : Prop :=
  context.state.pending = ∅ ∧
    ∀ candidate ∈ candidates,
      match candidate.coordinate with
      | .chainStart _ _ _ _ => True
      | .position position =>
          context.state.values (.position position) = none ∧
            context.values position = none

theorem candidateCoordinatesFresh_empty (candidates : List Probe) :
    CandidateCoordinatesFresh
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues }
      candidates := by
  constructor
  · rfl
  · intro candidate _hcandidate
    cases candidate.coordinate <;> simp [LazyRevealProbe.State.empty,
      emptyDeferredStructuralValues]

theorem not_hitAt_of_pending_eq_empty
    (context : DeferredContext) (coordinate : Coordinate) (output : HashOutput)
    (hpending : context.state.pending = ∅) :
    ¬context.state.hitAt coordinate output := by
  simp [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt, hpending]

noncomputable def resolvedCandidateGroupsFire : Nat → List Probe → DeferredContext → ProbComp Bool
  | 0, _, _ => pure false
  | _ + 1, [], _ => pure false
  | fuel + 1, candidate :: remaining, context =>
      match candidate.coordinate with
      | .chainStart _ _ _ _ => resolvedCandidateGroupsFire fuel remaining context
      | .position target => do
          let resolved ← resolveDeferredPositionValue target context
          match resolved with
          | none => pure true
          | some resolved =>
              if candidateListHits target (candidate :: remaining) resolved.output then
                pure true
              else
                resolvedCandidateGroupsFire fuel
                  (removeTargetCandidates target (candidate :: remaining))
                  resolved.toDeferredContext

theorem candidateCoordinatesFresh_remove_resolved
    (context : DeferredContext) (candidate : Probe) (remaining : List Probe)
    (target : Position) (output : HashOutput)
    (hfresh : CandidateCoordinatesFresh context (candidate :: remaining)) :
    CandidateCoordinatesFresh
      { state := context.state.clearPending (.position target)
        values := context.values.install target output }
      (removeTargetCandidates target (candidate :: remaining)) := by
  constructor
  · simp [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway, hfresh.1]
  · intro nextCandidate hnext
    have hnextOriginal : nextCandidate ∈ candidate :: remaining := by
      unfold removeTargetCandidates at hnext
      exact (List.mem_filter.mp hnext).1
    have hnotTarget : ¬candidateTargets target nextCandidate := by
      unfold removeTargetCandidates at hnext
      have := (List.mem_filter.mp hnext).2
      simpa using this
    have hnextFresh := hfresh.2 nextCandidate hnextOriginal
    cases hnextCoordinate : nextCandidate.coordinate with
    | chainStart lay tree leafIdx chainIdx => trivial
    | position other =>
        simp only [hnextCoordinate] at hnextFresh
        have hne : other ≠ target := by
          intro heq
          subst other
          apply hnotTarget
          simp [candidateTargets, hnextCoordinate]
        constructor
        · simpa [LazyRevealProbe.State.clearPending] using hnextFresh.1
        · simpa [DeferredStructuralValues.install, Function.update_of_ne hne] using
            hnextFresh.2

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem evalDist_resolvedCandidateGroupsFire_eq_planned
    (fuel : Nat) (candidates : List Probe) (context : DeferredContext)
    (hfresh : CandidateCoordinatesFresh context candidates) :
    evalDist (resolvedCandidateGroupsFire fuel candidates context) =
      evalDist (plannedCandidateGroupsFire fuel candidates) := by
  induction fuel generalizing candidates context with
  | zero => simp [resolvedCandidateGroupsFire, plannedCandidateGroupsFire]
  | succ fuel ih =>
      cases candidates with
      | nil => simp [resolvedCandidateGroupsFire, plannedCandidateGroupsFire]
      | cons candidate remaining =>
          cases hcoordinate : candidate.coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [resolvedCandidateGroupsFire, plannedCandidateGroupsFire, hcoordinate]
              exact ih remaining context ⟨hfresh.1, fun next hnext =>
                hfresh.2 next (List.mem_cons_of_mem candidate hnext)⟩
          | position target =>
              have htargetFresh := hfresh.2 candidate (by simp)
              simp only [hcoordinate] at htargetFresh
              have hnoHit : ∀ output,
                  ¬context.state.hitAt (.position target) output := fun output =>
                not_hitAt_of_pending_eq_empty context (.position target) output hfresh.1
              simp only [resolvedCandidateGroupsFire, plannedCandidateGroupsFire, hcoordinate]
              rw [resolveDeferredPositionValue_fresh target context htargetFresh.1
                htargetFresh.2]
              simp only [bind_assoc]
              apply evalDist_bind_congr
              intro output _houtput
              simp only [hnoHit output, ↓reduceIte, pure_bind]
              by_cases hfire : candidateListHits target (candidate :: remaining) output
              · simp [hfire]
              · simp only [hfire, ↓reduceIte]
                exact ih (removeTargetCandidates target (candidate :: remaining))
                  { state := context.state.clearPending (.position target)
                    values := context.values.install target output }
                  (candidateCoordinatesFresh_remove_resolved context candidate remaining target
                    output hfresh)

noncomputable def resolvedCandidateListFire
    (candidates : List Probe) (context : DeferredContext) : ProbComp Bool :=
  resolvedCandidateGroupsFire candidates.length candidates context

theorem evalDist_resolvedCandidateListFire_empty
    (candidates : List Probe) :
    evalDist (resolvedCandidateListFire candidates
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues }) =
      evalDist (plannedCandidateListFire candidates) := by
  exact evalDist_resolvedCandidateGroupsFire_eq_planned candidates.length candidates _
    (candidateCoordinatesFresh_empty candidates)

theorem probEvent_resolvedCandidateListFire_empty_le (candidates : List Probe) :
    Pr[= true | resolvedCandidateListFire candidates
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues }] ≤
      (candidates.length : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ = Pr[= true | plannedCandidateListFire candidates] :=
      OracleComp.probOutput_congr rfl
        (evalDist_resolvedCandidateListFire_empty candidates)
    _ ≤ _ := probEvent_plannedCandidateListFire_le candidates

end SphincsSecurity.Concrete.OtsProbeSimulation
