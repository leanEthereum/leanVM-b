import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateFresh

/-!
# Planned-probe resolution commutation

Resolving a target before one planned candidate and resolving it again afterward is distributionally identical to executing the candidate first and resolving the target once.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open ENNReal

def addCandidateContext (context : DeferredContext) (candidate : Probe) : DeferredContext :=
  if candidate.coordinate ∈ context.state.revealed then context
  else { context with
    state := context.state.addPending candidate.coordinate candidate.candidate }

noncomputable def resolveAfterCandidate
    (target : Position) (candidate : Probe) (context : DeferredContext) :
    ProbComp (Option DeferredResolution) :=
  resolveDeferredPositionValue target (addCandidateContext context candidate)

theorem resolveDeferredPositionValue_then_resolve_self
    (position : Position) (context : DeferredContext) :
    evalDist (do
      let first ← resolveDeferredPositionValue position context
      match first with
      | none => pure none
      | some first => resolveDeferredPositionValue position first.toDeferredContext) =
      evalDist (resolveDeferredPositionValue position context) := by
  calc
    _ = evalDist (resolveDeferredPositionValue position context >>= pure) := by
      apply evalDist_bind_congr
      intro first hfirst
      cases first with
      | none => rfl
      | some first =>
          exact congrArg evalDist
            (resolveDeferredPositionValue_of_resolved position context first hfirst)
    _ = _ := by rw [bind_pure]

set_option maxRecDepth 100000 in
theorem resolveDeferredPositionValue_then_resolveAfterCandidate
    (target : Position) (candidate : Probe) (context : DeferredContext) :
    evalDist (do
      let first ← resolveDeferredPositionValue target context
      match first with
      | none => pure none
      | some first => resolveAfterCandidate target candidate first.toDeferredContext) =
      evalDist (resolveAfterCandidate target candidate context) := by
  unfold resolveAfterCandidate addCandidateContext
  by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
  · have hresolvedRevealed : ∀ first,
        some first ∈ support (resolveDeferredPositionValue target context) →
        candidate.coordinate ∈ first.state.revealed := by
      intro first hfirst
      rw [resolveDeferredPositionValue_state_eq_clearPending target context first hfirst]
      exact hrevealed
    simp only [hrevealed, ↓reduceIte]
    calc
      _ = evalDist (resolveDeferredPositionValue target context >>= pure) := by
        apply evalDist_bind_congr
        intro first hfirst
        cases first with
        | none => rfl
        | some first =>
            simp only [hresolvedRevealed first hfirst, ↓reduceIte]
            exact congrArg evalDist
              (resolveDeferredPositionValue_of_resolved target context first hfirst)
      _ = _ := by rw [bind_pure]
  · have hresolvedNotRevealed : ∀ first,
        some first ∈ support (resolveDeferredPositionValue target context) →
        candidate.coordinate ∉ first.state.revealed := by
      intro first hfirst hfirstRevealed
      apply hrevealed
      rw [resolveDeferredPositionValue_state_eq_clearPending target context first hfirst]
        at hfirstRevealed
      exact hfirstRevealed
    simp only [hrevealed, ↓reduceIte]
    cases candidate with
    | mk coordinate digest =>
        by_cases heq : coordinate = .position target
        · subst coordinate
          calc
            _ = evalDist (do
                let first ← resolveDeferredPositionValue target context
                match first with
                | none => pure none
                | some first =>
                    resolveDeferredPositionValue target
                      { first.toDeferredContext with
                        state := first.state.addPending (.position target) digest }) := by
                  apply evalDist_bind_congr
                  intro first hfirst
                  cases first with
                  | none => rfl
                  | some first =>
                      simp [hresolvedNotRevealed first hfirst]
            _ = _ := congrArg evalDist
              (resolveDeferredPositionValue_then_addPending_self_resolve target context digest)
        · rw [resolveDeferredPositionValue_addPending_of_ne target context coordinate digest heq]
          simp only [map_eq_bind_pure_comp]
          apply evalDist_bind_congr
          intro first hfirst
          cases first with
          | none => rfl
          | some first =>
              simp only [hresolvedNotRevealed first hfirst, ↓reduceIte]
              rw [resolveDeferredPositionValue_addPending_of_ne target
                first.toDeferredContext coordinate digest heq]
              rw [map_eq_bind_pure_comp,
                resolveDeferredPositionValue_of_resolved target context first hfirst]
              simp [DeferredResolution.addPending]

def candidateListHits (target : Position) : List Probe → HashOutput → Prop
  | [], _ => False
  | candidate :: remaining, output =>
      (candidate.coordinate = .position target ∧
        truncateHash output = candidate.candidate) ∨
      candidateListHits target remaining output

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampleHashOutput_candidateListHits_le
    (target : Position) (candidates : List Probe) :
    Pr[candidateListHits target candidates | LazyRevealProbe.sampleHashOutput] ≤
      (candidates.length : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction candidates with
  | nil => simp [candidateListHits]
  | cons candidate remaining ih =>
      let epsilon := ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
      have hhead : Pr[fun output : HashOutput =>
          candidate.coordinate = .position target ∧
            truncateHash output = candidate.candidate |
          LazyRevealProbe.sampleHashOutput] ≤ epsilon := by
        by_cases hcoordinate : candidate.coordinate = .position target
        · apply le_of_eq
          calc
            _ = Pr[fun output : HashOutput =>
                truncateHash output = candidate.candidate |
                  LazyRevealProbe.sampleHashOutput] := by
                apply OracleComp.probEvent_congr' (fun _ _ => by simp [hcoordinate]) rfl
            _ = (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
              unfold LazyRevealProbe.sampleHashOutput
              exact SphincsSecurity.probEvent_uniform_truncateHash_eq _
            _ = epsilon := by
              rw [show Fintype.card Digest = 2 ^ digestBits by simp]
        · simp [hcoordinate]
      calc
        _ ≤ Pr[fun output : HashOutput =>
              candidate.coordinate = .position target ∧
                truncateHash output = candidate.candidate |
              LazyRevealProbe.sampleHashOutput] +
            Pr[candidateListHits target remaining |
              LazyRevealProbe.sampleHashOutput] :=
          probEvent_or_le LazyRevealProbe.sampleHashOutput _ _
        _ ≤ epsilon + (remaining.length : ℝ≥0∞) * epsilon :=
          add_le_add hhead ih
        _ = ((candidate :: remaining).length : ℝ≥0∞) * epsilon := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

noncomputable def resolveCandidateListFire
    (target : Position) (candidates : List Probe) (context : DeferredContext) :
    ProbComp Bool := by
  classical
  exact do
    let resolved ← resolveDeferredPositionValue target context
    match resolved with
    | none => pure false
    | some resolved => pure (decide (candidateListHits target candidates resolved.output))

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem probEvent_resolveCandidateListFire_le
    (target : Position) (candidates : List Probe) (context : DeferredContext)
    (hhidden : context.state.values (.position target) = none)
    (hprivate : context.values target = none) :
    Pr[= true | resolveCandidateListFire target candidates context] ≤
      (candidates.length : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  have hrun : resolveCandidateListFire target candidates context = (do
      let output ← LazyRevealProbe.sampleHashOutput
      if context.state.hitAt (.position target) output then pure false
      else pure (decide (candidateListHits target candidates output))) := by
    unfold resolveCandidateListFire
    rw [resolveDeferredPositionValue_fresh target context hhidden hprivate]
    simp only [bind_assoc]
    apply bind_congr
    intro output
    by_cases hhit : context.state.hitAt (.position target) output <;> simp [hhit]
  rw [hrun, ← probEvent_eq_eq_probOutput]
  refine (probEvent_bind_le_probEvent_add
    (mx := LazyRevealProbe.sampleHashOutput)
    (my := fun output =>
      if context.state.hitAt (.position target) output then pure false
      else pure (decide (candidateListHits target candidates output)))
    (q := fun hit : Bool => hit = true)
    (p := candidateListHits target candidates)
    (ε := 0) ?_).trans ?_
  · intro output _houtput hmiss
    by_cases hhit : context.state.hitAt (.position target) output
    · simp [hhit]
    · simp [hhit, hmiss]
  · simpa only [add_zero] using
      probEvent_sampleHashOutput_candidateListHits_le target candidates

end SphincsSecurity.Concrete.OtsProbeSimulation
