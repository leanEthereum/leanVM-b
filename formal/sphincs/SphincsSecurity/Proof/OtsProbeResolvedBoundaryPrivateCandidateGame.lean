import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateCount

/-!
# Finite planned-candidate game

The abstract all-miss endpoint samples only structural coordinates named by the recorded candidate list. Repeated candidates at one coordinate share one hidden output, and the total first-fire probability is charged by the list length rather than by a structural-position universe.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

def candidateTargets (target : Position) (candidate : Probe) : Bool :=
  decide (candidate.coordinate = .position target)

def candidateTargetCount (target : Position) (candidates : List Probe) : Nat :=
  candidates.countP (candidateTargets target)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem probEvent_sampleHashOutput_candidateListHits_le_count
    (target : Position) (candidates : List Probe) :
    Pr[candidateListHits target candidates | LazyRevealProbe.sampleHashOutput] ≤
      (candidateTargetCount target candidates : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction candidates with
  | nil => simp [candidateListHits, candidateTargetCount]
  | cons candidate remaining ih =>
      let epsilon := ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
      by_cases hcoordinate : candidate.coordinate = .position target
      · have hhead : Pr[fun output : HashOutput =>
            truncateHash output = candidate.candidate |
            LazyRevealProbe.sampleHashOutput] = epsilon := by
          calc
            _ = (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
              unfold LazyRevealProbe.sampleHashOutput
              exact SphincsSecurity.probEvent_uniform_truncateHash_eq _
            _ = epsilon := by
              rw [show Fintype.card Digest = 2 ^ digestBits by simp]
        have hevent : candidateListHits target (candidate :: remaining) =
            fun output => truncateHash output = candidate.candidate ∨
              candidateListHits target remaining output := by
          funext output
          simp [candidateListHits, hcoordinate]
        calc
          _ = Pr[fun output : HashOutput =>
                truncateHash output = candidate.candidate ∨
                  candidateListHits target remaining output |
                LazyRevealProbe.sampleHashOutput] := by rw [hevent]
          _ ≤ Pr[fun output : HashOutput =>
                truncateHash output = candidate.candidate |
                LazyRevealProbe.sampleHashOutput] +
              Pr[candidateListHits target remaining |
                LazyRevealProbe.sampleHashOutput] :=
            probEvent_or_le LazyRevealProbe.sampleHashOutput _ _
          _ ≤ epsilon +
              (candidateTargetCount target remaining : ℝ≥0∞) * epsilon :=
            add_le_add hhead.le ih
          _ = (candidateTargetCount target (candidate :: remaining) : ℝ≥0∞) *
              epsilon := by
            simp [candidateTargetCount, candidateTargets, hcoordinate]
            ring
      · have hevent : candidateListHits target (candidate :: remaining) =
            candidateListHits target remaining := by
          funext output
          simp [candidateListHits, hcoordinate]
        rw [hevent]
        simpa [candidateTargetCount, candidateTargets, hcoordinate] using ih

def removeTargetCandidates (target : Position) (candidates : List Probe) : List Probe :=
  candidates.filter fun candidate => !candidateTargets target candidate

theorem candidateTargetCount_add_removeTargetCandidates_length
    (target : Position) (candidates : List Probe) :
    candidateTargetCount target candidates +
        (removeTargetCandidates target candidates).length = candidates.length := by
  rw [candidateTargetCount, removeTargetCandidates, List.countP_eq_length_filter]
  exact (List.length_eq_length_filter_add
    (l := candidates) (candidateTargets target)).symm

noncomputable def plannedCandidateGroupsFire : Nat → List Probe → ProbComp Bool
  | 0, _ => pure false
  | _ + 1, [] => pure false
  | fuel + 1, candidate :: remaining =>
      match candidate.coordinate with
      | .chainStart _ _ _ _ => plannedCandidateGroupsFire fuel remaining
      | .position target => do
          let output ← LazyRevealProbe.sampleHashOutput
          if candidateListHits target (candidate :: remaining) output then
            pure true
          else
            plannedCandidateGroupsFire fuel
              (removeTargetCandidates target (candidate :: remaining))

noncomputable def plannedCandidateListFire (candidates : List Probe) : ProbComp Bool :=
  plannedCandidateGroupsFire candidates.length candidates

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem probEvent_plannedCandidateGroupsFire_le
    (fuel : Nat) (candidates : List Probe) (hlength : candidates.length ≤ fuel) :
    Pr[= true | plannedCandidateGroupsFire fuel candidates] ≤
      (candidates.length : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  let epsilon := ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
  induction fuel generalizing candidates with
  | zero =>
      have hcandidates : candidates = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst candidates
      simp [plannedCandidateGroupsFire]
  | succ fuel ih =>
      cases candidates with
      | nil => simp [plannedCandidateGroupsFire]
      | cons candidate remaining =>
          cases hcoordinate : candidate.coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [plannedCandidateGroupsFire, hcoordinate]
              exact (ih remaining (by simpa using hlength)).trans (by
                gcongr
                simp)
          | position target =>
              let rest := removeTargetCandidates target (candidate :: remaining)
              have hheadTarget : candidateTargets target candidate = true := by
                simp [candidateTargets, hcoordinate]
              have hcountPositive :
                  1 ≤ candidateTargetCount target (candidate :: remaining) := by
                simp [candidateTargetCount, hheadTarget]
              have hrestLength : rest.length ≤ fuel := by
                have hpartition :=
                  candidateTargetCount_add_removeTargetCandidates_length target
                    (candidate :: remaining)
                dsimp only [rest]
                omega
              have hrest := ih rest hrestLength
              have hstep : Pr[= true |
                    LazyRevealProbe.sampleHashOutput >>= fun output =>
                      if candidateListHits target (candidate :: remaining) output then
                        pure true
                      else plannedCandidateGroupsFire fuel rest] ≤
                  (candidateTargetCount target (candidate :: remaining) : ℝ≥0∞) * epsilon +
                    (rest.length : ℝ≥0∞) * epsilon := by
                rw [← probEvent_eq_eq_probOutput]
                rw [← probEvent_eq_eq_probOutput] at hrest
                have hbind := probEvent_bind_le_probEvent_add
                  (mx := LazyRevealProbe.sampleHashOutput)
                  (my := fun output =>
                    if candidateListHits target (candidate :: remaining) output then
                      pure true
                    else plannedCandidateGroupsFire fuel rest)
                  (q := fun hit : Bool => hit = true)
                  (p := candidateListHits target (candidate :: remaining))
                  (ε := (rest.length : ℝ≥0∞) * epsilon) (by
                    intro output _houtput hmiss
                    simp only [hmiss, ↓reduceIte]
                    simpa only [epsilon] using hrest)
                calc
                  _ ≤ Pr[candidateListHits target (candidate :: remaining) |
                        LazyRevealProbe.sampleHashOutput] +
                      (rest.length : ℝ≥0∞) * epsilon := hbind
                  _ ≤ (candidateTargetCount target (candidate :: remaining) : ℝ≥0∞) *
                        epsilon + (rest.length : ℝ≥0∞) * epsilon :=
                    add_le_add
                      (probEvent_sampleHashOutput_candidateListHits_le_count target
                        (candidate :: remaining)) le_rfl
              rw [plannedCandidateGroupsFire, hcoordinate]
              change Pr[= true |
                  LazyRevealProbe.sampleHashOutput >>= fun output =>
                    if candidateListHits target (candidate :: remaining) output then
                      pure true
                    else plannedCandidateGroupsFire fuel rest] ≤ _
              calc
                _ ≤ (candidateTargetCount target (candidate :: remaining) : ℝ≥0∞) * epsilon +
                      (rest.length : ℝ≥0∞) * epsilon := hstep
                _ = ((candidateTargetCount target (candidate :: remaining) +
                      rest.length : Nat) : ℝ≥0∞) * epsilon := by
                    push_cast
                    ring
                _ = ((candidate :: remaining).length : ℝ≥0∞) * epsilon := by
                    rw [candidateTargetCount_add_removeTargetCandidates_length target
                      (candidate :: remaining)]

theorem probEvent_plannedCandidateListFire_le (candidates : List Probe) :
    Pr[= true | plannedCandidateListFire candidates] ≤
      (candidates.length : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  exact probEvent_plannedCandidateGroupsFire_le candidates.length candidates le_rfl

theorem probEvent_bind_plannedCandidateListFire_le_of_length
    (plans : ProbComp (List Probe)) (q : Nat)
    (hlength : ∀ candidates ∈ support plans, candidates.length ≤ q) :
    Pr[= true | plans >>= plannedCandidateListFire] ≤
      (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [← probEvent_eq_eq_probOutput]
  apply probEvent_bind_le_of_forall_le
  intro candidates hcandidates
  rw [probEvent_eq_eq_probOutput]
  exact (probEvent_plannedCandidateListFire_le candidates).trans (by
    gcongr
    exact_mod_cast hlength candidates hcandidates)

theorem probEvent_privatePlan_le_of_candidate_game
    (run : ProbComp (Bool × List Probe)) (q : Nat)
    (hdomination : Pr[fun result => result.1 = true | run] ≤
      Pr[= true | (Prod.snd <$> run) >>= plannedCandidateListFire])
    (hlength : ∀ result ∈ support run, result.2.length ≤ q) :
    Pr[fun result => result.1 = true | run] ≤
      (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply hdomination.trans
  apply probEvent_bind_plannedCandidateListFire_le_of_length
  intro candidates hcandidates
  rw [support_map] at hcandidates
  obtain ⟨result, hresult, rfl⟩ := hcandidates
  exact hlength result hresult

end SphincsSecurity.Concrete.OtsProbeSimulation
