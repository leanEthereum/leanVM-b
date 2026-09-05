import SphincsSecurity.Proof.OtsProbeExecutionCharge
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalOperational
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassification

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

def unmaterializedCandidateCharge (state : LazyRevealProbe.State Coordinate) : Option Probe → Nat
  | none => 0
  | some candidate => if candidate.coordinate ∈ state.revealed then 0
      else LazyRevealProbe.pendingProbeCharge state candidate.coordinate candidate.candidate

def materializedCandidateCharge (state : LazyRevealProbe.State Coordinate) : Option Probe → Nat
  | none => 0
  | some candidate => if candidate.coordinate ∈ state.revealed ∨
      (candidate.coordinate, candidate.candidate) ∈ state.pending then 0
      else if state.values candidate.coordinate ≠ none then 1 else 0

theorem candidateCharge_sum_le_one (state : LazyRevealProbe.State Coordinate) (candidate : Option Probe) :
    unmaterializedCandidateCharge state candidate + materializedCandidateCharge state candidate ≤ 1 := by
  cases candidate with
  | none => exact Nat.zero_le 1
  | some candidate =>
      simp only [unmaterializedCandidateCharge, materializedCandidateCharge, LazyRevealProbe.pendingProbeCharge]
      split_ifs <;> omega

theorem unmaterializedCandidateCharge_eq_zero_of_existingHiddenHit
    (state : LazyRevealProbe.State Coordinate) (candidate : Probe)
    (hhit : (cleanProbeObservation state candidate.coordinate candidate.candidate).ExistingHiddenHit) :
    unmaterializedCandidateCharge state (some candidate) = 0 := by
  obtain ⟨_, output, hvalue, _⟩ := hhit
  change state.values candidate.coordinate = some output at hvalue
  simp [unmaterializedCandidateCharge, LazyRevealProbe.pendingProbeCharge, hvalue]

theorem materializedCandidateCharge_eq_one_of_existingHiddenHit
    (state : LazyRevealProbe.State Coordinate) (candidate : Probe)
    (hhit : (cleanProbeObservation state candidate.coordinate candidate.candidate).ExistingHiddenHit)
    (hfresh : (candidate.coordinate, candidate.candidate) ∉ state.pending) :
    materializedCandidateCharge state (some candidate) = 1 := by
  obtain ⟨hrevealed, output, hvalue, _⟩ := hhit
  have hhidden : candidate.coordinate ∉ state.revealed := by
    simpa only [cleanProbeObservation, decide_eq_false_iff_not] using hrevealed
  change state.values candidate.coordinate = some output at hvalue
  simp [materializedCandidateCharge, hhidden, hfresh, hvalue]

theorem materializedCandidateCharge_eq_one_of_first_existingHiddenHit
    (state : LazyRevealProbe.State Coordinate) (candidate : Probe) (observations : List CleanProbeObservation)
    (htracked : CleanProbeObservationsTrackedBy observations state)
    (hcovered : CleanProbeObservationsCoverPending observations state)
    (hprior : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hhit : (cleanProbeObservation state candidate.coordinate candidate.candidate).ExistingHiddenHit) :
    materializedCandidateCharge state (some candidate) = 1 := by
  apply materializedCandidateCharge_eq_one_of_existingHiddenHit state candidate hhit
  intro hpending
  let result : ObservedCleanRunResult Unit := ⟨state, 0, (), fun _ => 0, observations⟩
  have hvalid := directDeferredContext_valid_of_no_existingHiddenHit result htracked hcovered (by
    rintro ⟨observation, hobservation, hearlier⟩
    exact hprior observation hobservation hearlier)
  obtain ⟨_, output, hvalue, hcandidate⟩ := hhit
  change state.values candidate.coordinate = some output at hvalue
  apply hvalid.2 candidate.coordinate output hvalue
  change truncateHash output ∈ state.pendingAt candidate.coordinate
  rw [hcandidate]
  exact (LazyRevealProbe.State.mem_pendingAt_iff state candidate.coordinate candidate.candidate).2 hpending

theorem executeCandidate_expectedCharge_le (candidate : Option Probe) (cache : SplitHashCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    LazyRevealProbe.expectedProbeCharge ((executeCandidate? candidate).run cache) state fuel ≤
      unmaterializedCandidateCharge state candidate := by
  cases candidate with
  | none => simp [executeCandidate?, LazyRevealProbe.expectedProbeCharge, unmaterializedCandidateCharge]
  | some candidate =>
      change LazyRevealProbe.expectedProbeCharge
        ((LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate) >>= fun _ => pure ((), cache))
        state fuel ≤ _
      rw [LazyRevealProbe.probeQuery, LazyRevealProbe.expectedProbeCharge_query_bind]
      cases fuel with
      | zero => exact bot_le
      | succ remaining =>
          by_cases hrevealed : candidate.coordinate ∈ state.revealed
          · simp only [hrevealed, ↓reduceIte, unmaterializedCandidateCharge,
              LazyRevealProbe.expectedProbeCharge, OracleComp.construct_pure, Nat.cast_zero, le_refl]
          · simp only [hrevealed, ↓reduceIte, unmaterializedCandidateCharge,
              LazyRevealProbe.expectedProbeCharge, OracleComp.construct_pure, add_zero, le_refl]

theorem probingHashQueryAfterRootAwarePlan_expectedCharge_le
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery) (cache : SplitHashCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    LazyRevealProbe.expectedProbeCharge ((probingHashQueryAfterRootAwarePlan parameter input plan).run cache)
        state fuel ≤ unmaterializedCandidateCharge state (rootAwareCandidateForPlan? parameter input plan) := by
  unfold probingHashQueryAfterRootAwarePlan
  rw [StateT.run_bind, LazyRevealProbe.expectedProbeCharge_bind_of_tail_probeFree]
  · exact executeCandidate_expectedCharge_le _ cache state fuel
  · intro result
    cases plan.action with
    | ordinary => exact splitHashQuery_probeFree _ result.2
    | resolve coordinate => exact resolveKnownInput_probeFree parameter coordinate input result.2

theorem probingHashQueryAfterRootAwarePublicPlan_expectedCharge_le
    (parameter : PublicParameter) (input : HashInput) (publicState : LazyRevealProbe.State Coordinate)
    (plan : PlannedHashQuery) (cache : SplitHashCache) (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    LazyRevealProbe.expectedProbeCharge
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache) state fuel ≤
      unmaterializedCandidateCharge state (rootAwareCandidateForPlan? parameter input plan) := by
  unfold probingHashQueryAfterRootAwarePublicPlan
  rw [StateT.run_bind, LazyRevealProbe.expectedProbeCharge_bind_of_tail_probeFree]
  · exact executeCandidate_expectedCharge_le _ cache state fuel
  · intro result
    exact probingHashQueryPublicAction_probeFree parameter input publicState plan.action result.2

theorem probingHashQueryAfterRootAwarePublicPlan_charge_add_materialized_le_one
    (parameter : PublicParameter) (input : HashInput) (publicState : LazyRevealProbe.State Coordinate)
    (plan : PlannedHashQuery) (cache : SplitHashCache) (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    LazyRevealProbe.expectedProbeCharge
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache) state fuel +
      (materializedCandidateCharge state (rootAwareCandidateForPlan? parameter input plan) : ℝ≥0∞) ≤ 1 := by
  apply (add_le_add (probingHashQueryAfterRootAwarePublicPlan_expectedCharge_le
    parameter input publicState plan cache state fuel) le_rfl).trans
  rw [← Nat.cast_add, ← Nat.cast_one]
  exact Nat.cast_le.mpr (candidateCharge_sum_le_one state _)

theorem probingHashQueryAfterRootAwarePublicPlan_charge_eq_zero_of_existingHiddenHit
    (parameter : PublicParameter) (input : HashInput) (publicState : LazyRevealProbe.State Coordinate)
    (plan : PlannedHashQuery) (cache : SplitHashCache) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (candidate : Probe) (hcandidate : rootAwareCandidateForPlan? parameter input plan = some candidate)
    (hhit : (cleanProbeObservation state candidate.coordinate candidate.candidate).ExistingHiddenHit) :
    LazyRevealProbe.expectedProbeCharge
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache) state fuel = 0 := by
  have hbound := probingHashQueryAfterRootAwarePublicPlan_expectedCharge_le parameter input publicState plan cache state fuel
  rw [hcandidate, unmaterializedCandidateCharge_eq_zero_of_existingHiddenHit state candidate hhit, Nat.cast_zero] at hbound
  exact le_antisymm hbound zero_le

end SphincsSecurity.Concrete.OtsProbeSimulation
