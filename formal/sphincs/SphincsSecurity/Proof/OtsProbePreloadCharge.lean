import SphincsSecurity.Proof.OtsProbeRootQueryReserve
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionCommonFactorization

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

theorem candidateCharge_sum_eq (state : LazyRevealProbe.State Coordinate) (candidate : Probe) :
    unmaterializedCandidateCharge state (some candidate) + materializedCandidateCharge state (some candidate) =
      if candidate.coordinate ∈ state.revealed ∨ (candidate.coordinate, candidate.candidate) ∈ state.pending then 0 else 1 := by
  classical
  simp only [unmaterializedCandidateCharge, materializedCandidateCharge, LazyRevealProbe.pendingProbeCharge]
  split_ifs <;> simp_all

theorem candidateCharge_sum_eq_of_pending_revealed_eq
    (left right : LazyRevealProbe.State Coordinate) (candidate : Option Probe)
    (hpending : left.pending = right.pending) (hrevealed : left.revealed = right.revealed) :
    unmaterializedCandidateCharge left candidate + materializedCandidateCharge left candidate =
      unmaterializedCandidateCharge right candidate + materializedCandidateCharge right candidate := by
  cases candidate with
  | none => rfl
  | some candidate => rw [candidateCharge_sum_eq, candidateCharge_sum_eq, hpending, hrevealed]

theorem candidateCharge_sum_preload_eq
    (state : LazyRevealProbe.State Coordinate) (candidate : Option Probe)
    (target : Position) (output : HashOutput) :
    unmaterializedCandidateCharge (preloadPositionValue target output state) candidate +
        materializedCandidateCharge (preloadPositionValue target output state) candidate =
      unmaterializedCandidateCharge state candidate + materializedCandidateCharge state candidate :=
  candidateCharge_sum_eq_of_pending_revealed_eq _ _ candidate rfl rfl

theorem materializedCandidateCharge_preload_eq_unmaterialized
    (state : LazyRevealProbe.State Coordinate) (target : Position) (output : HashOutput) (candidate : Digest)
    (hvalue : state.values (.position target) = none) :
    materializedCandidateCharge (preloadPositionValue target output state) (some ⟨.position target, candidate⟩) =
      unmaterializedCandidateCharge state (some ⟨.position target, candidate⟩) := by
  classical
  simp [materializedCandidateCharge, unmaterializedCandidateCharge, LazyRevealProbe.pendingProbeCharge,
    preloadPositionValue, hvalue]
  split_ifs <;> simp_all

theorem unmaterializedCandidateCharge_preload_target_eq_zero
    (state : LazyRevealProbe.State Coordinate) (target : Position) (output : HashOutput) (candidate : Digest) :
    unmaterializedCandidateCharge (preloadPositionValue target output state) (some ⟨.position target, candidate⟩) = 0 := by
  classical
  simp [unmaterializedCandidateCharge, LazyRevealProbe.pendingProbeCharge, preloadPositionValue]

theorem probingHashQueryAfterRootAwarePublicPlan_preloadedCharge_le_originalCharge
    (parameter : PublicParameter) (input : HashInput) (publicState : LazyRevealProbe.State Coordinate)
    (plan : PlannedHashQuery) (cache : SplitHashCache) (context : DeferredContext) (fuel : Nat)
    (target : Position) (output : HashOutput) :
    ordinaryContinuationCharge (fun _ _ _ => 0)
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache)
        { context with state := preloadPositionValue target output context.state } fuel +
      (materializedCandidateCharge (preloadPositionValue target output context.state)
        (rootAwareCandidateForPlan? parameter input plan) : ℝ≥0∞) ≤
      ((unmaterializedCandidateCharge context.state (rootAwareCandidateForPlan? parameter input plan) +
        materializedCandidateCharge context.state (rootAwareCandidateForPlan? parameter input plan) : Nat) : ℝ≥0∞) := by
  unfold probingHashQueryAfterRootAwarePublicPlan
  rw [StateT.run_bind, ordinaryContinuationCharge_zero_bind_of_tail_probeFree _
    (fun result : Unit × SplitHashCache => (probingHashQueryPublicAction parameter input publicState plan.action).run result.2)
    (fun result => probingHashQueryPublicAction_probeFree parameter input publicState plan.action result.2)]
  apply (add_le_add (executeCandidate_ordinaryCharge_le _ cache _ fuel) le_rfl).trans_eq
  rw [← Nat.cast_add]
  exact congrArg (fun value : Nat => (value : ℝ≥0∞)) (candidateCharge_sum_preload_eq context.state _ target output)

theorem probingHashQueryAfterRootAwarePublicPlan_preloadedWeightedCharge_le_originalCharge
    (parameter : PublicParameter) (input : HashInput) (publicState : LazyRevealProbe.State Coordinate)
    (plan : PlannedHashQuery) (cache : SplitHashCache) (context : DeferredContext) (fuel : Nat)
    (target : Position) (output : HashOutput) :
    ordinaryContinuationCharge (fun _ _ _ => 0)
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache)
        { context with state := preloadPositionValue target output context.state } fuel +
      (materializedCandidateCharge (preloadPositionValue target output context.state)
        (rootAwareCandidateForPlan? parameter input plan) : ℝ≥0∞) * (4 / 3) ≤
      ((unmaterializedCandidateCharge context.state (rootAwareCandidateForPlan? parameter input plan) +
        materializedCandidateCharge context.state (rootAwareCandidateForPlan? parameter input plan) : Nat) : ℝ≥0∞) *
          (4 / 3) := by
  have hfactor : (1 : ℝ≥0∞) ≤ 4 / 3 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num
  calc
    _ ≤ (ordinaryContinuationCharge (fun _ _ _ => 0)
          ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache)
          { context with state := preloadPositionValue target output context.state } fuel +
        (materializedCandidateCharge (preloadPositionValue target output context.state)
          (rootAwareCandidateForPlan? parameter input plan) : ℝ≥0∞)) * (4 / 3) := by
      rw [add_mul]
      exact add_le_add (by simpa only [mul_one] using mul_le_mul' le_rfl hfactor) le_rfl
    _ ≤ _ := mul_le_mul' (probingHashQueryAfterRootAwarePublicPlan_preloadedCharge_le_originalCharge
      parameter input publicState plan cache context fuel target output) le_rfl

theorem canonicalPreloadedQuery_weightedCharge_le_originalCharge
    (parameter : PublicParameter) (input : HashInput) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) (context : DeferredContext) (fuel : Nat)
    (target : Position) (output : HashOutput)
    (hhidden : Coordinate.position target ∉ context.state.revealed) :
    let preloaded := preloadPositionValue target output context.state
    let publicState := (materializedCanonicalContext table preloaded).state
    let plan := purePlanProbingHashQuery parameter input publicState
    let originalPlan := purePlanProbingHashQuery parameter input (materializedCanonicalContext table context.state).state
    ordinaryContinuationCharge (fun _ _ _ => 0)
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache)
        { context with state := preloaded } fuel +
      (materializedCandidateCharge preloaded (rootAwareCandidateForPlan? parameter input plan) : ℝ≥0∞) * (4 / 3) ≤
      ((unmaterializedCandidateCharge context.state (rootAwareCandidateForPlan? parameter input originalPlan) +
        materializedCandidateCharge context.state (rootAwareCandidateForPlan? parameter input originalPlan) : Nat) : ℝ≥0∞) *
          (4 / 3) := by
  dsimp only
  have hplan := purePlanProbingHashQuery_eq_of_values_eq
    (materializedCanonicalContext_values_preload_hidden table context.state target output hhidden) parameter input
  rw [hplan]
  exact probingHashQueryAfterRootAwarePublicPlan_preloadedWeightedCharge_le_originalCharge parameter input
    (materializedCanonicalContext table (preloadPositionValue target output context.state)).state
    (purePlanProbingHashQuery parameter input (materializedCanonicalContext table context.state).state)
    cache context fuel target output

end SphincsSecurity.Concrete.OtsProbeSimulation
