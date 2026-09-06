import SphincsSecurity.Proof.FtsProbeJointObserverFtsCost
import SphincsSecurity.Proof.FtsProbeJointCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot

noncomputable def expectedJointRetainedCharge
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat) (charge : JointQueryCharge) : ENNReal :=
  ∑' result, Pr[= result | AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty q
    ((liftNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
      OtsProbeSimulation.emptySplitHashCache).run emptySplitHashCache)] *
    match result with
    | .stopped _ => 0
    | .done _ state (entry, ftsCache) => match entry with
      | none => 0
      | some entry => expectedJointQueryCharge parameter entry.value.1 table charge
          (Option.map (fun rest => (entry.value.1, rest)) <$>
            OtsProbeSimulation.capOuterHashQueries (retainedGameRestComputation adversary ⟨entry.value.1, parameter⟩) q)
          state q entry.context entry.remaining entry.history entry.value.2 ftsCache

theorem expectedJointRetainedOts_add_fts_le_q
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat) :
    expectedJointRetainedCharge adversary parameter table q (jointOtsQueryCharge parameter) +
      expectedJointRetainedCharge adversary parameter table q (jointFtsQueryCharge parameter) ≤ q := by
  unfold expectedJointRetainedCharge
  rw [← ENNReal.tsum_add]
  calc
    _ ≤ ∑' result, Pr[= result | AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty q
        ((liftNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
          OtsProbeSimulation.emptySplitHashCache).run emptySplitHashCache)] * (q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro result
      rw [← mul_add]
      apply mul_le_mul' le_rfl
      cases result with
      | stopped hit => simp
      | done hit state value =>
          rcases value with ⟨entry, ftsCache⟩
          cases entry with
          | none => simp
          | some entry =>
              apply expectedJointOts_add_fts_charge_le_outerBound parameter entry.value.1 table _ q _
                state q entry.context entry.remaining entry.history entry.value.2 ftsCache
              rw [isQueryBoundP_map_iff]
              exact OtsProbeSimulation.capOuterHashQueries_hashBound _ q
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one

theorem expectedRunChargedCost_jointRetained
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat) :
    AdaptiveRevealProbe.expectedRunChargedCost table AdaptiveRevealProbe.State.empty q
      ((maskedJointRetained adversary parameter q (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
        OtsProbeSimulation.emptySplitHashCache).run emptySplitHashCache) =
      expectedJointRetainedCharge adversary parameter table q (jointFtsQueryCharge parameter) := by
  unfold maskedJointRetained bindNativeSteps
  rw [StateT.run_bind, AdaptiveRevealProbe.expectedRunChargedCost_bind_of_resume
    table AdaptiveRevealProbe.State.empty q q 0 _ _ (by
      convert AdaptiveRevealProbe.runCharged_bind_probeFree table AdaptiveRevealProbe.State.empty q _ _
        (liftNativeBlock_probeFree OtsProbeSimulation.maskedPublishedTreeRoot (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
          OtsProbeSimulation.emptySplitHashCache emptySplitHashCache) using 1
      apply bind_congr
      intro result
      cases result <;> simp), Nat.cast_zero, zero_add]
  unfold expectedJointRetainedCharge
  apply tsum_congr
  intro result
  congr 1
  cases result with
  | stopped hit => rfl
  | done hit state value =>
      rcases value with ⟨entry, ftsCache⟩
      cases entry with
      | none => exact AdaptiveRevealProbe.expectedRunChargedCost_pure table state q (none, ftsCache)
      | some entry =>
          apply expectedRunChargedCost_maskedJointComputation parameter entry.value.1 table _ q _ state q le_rfl
            entry.context entry.remaining entry.history entry.value.2 ftsCache
          rw [isQueryBoundP_map_iff]
          exact OtsProbeSimulation.capOuterHashQueries_hashBound _ q

end SphincsSecurity.Concrete.FtsProbeSimulation
