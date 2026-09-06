import SphincsSecurity.Proof.JointProbeRetainedCost
import SphincsSecurity.Proof.OtsProbeStepCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot

def NonSecretHashInput (parameter : PublicParameter) (input : HashInput) : Prop :=
  (¬ ∃ position : Position, OtsProbeSimulation.IsOtsPosition position ∧ AtPosition parameter input position) ∧
    decodeProbe? parameter input = none

noncomputable def jointNonSecretQueryCharge (parameter : PublicParameter) : JointQueryCharge
  | .inl (.inr input), _, _, _, _ => if NonSecretHashInput parameter input then 1 else 0
  | _, _, _, _, _ => 0

theorem jointOts_add_fts_add_nonSecret_queryCharge_le_one
    (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain)
    (context : OtsProbeSimulation.DeferredContext) (cache : OtsProbeSimulation.SplitHashCache)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsCache : SplitHashCache) :
    (jointOtsQueryCharge parameter input context cache state ftsCache +
      jointFtsQueryCharge parameter input context cache state ftsCache) +
      jointNonSecretQueryCharge parameter input context cache state ftsCache ≤
        if OtsProbeSimulation.IsOuterHash input then 1 else 0 := by
  cases input with
  | inl input =>
      cases input with
      | inl n => simp [jointOtsQueryCharge, jointFtsQueryCharge, jointNonSecretQueryCharge, OtsProbeSimulation.IsOuterHash]
      | inr input =>
          by_cases hnon : NonSecretHashInput parameter input
          · rw [jointOtsQueryCharge, OtsProbeSimulation.probingHashQuery_eq_split_of_not_atOtsPosition parameter input hnon.1,
              OtsProbeSimulation.expectedErasedHistoryProbeCost_eq_zero_of_probeFree _ context
                (OtsProbeSimulation.splitHashQuery_probeFree _ _)]
            simp [jointFtsQueryCharge, jointHashProbeCharge, hnon.2, jointNonSecretQueryCharge, hnon,
              OtsProbeSimulation.IsOuterHash]
          · simpa only [jointNonSecretQueryCharge, if_neg hnon, add_zero] using
              jointOts_add_fts_queryCharge_le_one parameter (.inl (.inr input)) context cache state ftsCache
  | inr message => simp [jointOtsQueryCharge, jointFtsQueryCharge, jointNonSecretQueryCharge, OtsProbeSimulation.IsOuterHash]

theorem expectedJointRetainedCharge_add
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat)
    (left right : JointQueryCharge) :
    expectedJointRetainedCharge adversary parameter table q
        (fun input context cache state ftsCache => left input context cache state ftsCache + right input context cache state ftsCache) =
      expectedJointRetainedCharge adversary parameter table q left +
        expectedJointRetainedCharge adversary parameter table q right := by
  unfold expectedJointRetainedCharge
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  rw [← mul_add]
  congr 1
  cases result with
  | stopped hit => simp
  | done hit state value =>
      rcases value with ⟨entry, ftsCache⟩
      cases entry with
      | none => simp
      | some entry => exact expectedJointQueryCharge_add parameter entry.value.1 table left right _ _ _ _ _ _ _ _

theorem expectedJointRetainedCharge_le_outerBound
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat)
    (charge : JointQueryCharge)
    (hcharge : ∀ input context cache state ftsCache, charge input context cache state ftsCache ≤
      if OtsProbeSimulation.IsOuterHash input then 1 else 0) :
    expectedJointRetainedCharge adversary parameter table q charge ≤ q := by
  unfold expectedJointRetainedCharge
  calc
    _ ≤ ∑' result, Pr[= result | AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty q
        ((liftNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
          OtsProbeSimulation.emptySplitHashCache).run emptySplitHashCache)] * (q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro result
      apply mul_le_mul' le_rfl
      cases result with
      | stopped hit => exact bot_le
      | done hit state value =>
          rcases value with ⟨entry, ftsCache⟩
          cases entry with
          | none => exact bot_le
          | some entry =>
              apply expectedJointQueryCharge_le_outerBound parameter entry.value.1 table charge hcharge _ q
              rw [isQueryBoundP_map_iff]
              exact OtsProbeSimulation.capOuterHashQueries_hashBound _ q
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one

theorem expectedJointRetainedOts_add_fts_add_nonSecret_le_q
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat) :
    (expectedJointRetainedCharge adversary parameter table q (jointOtsQueryCharge parameter) +
      expectedJointRetainedCharge adversary parameter table q (jointFtsQueryCharge parameter)) +
      expectedJointRetainedCharge adversary parameter table q (jointNonSecretQueryCharge parameter) ≤ q := by
  rw [← expectedJointRetainedCharge_add, ← expectedJointRetainedCharge_add]
  exact expectedJointRetainedCharge_le_outerBound adversary parameter table q _
    (jointOts_add_fts_add_nonSecret_queryCharge_le_one parameter)

end SphincsSecurity.Concrete.FtsProbeSimulation

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def sampledJointNonSecretQueryCharge (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      FtsProbeSimulation.expectedJointRetainedCharge adversary parameter (FtsProbeSimulation.curryFtsTableEquiv ftsSecret) q
        (FtsProbeSimulation.jointNonSecretQueryCharge parameter)

theorem sampledNativeFtsOts_add_fts_add_nonSecret_charge_le_q (adversary : Adversary) (q : Nat) :
    (sampledNativeFtsOtsCharge adversary q + sampledJointRetainedProbeCharge adversary q) +
      sampledJointNonSecretQueryCharge adversary q ≤ q := by
  rw [sampledNativeFtsOtsCharge_eq_jointObserver]
  unfold sampledJointObservedOtsCharge sampledJointRetainedProbeCharge sampledJointNonSecretQueryCharge
  simp_rw [FtsProbeSimulation.jointRetainedProbeCharge_eq_sampled_observer]
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  calc
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] * (q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro parameter
      rw [← mul_add, ← mul_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      rw [← mul_add, ← mul_add]
      exact mul_le_mul' le_rfl
        (FtsProbeSimulation.expectedJointRetainedOts_add_fts_add_nonSecret_le_q adversary parameter _ q)
    _ ≤ _ := by
      simp_rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one (mul_le_mul' tsum_probOutput_le_one le_rfl)).trans_eq (by simp)

theorem sampledNativeFtsOts_add_nonSecret_add_fts_hit_le_query_rate (adversary : Adversary) (q : Nat) :
    (sampledNativeFtsOtsCharge adversary q + sampledJointNonSecretQueryCharge adversary q) *
        (Fintype.card Digest : ENNReal)⁻¹ + sampledJointRetainedFtsHitRisk adversary q ≤
      (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  apply (add_le_add le_rfl (sampledJointRetainedFtsHitRisk_le_probeCharge adversary q)).trans
  rw [← add_mul]
  apply mul_le_mul' _ le_rfl
  simpa only [add_assoc, add_comm, add_left_comm] using
    sampledNativeFtsOts_add_fts_add_nonSecret_charge_le_q adversary q

end SphincsSecurity.Concrete
