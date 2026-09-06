import SphincsSecurity.Proof.FtsProbeJointRetainedBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot

theorem jointRetainedProbeCharge_eq_sampled_observer
    (adversary : Adversary) (parameter : PublicParameter) (q : Nat) :
    jointRetainedProbeCharge adversary parameter q =
      ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
        expectedJointRetainedCharge adversary parameter (curryFtsTableEquiv ftsSecret) q (jointFtsQueryCharge parameter) := by
  rw [jointRetainedProbeCharge_eq_expectedCost, AdaptiveRevealProbe.chargedExperiment, tsum_probOutput_bind_mul]
  have hextend (table : Coordinate → Digest) :
      AdaptiveRevealProbe.extendTable (AdaptiveRevealProbe.State.empty : AdaptiveRevealProbe.State Coordinate) table = table := by
    funext coordinate
    rfl
  simp only [hextend]
  change (∑' table, Pr[= table | AdaptiveRevealProbe.sampleTable] *
    AdaptiveRevealProbe.expectedRunChargedCost table AdaptiveRevealProbe.State.empty q
      ((maskedJointRetained adversary parameter q (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
        OtsProbeSimulation.emptySplitHashCache).run emptySplitHashCache)) = _
  simp_rw [expectedRunChargedCost_jointRetained]
  calc
    _ = ∑' table, Pr[= table | curryFtsTableEquiv <$> sampleFtsSecrets] *
        expectedJointRetainedCharge adversary parameter table q (jointFtsQueryCharge parameter) := by
      apply tsum_congr
      intro table
      rw [OracleComp.probOutput_congr (x := table) (y := table) rfl evalDist_uncurry_sampleFtsSecrets]
    _ = _ := by rw [tsum_probOutput_map_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def sampledJointObservedOtsCharge (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      FtsProbeSimulation.expectedJointRetainedCharge adversary parameter (FtsProbeSimulation.curryFtsTableEquiv ftsSecret) q
        (FtsProbeSimulation.jointOtsQueryCharge parameter)

theorem sampledJointObservedOts_add_fts_charge_le_q (adversary : Adversary) (q : Nat) :
    sampledJointObservedOtsCharge adversary q + sampledJointRetainedProbeCharge adversary q ≤ q := by
  unfold sampledJointObservedOtsCharge sampledJointRetainedProbeCharge
  simp_rw [FtsProbeSimulation.jointRetainedProbeCharge_eq_sampled_observer]
  rw [← ENNReal.tsum_add]
  calc
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] * (q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro parameter
      rw [← mul_add, ← ENNReal.tsum_add]
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      rw [← mul_add]
      exact mul_le_mul' le_rfl (FtsProbeSimulation.expectedJointRetainedOts_add_fts_le_q adversary parameter _ q)
    _ ≤ _ := by
      simp_rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one (mul_le_mul' tsum_probOutput_le_one le_rfl)).trans_eq (by simp)

theorem sampledJointObservedOts_add_fts_hit_le_query_rate (adversary : Adversary) (q : Nat) :
    sampledJointObservedOtsCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledJointRetainedFtsHitRisk adversary q ≤ (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  apply (add_le_add le_rfl (sampledJointRetainedFtsHitRisk_le_probeCharge adversary q)).trans
  rw [← add_mul]
  exact mul_le_mul' (sampledJointObservedOts_add_fts_charge_le_q adversary q) le_rfl

end SphincsSecurity.Concrete
