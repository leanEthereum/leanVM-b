import SphincsSecurity.Proof.OtsProbeSourceFailureBound
import SphincsSecurity.Proof.JointProbeCandidateBudget
import SphincsSecurity.Proof.SecurityJointCompletionSplitEndpoint

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation
attribute [local instance] Classical.propDecidable

noncomputable def sampledNativeFtsMaterializedProbeRisk (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      initializedSourceMaterializedRisk
        (FtsProbeSimulation.nativeFtsRetainedSource adversary parameter (FtsProbeSimulation.curryFtsTableEquiv ftsSecret) q) fuel

theorem sampledNativeFtsOtsFailureRisk_le_direct_add_materialized
    (adversary : Adversary) (q fuel : Nat) (hbudget : q < fuel) (hspace : fuel < Fintype.card Digest) :
    sampledNativeFtsOtsFailureRisk adversary q fuel ≤
      sampledNativeFtsDirectRisk Finset.univ adversary fuel q + sampledNativeFtsMaterializedProbeRisk adversary q fuel := by
  unfold sampledNativeFtsOtsFailureRisk sampledNativeFtsDirectRisk sampledNativeFtsMaterializedProbeRisk
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro parameter
  rw [← mul_add, ← ENNReal.tsum_add]
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  rw [← mul_add]
  exact mul_le_mul' le_rfl (probEvent_sampled_source_finish_le_direct_add_materialized
    (FtsProbeSimulation.nativeFtsRetainedSource adversary parameter (FtsProbeSimulation.curryFtsTableEquiv ftsSecret) q) q fuel
    (FtsProbeSimulation.nativeFtsRetainedSource_probeBound adversary parameter _ q) hbudget hspace)

theorem sampledNativeFtsOtsFailure_add_fts_hit_le_query_rate_add_materialized
    (adversary : Adversary) (q fuel : Nat) (hbudget : q < fuel) (hspace : fuel < Fintype.card Digest) :
    sampledNativeFtsOtsFailureRisk adversary q fuel + sampledJointRetainedFtsHitRisk adversary q ≤
      (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + sampledNativeFtsMaterializedProbeRisk adversary q fuel := by
  calc
    _ ≤ (sampledNativeFtsDirectRisk Finset.univ adversary fuel q + sampledNativeFtsMaterializedProbeRisk adversary q fuel) +
        sampledJointRetainedFtsHitRisk adversary q :=
      add_le_add (sampledNativeFtsOtsFailureRisk_le_direct_add_materialized adversary q fuel hbudget hspace) le_rfl
    _ = (sampledNativeFtsDirectRisk Finset.univ adversary fuel q + sampledJointRetainedFtsHitRisk adversary q) +
        sampledNativeFtsMaterializedProbeRisk adversary q fuel := by ac_rfl
    _ ≤ _ := add_le_add (sampledNativeFtsDirect_add_fts_hit_le_query_rate Finset.univ adversary fuel q
      (hbudget.trans hspace).le) le_rfl

theorem forgeAdvantage_le_joint_query_rate_add_materialized_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      ((q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + sampledNativeFtsMaterializedProbeRisk adversary q (q + 1)) +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by
  have hspace : q + 1 < Fintype.card Digest := by
    have hcard : Fintype.card Digest = 2 ^ 128 := by
      rw [show Fintype.card Digest = 2 ^ digestBits from card_bitVec digestBits]
      rfl
    rw [hcard]
    omega
  exact (forgeAdvantage_le_nativeFts_ots_add_fts_remaining127 adversary q hqPos hq hqMax (q + 1)).trans
    (add_le_add (add_le_add le_rfl
      (sampledNativeFtsOtsFailure_add_fts_hit_le_query_rate_add_materialized adversary q (q + 1) (by omega) hspace)) le_rfl)

end SphincsSecurity.Concrete
