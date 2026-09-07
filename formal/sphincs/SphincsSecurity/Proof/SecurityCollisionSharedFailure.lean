import SphincsSecurity.Proof.SecurityCollisionEncoding
import SphincsSecurity.Proof.SecurityOriginalSharedFailureEndpoint

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
open OtsProbeSimulation
open FtsProbeSimulation.JointOriginal
set_option backward.isDefEq.respectTransparency false

theorem forgeAdvantage_le_collisionBase_add_clean_secret_allowance127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (allowance : ENNReal)
    (hsecrets : Pr[SampledFirstOtsOrCleanSecret | sampledFirstParentRetainedGame adversary] ≤ allowance) :
    forgeAdvantage scheme adversary ≤
      sampledPreParentQueryCharge (fun key cache input => collisionParentStoppedEncodingBaseCharge key cache input +
        ftsParentQueryCharge key cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ +
      allowance + Pr[SampledViewedEvent messageOrForestEvent | sampledViewedGame adversary] := by
  have hbase := forgeAdvantage_le_collisionBase127_add_parent_residual adversary q hq hqMax
  rw [← sampledFirstParentSettlementGame_flag_projection, probEvent_map] at hbase
  apply hbase.trans
  apply (add_le_add le_rfl
    (probEvent_firstParentEncodingResidual_le_clean_secret_allowance adversary allowance hsecrets)).trans_eq
  rw [sampledPreParentQueryCharge_add]
  simp only [show Fintype.card Digest = 2 ^ digestBits from card_bitVec digestBits, add_mul]
  ac_rfl

theorem forgeAdvantage_le_collisionBase_add_sharedFailure_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    forgeAdvantage scheme adversary ≤
      sampledPreParentQueryCharge (fun key cache input => collisionParentStoppedEncodingBaseCharge key cache input +
        ftsParentQueryCharge key cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledParentSharedFailureRisk adversary q fuel +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) :=
  (forgeAdvantage_le_collisionBase_add_clean_secret_allowance127 adversary q hq hqMax _
    (probEvent_sampledFirstOtsOrCleanSecret_le_sharedFailure adversary q hq fuel)).trans
      (add_le_add le_rfl (probEvent_sampled_messageOrForest_le127 adversary q hqPos hq hqMax))

end SphincsSecurity.Concrete
