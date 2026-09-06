import SphincsSecurity.Proof.JointProbeMaterializedRiskBound

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

theorem forgeAdvantage_le_joint_query_rate_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      ((q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal)) +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) :=
  (forgeAdvantage_le_joint_query_rate_add_materialized_remaining127 adversary q hqPos hq hqMax).trans
    (add_le_add (add_le_add le_rfl (add_le_add le_rfl (sampledNativeFtsMaterializedProbeRisk_le_inv216 adversary q (q + 1)))) le_rfl)

end SphincsSecurity.Concrete
