import SphincsSecurity.Proof.SettledCollisionViewedGame
import SphincsSecurity.Proof.SecurityVerifierPrimitiveEndpoint

namespace SphincsSecurity.Concrete.SettledCollision

open OracleComp OracleSpec ENNReal

theorem forgeAdvantage_le_settled_charge_add_remaining_primitive (adversary : Adversary)
    (q : Nat) (hqPos : 1 ≤ q) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    forgeAdvantage scheme adversary ≤
      (sampledQueryCharge queryCharge adversary * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        Pr[SampledMonitorEvent remainingPrimitiveEvent | sampledViewedMonitorGame adversary]) +
      ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ +
        ((23 * q : Nat) : ℝ≥0∞) * ((2 ^ 134 : Nat) : ℝ≥0∞)⁻¹) :=
  (forgeAdvantage_le_sampled_verifierPrimitive_add_occupancy_remaining adversary q hqPos hq hqMax).trans
    (add_le_add (probEvent_sampled_verifierPrimitive_le_charge_add_remaining adversary) le_rfl)

end SphincsSecurity.Concrete.SettledCollision
