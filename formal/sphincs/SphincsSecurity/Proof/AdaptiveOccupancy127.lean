import SphincsSecurity.Proof.SigningOrderArithmetic

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
set_option backward.isDefEq.respectTransparency false

theorem finiteInitialMixedEnvelope_le_127 (q : Nat) (hq : q ≤ 2 ^ 127) :
    finiteInitialMixedEnvelope q ≤ (29 : ENNReal) * 2 ^ 43 :=
  (finiteInitialMixedEnvelope_le_signingFactorial q hq).trans signingFactorialEnvelope_le

theorem expected_adaptive_validOccupancy_le_127 {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      (if SigningTranscript.Valid result.2.2 then observedLogOccupancy key result.2 else 0)) ≤ (29 : ENNReal) * 2 ^ 43 :=
  (expected_adaptive_validOccupancy_le_signingFactorial key q hq computation cache hnone hbudget).trans signingFactorialEnvelope_le

theorem expected_adaptive_validOccupancy_scaled_le_127 {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      (if SigningTranscript.Valid result.2.2 then observedLogOccupancy key result.2 else 0)) * ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≤
      (29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹ := by
  apply (mul_le_mul_left (expected_adaptive_validOccupancy_le_127 key q hq computation cache hnone hbudget) _).trans_eq
  have hleft : (29 : ENNReal) * 2 ^ 43 * ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≠ ∞ := by finiteness
  have hright : (29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹ ≠ ∞ := by finiteness
  apply (ENNReal.toReal_eq_toReal_iff' hleft hright).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div]

end SphincsSecurity.Concrete
