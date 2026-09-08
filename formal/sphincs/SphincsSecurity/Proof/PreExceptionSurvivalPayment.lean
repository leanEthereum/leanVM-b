import SphincsSecurity.Proof.PreExceptionSurvivalCost

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem expectedPreExceptionCharge_bind_le_of_survivalCost
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (left right : QueryCache HashSpec → HashInput → ENNReal)
    (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) (cost : Nat)
    (hcost : PreExceptionSurvivalCost exception right first cost)
    (hnext : ∀ value current, expectedPreExceptionCharge exception left (next value) current false ≤ cost)
    (cache : QueryCache HashSpec) (hit : Bool)
    (hzero : expectedPreExceptionCharge exception left first cache hit = 0) :
    expectedPreExceptionCharge exception left (first >>= next) cache hit ≤
      expectedPreExceptionCharge exception right (first >>= next) cache hit := by
  rw [expectedPreExceptionCharge_bind, expectedPreExceptionCharge_bind, hzero, zero_add]
  apply le_trans ?_ le_self_add
  apply le_trans ?_ (hcost cache hit)
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro result
  cases result.2 with
  | false =>
      rw [mul_comm (cost : ENNReal)]
      exact mul_le_mul' le_rfl (hnext result.1.1 result.1.2)
  | true => simp

end SphincsSecurity
