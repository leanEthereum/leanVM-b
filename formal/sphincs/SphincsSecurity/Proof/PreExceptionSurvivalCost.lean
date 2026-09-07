import SphincsSecurity.Proof.PreExceptionChargeComparison

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

def PreExceptionSurvivalCost
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp OracleWorld α) (cost : Nat) : Prop :=
  ∀ cache hit, (cost : ENNReal) * Pr[fun result => result.2 = false | runExceptionMonitor exception computation cache hit] ≤
    expectedPreExceptionCharge exception charge computation cache hit

theorem preExceptionSurvivalCost_zero
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal) (computation : OracleComp OracleWorld α) :
    PreExceptionSurvivalCost exception charge computation 0 := by
  intro cache hit
  simp only [Nat.cast_zero, zero_mul, zero_le]

theorem preExceptionSurvivalCost_mono
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal) (computation : OracleComp OracleWorld α)
    (a b : Nat) (hcost : PreExceptionSurvivalCost exception charge computation a) (hba : b ≤ a) :
    PreExceptionSurvivalCost exception charge computation b := by
  intro cache hit
  exact (mul_le_mul' (Nat.cast_le.mpr hba) le_rfl).trans (hcost cache hit)

theorem probEvent_survival_bind_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (first : OracleComp OracleWorld α) (second : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) (hit : Bool) :
    Pr[fun result => result.2 = false | runExceptionMonitor exception (first >>= second) cache hit] ≤
      Pr[fun result => result.2 = false | runExceptionMonitor exception first cache hit] := by
  rw [runExceptionMonitor_bind]
  apply probEvent_bind_le_probEvent (p := fun result : (α × QueryCache HashSpec) × Bool => result.2 = false)
  intro result _ hnot
  have htrue : result.2 = true := by
    cases hvalue : result.2 with
    | false => exact (hnot hvalue).elim
    | true => rfl
  rw [htrue, runExceptionMonitor_true, probEvent_map]
  simp

theorem preExceptionSurvivalCost_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (first : OracleComp OracleWorld α) (second : α → OracleComp OracleWorld β) (a b : Nat)
    (hfirst : PreExceptionSurvivalCost exception charge first a)
    (hsecond : ∀ value, PreExceptionSurvivalCost exception charge (second value) b) :
    PreExceptionSurvivalCost exception charge (first >>= second) (a + b) := by
  intro cache hit
  have ha := (mul_le_mul' le_rfl (probEvent_survival_bind_le exception first second cache hit)).trans (hfirst cache hit)
  have hb : (b : ENNReal) * Pr[fun result => result.2 = false | runExceptionMonitor exception (first >>= second) cache hit] ≤
      ∑' result, Pr[= result | runExceptionMonitor exception first cache hit] *
        expectedPreExceptionCharge exception charge (second result.1.1) result.1.2 result.2 := by
    rw [runExceptionMonitor_bind, probEvent_bind_eq_tsum, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro result
    rw [mul_left_comm]
    exact mul_le_mul' le_rfl (hsecond result.1.1 result.1.2 result.2)
  rw [Nat.cast_add, add_mul, expectedPreExceptionCharge_bind]
  exact add_le_add ha hb

theorem preExceptionSurvivalCost_hash
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal) (input : HashInput)
    (hcharge : ∀ cache, 1 ≤ charge cache input) :
    PreExceptionSurvivalCost exception charge (liftM (OracleWorld.query (.inr input))) 1 := by
  intro cache hit
  cases hit with
  | true => rw [runExceptionMonitor_true, probEvent_map]; simp
  | false =>
      rw [expectedPreExceptionCharge_query]
      simp only [Nat.cast_one, one_mul, Bool.false_eq_true, if_false, hashQueryCharge, Sum.elim_inr]
      exact probEvent_le_one.trans (hcharge cache)

end SphincsSecurity
