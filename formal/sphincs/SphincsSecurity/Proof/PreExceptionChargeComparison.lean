import SphincsSecurity.Proof.PreExceptionQueryCharge
import SphincsSecurity.Proof.ExceptionWitness

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem runExceptionMonitor_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) (hit : Bool) :
    runExceptionMonitor exception (computation >>= next) cache hit =
      runExceptionMonitor exception computation cache hit >>= fun result =>
        runExceptionMonitor exception (next result.1.1) result.1.2 result.2 := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp [runExceptionMonitor]
  | query_bind query continuation ih =>
      rw [bind_assoc, runExceptionMonitor, construct_query_bind,
        runExceptionMonitor, construct_query_bind, bind_assoc]
      exact bind_congr fun result => ih result.1 result.2 _

theorem expectedPreExceptionCharge_eq_zero_of_queryCharge_eq_zero
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool)
    (hzero : expectedQueryCharge charge computation cache = 0) :
    expectedPreExceptionCharge exception charge computation cache hit = 0 :=
  le_antisymm ((expectedPreExceptionCharge_le_queryCharge exception charge computation cache hit).trans_eq hzero) bot_le

theorem expectedPreExceptionCharge_query
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (query : OracleWorld.Domain) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception charge (OracleSpec.query query) cache hit =
      if hit then 0 else hashQueryCharge charge cache query := by
  simpa only [bind_pure, expectedPreExceptionCharge_pure, mul_zero, tsum_zero, add_zero] using
    expectedPreExceptionCharge_query_bind exception charge query pure cache hit

theorem expectedPreExceptionCharge_bind_le_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (first second : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) (hit : Bool)
    (hleft : expectedPreExceptionCharge exception first computation cache hit ≤
      expectedPreExceptionCharge exception second computation cache hit)
    (hright : ∀ result ∈ support (runExceptionMonitor exception computation cache hit),
      expectedPreExceptionCharge exception first (next result.1.1) result.1.2 result.2 ≤
        expectedPreExceptionCharge exception second (next result.1.1) result.1.2 result.2) :
    expectedPreExceptionCharge exception first (computation >>= next) cache hit ≤
      expectedPreExceptionCharge exception second (computation >>= next) cache hit := by
  rw [expectedPreExceptionCharge_bind, expectedPreExceptionCharge_bind]
  apply add_le_add hleft
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (runExceptionMonitor exception computation cache hit)
  · exact mul_le_mul' le_rfl (hright result hr)
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

theorem expectedPreExceptionCharge_lift_sequenceFin_le {n : Nat}
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (first second : QueryCache HashSpec → HashInput → ENNReal)
    (computation : Fin n → OracleComp HashSpec α)
    (h : ∀ i cache hit, expectedPreExceptionCharge exception first (liftM (computation i) : OracleComp OracleWorld α) cache hit ≤
      expectedPreExceptionCharge exception second (liftM (computation i) : OracleComp OracleWorld α) cache hit)
    (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception first (liftM (Concrete.sequenceFin computation) : OracleComp OracleWorld _) cache hit ≤
      expectedPreExceptionCharge exception second (liftM (Concrete.sequenceFin computation) : OracleComp OracleWorld _) cache hit := by
  induction n generalizing cache hit with
  | zero => simp [Concrete.sequenceFin]
  | succ n ih =>
      rw [Concrete.sequenceFin, liftM_bind]
      apply expectedPreExceptionCharge_bind_le_bind _ _ _ _ _ _ _ (h 0 cache hit)
      intro result _
      rw [liftM_bind]
      apply expectedPreExceptionCharge_bind_le_bind _ _ _ _ _ _ _
        (ih (fun i => computation i.succ) (fun i => h i.succ) result.1.2 result.2)
      intros
      simp

end SphincsSecurity
