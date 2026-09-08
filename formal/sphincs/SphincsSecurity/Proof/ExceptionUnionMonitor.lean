import SphincsSecurity.Proof.AmortizedExceptions

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem queryException_union
    (left right : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (cache : QueryCache HashSpec) (query : OracleWorld.Domain) (answer : OracleWorld.Range query) :
    queryException (fun before input output => left before input output ∨ right before input output) cache query answer =
      (queryException left cache query answer || queryException right cache query answer) := by
  classical
  cases query with
  | inl sample => rfl
  | inr input =>
      by_cases hfresh : cache input = none <;>
        by_cases hl : left cache input answer <;>
          by_cases hr : right cache input answer <;>
            simp only [queryException, hfresh, hl, hr, true_or, or_true, false_or,
              true_and, false_and, decide_true, decide_false, Bool.true_or, Bool.false_or]

theorem probEvent_runExceptionMonitor_union_le
    (left right : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (leftHit rightHit : Bool) :
    Pr[fun result => result.2 = true |
      runExceptionMonitor (fun before input output => left before input output ∨ right before input output)
        computation cache (leftHit || rightHit)] ≤
      Pr[fun result => result.2 = true | runExceptionMonitor left computation cache leftHit] +
        Pr[fun result => result.2 = true | runExceptionMonitor right computation cache rightHit] := by
  induction computation using OracleComp.inductionOn generalizing cache leftHit rightHit with
  | pure value =>
      cases leftHit <;> cases rightHit <;>
        simp [runExceptionMonitor, probEvent_pure]
  | query_bind query next ih =>
      simp only [runExceptionMonitor, construct_query_bind, probEvent_bind_eq_tsum]
      rw [← ENNReal.tsum_add]
      simp_rw [← mul_add]
      apply ENNReal.tsum_le_tsum
      intro result
      have hflags : ((leftHit || rightHit) || queryException
          (fun before input output => left before input output ∨ right before input output) cache query result.1) =
          ((leftHit || queryException left cache query result.1) || (rightHit || queryException right cache query result.1)) := by
        rw [queryException_union]
        simp only [Bool.or_assoc, Bool.or_left_comm]
      rw [hflags]
      exact mul_le_mul' le_rfl (ih result.1 result.2 _ _)

end SphincsSecurity
