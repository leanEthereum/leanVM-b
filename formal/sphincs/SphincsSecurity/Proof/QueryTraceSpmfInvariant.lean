import SphincsSecurity.Proof.QueryTraceInvariant
import SphincsSecurity.Proof.RetainedObservation

namespace SphincsSecurity.QueryPause

open _root_.OracleComp OracleSpec Concrete.RetainedObservation
set_option backward.isDefEq.respectTransparency false

theorem traced_spmf_invariant {Index Trace Result State : Type} {spec : OracleSpec Index} [Monoid Trace]
    (observation : (input : spec.Domain) → spec.Range input → Trace)
    (impl : QueryImpl spec (StateT State SPMF)) (invariant : Trace → State → Prop)
    (hstep : ∀ history state, invariant history state → ∀ input result,
      (impl input).run state result ≠ 0 → invariant (history * observation input result.1) result.2)
    (computation : OracleComp spec Result) (history : Trace) (state : State) (hinitial : invariant history state)
    (result : (Result × Trace) × State)
    (hresult : (simulateQ impl (traced observation computation)).run state result ≠ 0) :
    invariant (history * result.1.2) result.2 := by
  induction computation using OracleComp.inductionOn generalizing history state result with
  | pure value =>
      simp only [traced_pure, simulateQ_pure, StateT.run_pure, ne_eq,
        SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      simpa only [mul_one] using hinitial
  | query_bind input next ih =>
      simp only [traced_query_bind, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, ← bind_pure_comp] at hresult
      obtain ⟨middle, hmiddle, hcontinuation⟩ := (bind_nonzero _ _ _).mp hresult
      obtain ⟨tail, htail, heq⟩ := (bind_nonzero _ _ _).mp hcontinuation
      simp only [simulateQ_pure, StateT.run_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
      subst result
      simpa only [mul_assoc] using ih middle.1 (history * observation input middle.1) middle.2
        (hstep history state hinitial input middle hmiddle) tail htail

end SphincsSecurity.QueryPause
