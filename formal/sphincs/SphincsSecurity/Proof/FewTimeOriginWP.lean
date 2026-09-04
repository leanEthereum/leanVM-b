import SphincsSecurity.Proof.FewTimeOriginProbability

/-!
# Expected postconditions for stateful oracle simulations

The origin monitor is proved safe by recursion over the adversary computation. This wrapper gives
that recursion its weakest-precondition form and identifies it with the expected postcondition of
the simulated probabilistic computation.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

noncomputable def simulatedExpectedPost
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (computation : OracleComp spec α) (post : α × state → ℝ≥0∞)
    (initialState : state) : ℝ≥0∞ :=
  (OracleComp.recOn (motive := fun _ => (α × state → ℝ≥0∞) → state → ℝ≥0∞)
    computation
    (fun value post currentState => post (value, currentState))
    (fun input _ continuationPosts post currentState =>
      ∑' result, Pr[= result | (implementation input).run currentState] *
        continuationPosts result.1 post result.2)) post initialState

@[simp]
theorem simulatedExpectedPost_pure
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (value : α) (post : α × state → ℝ≥0∞) (initialState : state) :
    simulatedExpectedPost implementation (pure value : OracleComp spec α) post initialState =
      post (value, initialState) := by
  rfl

@[simp]
theorem simulatedExpectedPost_query_bind
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
    (post : α × state → ℝ≥0∞) (initialState : state) :
    simulatedExpectedPost implementation (liftM (spec.query input) >>= next) post initialState =
      ∑' result, Pr[= result | (implementation input).run initialState] *
        simulatedExpectedPost implementation (next result.1) post result.2 := by
  rfl

theorem simulatedExpectedPost_eq_tsum
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (computation : OracleComp spec α) (post : α × state → ℝ≥0∞)
    (initialState : state) :
    simulatedExpectedPost implementation computation post initialState =
      ∑' result, Pr[= result | (simulateQ implementation computation).run initialState] *
        post result := by
  induction computation using OracleComp.inductionOn generalizing initialState with
  | pure value =>
      simp [simulateQ_pure, tsum_probOutput_pure_mul]
  | query_bind input next ih =>
      rw [simulatedExpectedPost_query_bind, simulateQ_bind, StateT.run_bind,
        simulateQ_query, tsum_probOutput_bind_mul]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
      simp_rw [ih]

end SphincsSecurity
