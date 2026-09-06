import SphincsSecurity.Proof.SettledCollisionMonitor

namespace SphincsSecurity.Concrete.SettledCollision

open OracleComp OracleSpec

theorem runMonitor_pure (secretKey : SecretKey) (value : α)
    (cache : QueryCache HashSpec) (history : History) :
    runMonitor secretKey (pure value) cache history = pure ((value, cache), history) := rfl

theorem runMonitor_bind (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) (history : History) :
    runMonitor secretKey (computation >>= next) cache history = (do
      let result ← runMonitor secretKey computation cache history
      runMonitor secretKey (next result.1.1) result.1.2 result.2) := by
  induction computation using OracleComp.inductionOn generalizing cache history with
  | pure value => simp [runMonitor]
  | query_bind query continuation ih =>
      simp only [bind_assoc, runMonitor, OracleComp.construct_query_bind]
      exact bind_congr fun result => ih result.1 result.2 _

theorem runMonitor_map (secretKey : SecretKey)
    (f : α → β) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (history : History) :
    runMonitor secretKey (f <$> computation) cache history =
      (fun result => ((f result.1.1, result.1.2), result.2)) <$>
        runMonitor secretKey computation cache history := by
  rw [map_eq_bind_pure_comp, runMonitor_bind]
  rfl

theorem runMonitor_query (secretKey : SecretKey)
    (query : OracleWorld.Domain) (cache : QueryCache HashSpec) (history : History) :
    runMonitor secretKey (OracleWorld.query query) cache history =
      (fun result => (result, advance secretKey cache history query result.1)) <$>
        (romImpl query).run cache := by
  rw [← bind_pure (liftM (OracleWorld.query query) : OracleComp OracleWorld _)]
  rw [runMonitor, OracleComp.construct_query_bind]
  rfl

noncomputable def monitorImpl (secretKey : SecretKey) :
    QueryImpl OracleWorld (StateT (QueryCache HashSpec × History) ProbComp) :=
  fun query state =>
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      runMonitor secretKey (OracleWorld.query query) state.1 state.2

theorem simulateQ_monitorImpl_run (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (history : History) :
    (simulateQ (monitorImpl secretKey) computation).run (cache, history) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        runMonitor secretKey computation cache history := by
  induction computation using OracleComp.inductionOn generalizing cache history with
  | pure value => simp [runMonitor]
  | query_bind query next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, runMonitor_bind]
      simp only [monitorImpl, StateT.run, bind_map_left, map_bind]
      exact bind_congr fun result => ih result.1.1 result.1.2 result.2

theorem runMonitor_eq_simulateQ (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (history : History) :
    runMonitor secretKey computation cache history =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (monitorImpl secretKey) computation).run (cache, history) := by
  rw [simulateQ_monitorImpl_run]
  simp

end SphincsSecurity.Concrete.SettledCollision
