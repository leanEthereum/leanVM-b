import SphincsSecurity.Proof.EncodingPrehitMonitor

namespace SphincsSecurity.Concrete.TightEncoding

open OracleComp OracleSpec

theorem runEncodingPrehitMonitor_pure (secretKey : SecretKey) (value : α)
    (cache : QueryCache HashSpec) (hit : Bool) :
    runEncodingPrehitMonitor secretKey (pure value) cache hit = pure ((value, cache), hit) := rfl

theorem runEncodingPrehitMonitor_bind (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) (hit : Bool) :
    runEncodingPrehitMonitor secretKey (computation >>= next) cache hit = (do
      let result ← runEncodingPrehitMonitor secretKey computation cache hit
      runEncodingPrehitMonitor secretKey (next result.1.1) result.1.2 result.2) := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp [runEncodingPrehitMonitor]
  | query_bind query continuation ih =>
      simp only [bind_assoc, runEncodingPrehitMonitor, OracleComp.construct_query_bind]
      exact bind_congr fun result => ih result.1 result.2 _

theorem runEncodingPrehitMonitor_map (secretKey : SecretKey)
    (f : α → β) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hit : Bool) :
    runEncodingPrehitMonitor secretKey (f <$> computation) cache hit =
      (fun result => ((f result.1.1, result.1.2), result.2)) <$>
        runEncodingPrehitMonitor secretKey computation cache hit := by
  rw [map_eq_bind_pure_comp, runEncodingPrehitMonitor_bind]
  rfl

theorem runEncodingPrehitMonitor_query (secretKey : SecretKey)
    (query : OracleWorld.Domain) (cache : QueryCache HashSpec) (hit : Bool) :
    runEncodingPrehitMonitor secretKey (OracleWorld.query query) cache hit =
      (fun result => (result, hit || encodingPrehitQuery secretKey cache query result.1)) <$>
        (romImpl query).run cache := by
  rw [← bind_pure (liftM (OracleWorld.query query) : OracleComp OracleWorld _)]
  rw [runEncodingPrehitMonitor, OracleComp.construct_query_bind]
  rfl

noncomputable def encodingPrehitImpl (secretKey : SecretKey) :
    QueryImpl OracleWorld (StateT (QueryCache HashSpec × Bool) ProbComp) :=
  fun query state =>
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      runEncodingPrehitMonitor secretKey (OracleWorld.query query) state.1 state.2

theorem simulateQ_encodingPrehitImpl_run (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool) :
    (simulateQ (encodingPrehitImpl secretKey) computation).run (cache, hit) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        runEncodingPrehitMonitor secretKey computation cache hit := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp [runEncodingPrehitMonitor]
  | query_bind query next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, runEncodingPrehitMonitor_bind]
      simp only [encodingPrehitImpl, StateT.run, bind_map_left, map_bind]
      exact bind_congr fun result => ih result.1.1 result.1.2 result.2

theorem runEncodingPrehitMonitor_eq_simulateQ (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool) :
    runEncodingPrehitMonitor secretKey computation cache hit =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (encodingPrehitImpl secretKey) computation).run (cache, hit) := by
  rw [simulateQ_encodingPrehitImpl_run]
  simp

end SphincsSecurity.Concrete.TightEncoding
