import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Statement

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

noncomputable def queryException
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (cache : QueryCache HashSpec) : (query : OracleWorld.Domain) → OracleWorld.Range query → Bool
  | .inl _, _ => false
  | .inr input, answer => by
      classical
      exact decide (cache input = none ∧ exception cache input answer)

noncomputable def runExceptionMonitor
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool) :
    ProbComp ((α × QueryCache HashSpec) × Bool) :=
  OracleComp.construct
    (C := fun _ => QueryCache HashSpec → Bool → ProbComp ((α × QueryCache HashSpec) × Bool))
    (fun value cache hit => pure ((value, cache), hit))
    (fun query _ next cache hit => do
      let result ← (romImpl query).run cache
      next result.1 result.2 (hit || queryException exception cache query result.1))
    computation cache hit

theorem runExceptionMonitor_project
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool) :
    Prod.fst <$> runExceptionMonitor exception computation cache hit = (simulateQ romImpl computation).run cache := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp [runExceptionMonitor, simulateQ_pure]
  | query_bind query next ih =>
      rw [runExceptionMonitor, OracleComp.construct_query_bind, map_bind,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact bind_congr fun result => ih result.1 result.2 _

end SphincsSecurity
