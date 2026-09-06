import SphincsSecurity.Proof.OuterHashQueryCap
import SphincsSecurity.Proof.FtsProbeOrigin

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem capOuterHashQueries_pure (value : α) (q : Nat) :
    capOuterHashQueries (pure value) q = pure (some value) := rfl

theorem capOuterHashQueries_map
    (computation : OracleComp (OracleWorld + SigningSpec) α) (project : α → β) (q : Nat) :
    capOuterHashQueries (project <$> computation) q = Option.map project <$> capOuterHashQueries computation q := by
  induction computation using OracleComp.inductionOn generalizing q with
  | pure value => rfl
  | query_bind input next ih =>
      rw [map_bind, capOuterHashQueries_query_bind, capOuterHashQueries_query_bind]
      split_ifs
      · cases q with
        | zero => rfl
        | succ q =>
            rw [map_bind]
            exact bind_congr fun reply => ih reply q
      · rw [map_bind]
        exact bind_congr fun reply => ih reply q

def completedSigningTrace (result : Option α × QueryLog SigningSpec) : Option (α × QueryLog SigningSpec) :=
  result.1.map (fun value => (value, result.2))

theorem capOuterHashQueries_signingTrace
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat) :
    capOuterHashQueries (FtsProbeSimulation.signingTraceComputation computation) q =
      completedSigningTrace <$> FtsProbeSimulation.signingTraceComputation (capOuterHashQueries computation q) := by
  induction computation using OracleComp.inductionOn generalizing q with
  | pure value => rfl
  | query_bind input next ih =>
      rw [FtsProbeSimulation.signingTraceComputation_query_bind, capOuterHashQueries_query_bind, capOuterHashQueries_query_bind]
      split_ifs
      · cases q with
        | zero => rfl
        | succ q =>
            rw [FtsProbeSimulation.signingTraceComputation_query_bind, map_bind]
            apply bind_congr
            intro reply
            rw [capOuterHashQueries_map, ih reply q]
            simp only [Functor.map_map]
            apply congrArg (fun f => f <$> _)
            funext result
            rcases result with ⟨value, log⟩
            cases value <;> rfl
      · rw [FtsProbeSimulation.signingTraceComputation_query_bind, map_bind]
        apply bind_congr
        intro reply
        rw [capOuterHashQueries_map, ih reply q]
        simp only [Functor.map_map]
        apply congrArg (fun f => f <$> _)
        funext result
        rcases result with ⟨value, log⟩
        cases value <;> rfl

theorem isQueryBoundP_signingTraceComputation
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : computation.IsQueryBoundP IsOuterHash q) :
    (FtsProbeSimulation.signingTraceComputation computation).IsQueryBoundP IsOuterHash q := by
  induction computation using OracleComp.inductionOn generalizing q with
  | pure value => simp [FtsProbeSimulation.signingTraceComputation]
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [FtsProbeSimulation.signingTraceComputation_query_bind, isQueryBoundP_query_bind_iff]
      refine ⟨hbound.1, fun reply => ?_⟩
      rw [isQueryBoundP_map_iff]
      exact ih reply _ (hbound.2 reply)

end SphincsSecurity.Concrete.OtsProbeSimulation
