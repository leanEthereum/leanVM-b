import SphincsSecurity.Proof.OtsProbeErasedCostEnsured

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem capProbeQueries_eq_map_of_probeBound
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (q : Nat)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    capProbeQueries computation q = some <$> computation := by
  induction computation using OracleComp.inductionOn generalizing q with
  | pure value => simp [capProbeQueries, nativeProbeCutAt, privateCutValue]
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [capProbeQueries_query_bind_of_positive input next q
        (fun hprobe => hbound.1.resolve_left (not_not.mpr hprobe)), map_bind]
      exact bind_congr fun output => ih output _ (hbound.2 output)

theorem expectedErasedHistoryProbeCost_map
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (project : α → β) (context : DeferredContext) :
    expectedErasedHistoryProbeCost (project <$> computation) context =
      expectedErasedHistoryProbeCost computation context := by
  rw [map_eq_bind_pure_comp, expectedErasedHistoryProbeCost_bind]
  refine (congrArg (fun cost => expectedErasedHistoryProbeCost computation context + cost) ?_).trans (add_zero _)
  apply ENNReal.tsum_eq_zero.mpr
  intro entry
  cases entry <;> simp [expectedErasedHistoryProbeCost, runErasedHistoryCharged]

theorem expectedErasedHistoryProbeCost_cap_of_probeBound
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (q : Nat) (context : DeferredContext)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    expectedErasedHistoryProbeCost (capProbeQueries computation q) context =
      expectedErasedHistoryProbeCost computation context := by
  rw [capProbeQueries_eq_map_of_probeBound computation q hbound, expectedErasedHistoryProbeCost_map]

theorem sharedHistoryCutCharge_cap_ensuredInitial_le_cost
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (targets : Finset Position) (q : Nat)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    sharedHistoryCutCharge targets (capProbeQueries computation q) (ensuredInitialContext targets) q ≤
      expectedErasedHistoryProbeCost computation (ensuredInitialContext ∅) := by
  apply (sharedHistoryCutCharge_ensuredInitial_le_cost (capProbeQueries computation q) targets q).trans_eq
  exact expectedErasedHistoryProbeCost_cap_of_probeBound computation q (ensuredInitialContext ∅) hbound

end SphincsSecurity.Concrete.OtsProbeSimulation
