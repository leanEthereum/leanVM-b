import SphincsSecurity.Proof.OtsProbeHistoryEnsured

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem runErasedHistoryCharged_enlargeEnsured
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (extra : Finset Coordinate) :
    runErasedHistoryCharged computation (context.enlargeEnsured extra) =
      (fun result => (result.1.map (fun entry => entry.enlargeEnsured extra), result.2)) <$>
        runErasedHistoryCharged computation context := by
  induction computation using OracleComp.inductionOn generalizing context with
  | pure value => simp [runErasedHistoryCharged, HistoryResolvedPrefix.enlargeEnsured]
  | query_bind input next ih =>
      rw [runErasedHistoryCharged_query_bind, runResolvedHistoryPrefix_enlargeEnsured,
        bind_map_left, runErasedHistoryCharged_query_bind, map_bind]
      apply bind_congr
      intro entry
      cases entry with
      | none => rfl
      | some entry =>
          dsimp only [Option.map_some, HistoryResolvedPrefix.enlargeEnsured]
          rw [ih, Functor.map_map, Functor.map_map]
          rfl

theorem expectedErasedHistoryProbeCost_enlargeEnsured
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (extra : Finset Coordinate) :
    expectedErasedHistoryProbeCost computation (context.enlargeEnsured extra) =
      expectedErasedHistoryProbeCost computation context := by
  unfold expectedErasedHistoryProbeCost
  rw [runErasedHistoryCharged_enlargeEnsured, tsum_probOutput_map_mul]

theorem ensuredInitialContext_eq_enlarge_empty (targets : Finset Position) :
    ensuredInitialContext targets = (ensuredInitialContext ∅).enlargeEnsured (targets.image Coordinate.position) := by
  simp [ensuredInitialContext, DeferredContext.enlargeEnsured]

theorem expectedErasedHistoryProbeCost_ensuredInitial
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (targets : Finset Position) :
    expectedErasedHistoryProbeCost computation (ensuredInitialContext targets) =
      expectedErasedHistoryProbeCost computation (ensuredInitialContext ∅) := by
  rw [ensuredInitialContext_eq_enlarge_empty targets, expectedErasedHistoryProbeCost_enlargeEnsured]

theorem sharedHistoryCutCharge_ensuredInitial_le_cost
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (targets : Finset Position) (q : Nat) :
    sharedHistoryCutCharge targets computation (ensuredInitialContext targets) q ≤
      expectedErasedHistoryProbeCost computation (ensuredInitialContext ∅) := by
  rw [← expectedErasedHistoryProbeCost_ensuredInitial computation targets]
  exact sharedHistoryCutCharge_le_expectedProbeCost targets computation (ensuredInitialContext targets) q

end SphincsSecurity.Concrete.OtsProbeSimulation
