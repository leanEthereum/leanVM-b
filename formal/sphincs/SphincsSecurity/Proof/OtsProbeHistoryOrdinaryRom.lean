import SphincsSecurity.Proof.OtsProbeHistoryOrdinaryHash

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem runHistoryPrefix_ordinaryRom_query
    (input : OracleWorld.Domain)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache) :
    runResolvedHistoryPrefix ((ordinaryRomImpl input).run cache) context fuel history =
      ordinaryHistoryResult context fuel history cache <$>
        (romImpl input).run (ordinaryQueryCache cache) := by
  cases input with
  | inr input => exact runHistoryPrefix_ordinaryHash input context fuel history cache
  | inl n =>
      change runResolvedHistoryPrefix
        ((LazyRevealProbe.uniformQuery (Coordinate := Coordinate) n) >>= fun output => pure (output, cache))
          context fuel history =
        ordinaryHistoryResult context fuel history cache <$>
          ((fun output => (output, ordinaryQueryCache cache)) <$>
            (liftM (unifSpec.query n) : ProbComp _))
      rw [LazyRevealProbe.uniformQuery, runResolvedHistoryPrefix_query_bind]
      simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, runResolvedHistoryPrefix,
        construct_pure, Functor.map_map, ordinaryHistoryResult, replaceOrdinaryCache_self]
      rfl

theorem runHistoryPrefix_simulateQ_ordinaryRomImpl
    (computation : OracleComp OracleWorld α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache) :
    runResolvedHistoryPrefix ((simulateQ ordinaryRomImpl computation).run cache) context fuel history =
      ordinaryHistoryResult context fuel history cache <$>
        (simulateQ romImpl computation).run (ordinaryQueryCache cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel history cache with
  | pure value => simp [runResolvedHistoryPrefix, ordinaryHistoryResult, replaceOrdinaryCache_self]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, runResolvedHistoryPrefix_bind,
        runHistoryPrefix_ordinaryRom_query, bind_map_left]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      apply bind_congr
      intro result
      dsimp only [ordinaryHistoryResult]
      rw [ih, ordinaryQueryCache_replaceOrdinaryCache]
      congr 1

theorem runErasedHistoryPrefix_simulateQ_ordinaryRomImpl
    (computation : OracleComp OracleWorld α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache) :
    runResolvedHistoryPrefix (eraseProbeQueries ((simulateQ ordinaryRomImpl computation).run cache)) context fuel history =
      ordinaryHistoryResult context fuel history cache <$>
        (simulateQ romImpl computation).run (ordinaryQueryCache cache) := by
  rw [eraseProbeQueries_eq_of_probeFree _ (simulateQ_ordinaryRomImpl_probeFree computation cache)]
  exact runHistoryPrefix_simulateQ_ordinaryRomImpl computation context fuel history cache

theorem mem_support_ordinaryRom_of_historyPrefix
    (computation : OracleComp OracleWorld α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache)
    (entry : HistoryResolvedPrefix (α × SplitHashCache))
    (hresult : some entry ∈ support (runResolvedHistoryPrefix
      (eraseProbeQueries ((simulateQ ordinaryRomImpl computation).run cache)) context fuel history)) :
    (entry.value.1, ordinaryQueryCache entry.value.2) ∈ support
      ((simulateQ romImpl computation).run (ordinaryQueryCache cache)) := by
  rw [runErasedHistoryPrefix_simulateQ_ordinaryRomImpl, support_map] at hresult
  obtain ⟨result, hresult, heq⟩ := hresult
  simp only [ordinaryHistoryResult, Option.some.injEq] at heq
  subst entry
  exact hresult

end SphincsSecurity.Concrete.OtsProbeSimulation
