import SphincsSecurity.Proof.OtsProbeCappedHistoryFts

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def replaceOrdinaryCache (cache : SplitHashCache) (ordinary : QueryCache HashSpec) : SplitHashCache
  | .ordinary input => ordinary input
  | .hidden coordinate => cache (.hidden coordinate)

theorem ordinaryQueryCache_replaceOrdinaryCache (cache : SplitHashCache) (ordinary : QueryCache HashSpec) :
    ordinaryQueryCache (replaceOrdinaryCache cache ordinary) = ordinary := rfl

theorem replaceOrdinaryCache_self (cache : SplitHashCache) :
    replaceOrdinaryCache cache (ordinaryQueryCache cache) = cache := by
  funext key
  cases key <;> rfl

theorem replaceOrdinaryCache_replace (cache : SplitHashCache) (left right : QueryCache HashSpec) :
    replaceOrdinaryCache (replaceOrdinaryCache cache left) right = replaceOrdinaryCache cache right := by
  funext key
  cases key <;> rfl

theorem replaceOrdinaryCache_cacheQuery (cache : SplitHashCache) (input : HashInput) (output : HashOutput) :
    replaceOrdinaryCache cache ((ordinaryQueryCache cache).cacheQuery input output) =
      Function.update cache (.ordinary input) (some output) := by
  funext key
  cases key with
  | hidden coordinate => simp [replaceOrdinaryCache, Function.update]
  | ordinary other =>
      by_cases heq : other = input <;> simp [replaceOrdinaryCache, QueryCache.cacheQuery, Function.update, ordinaryQueryCache, heq]

def ordinaryHistoryResult (context : DeferredContext) (fuel : Nat) (history : List Probe)
    (cache : SplitHashCache) (result : α × QueryCache HashSpec) : Option (HistoryResolvedPrefix (α × SplitHashCache)) :=
  some ⟨context, fuel, (result.1, replaceOrdinaryCache cache result.2), history⟩

theorem runHistoryPrefix_ordinaryHash
    (input : HashInput) (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache) :
    runResolvedHistoryPrefix ((ordinaryHashImpl input).run cache) context fuel history =
      ordinaryHistoryResult context fuel history cache <$>
        (randomOracle (spec := HashSpec) input).run (ordinaryQueryCache cache) := by
  change runResolvedHistoryPrefix ((splitHashQuery (.ordinary input)).run cache) context fuel history = _
  rw [splitHashQuery_run_eq]
  cases hlookup : cache (.ordinary input) with
  | some output =>
      rw [QueryImpl.withCaching_run_some uniformSampleImpl (show ordinaryQueryCache cache input = some output from hlookup)]
      simp [runResolvedHistoryPrefix, ordinaryHistoryResult, replaceOrdinaryCache_self]
  | none =>
      rw [QueryImpl.withCaching_run_none uniformSampleImpl (show ordinaryQueryCache cache input = none from hlookup)]
      rw [LazyRevealProbe.hashOutputQuery, runResolvedHistoryPrefix_query_bind]
      change (LazyRevealProbe.sampleHashOutput >>= fun output =>
          pure (some (⟨context, fuel, (output, Function.update cache (.ordinary input) (some output)), history⟩ : HistoryResolvedPrefix (HashOutput × SplitHashCache)))) = _
      simp only [Functor.map_map, ordinaryHistoryResult, replaceOrdinaryCache_cacheQuery]
      rfl

theorem runHistoryPrefix_simulateQ_ordinaryHashImpl
    (computation : OracleComp HashSpec α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache) :
    runResolvedHistoryPrefix ((simulateQ ordinaryHashImpl computation).run cache) context fuel history =
      ordinaryHistoryResult context fuel history cache <$>
        (simulateQ (randomOracle : QueryImpl HashSpec _) computation).run (ordinaryQueryCache cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel history cache with
  | pure value => simp [runResolvedHistoryPrefix, ordinaryHistoryResult, replaceOrdinaryCache_self]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, runResolvedHistoryPrefix_bind,
        runHistoryPrefix_ordinaryHash, bind_map_left]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      apply bind_congr
      intro result
      dsimp only [ordinaryHistoryResult]
      rw [ih, ordinaryQueryCache_replaceOrdinaryCache]
      congr 1

theorem eraseProbeQueries_eq_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    eraseProbeQueries computation = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [eraseProbeQueries, construct_query_bind]
      cases input
      case probe coordinate digest => simp [LazyRevealProbe.IsProbe] at hbound
      all_goals
        apply bind_congr
        intro output
        exact ih output (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)

theorem runErasedHistoryPrefix_simulateQ_ordinaryHashImpl
    (computation : OracleComp HashSpec α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache) :
    runResolvedHistoryPrefix (eraseProbeQueries ((simulateQ ordinaryHashImpl computation).run cache)) context fuel history =
      ordinaryHistoryResult context fuel history cache <$>
        (simulateQ (randomOracle : QueryImpl HashSpec _) computation).run (ordinaryQueryCache cache) := by
  rw [eraseProbeQueries_eq_of_probeFree _ (simulateQ_ordinaryHashImpl_probeFree computation cache)]
  exact runHistoryPrefix_simulateQ_ordinaryHashImpl computation context fuel history cache

theorem capProbeQueries_bind_probeFree
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) (q : Nat)
    (hfree : left.IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    capProbeQueries (left >>= next) q = left >>= fun value => capProbeQueries (next value) q := by
  induction left using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input continuation ih =>
      rw [isQueryBoundP_query_bind_iff] at hfree
      have hnot : ¬LazyRevealProbe.IsProbe input := by simpa using hfree.1
      rw [bind_assoc, capProbeQueries_query_bind, if_neg hnot, bind_assoc]
      apply bind_congr
      intro output
      exact ih output (by simpa using hfree.2 output)

theorem runErasedHistoryPrefix_capped_ordinary_block
    (computation : OracleComp HashSpec α)
    (next : α × SplitHashCache → OracleComp (LazyRevealProbe.World Coordinate) β)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache) :
    runResolvedHistoryPrefix
      (eraseProbeQueries (capProbeQueries (((simulateQ ordinaryHashImpl computation).run cache) >>= next) q))
      context fuel history =
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run (ordinaryQueryCache cache) >>= fun result =>
        runResolvedHistoryPrefix
          (eraseProbeQueries (capProbeQueries (next (result.1, replaceOrdinaryCache cache result.2)) q))
          context fuel history) := by
  rw [capProbeQueries_bind_probeFree _ next q (simulateQ_ordinaryHashImpl_probeFree computation cache),
    eraseProbeQueries_bind, runResolvedHistoryPrefix_bind, runErasedHistoryPrefix_simulateQ_ordinaryHashImpl,
    bind_map_left]
  rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
