import SphincsSecurity.Proof.OtsProbeHistoryOrdinaryHash

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def ordinaryResolvedResult (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) (result : α × QueryCache HashSpec) : Option (ResolvedRunResult (α × SplitHashCache)) :=
  some ⟨context, fuel, (result.1, replaceOrdinaryCache cache result.2), table⟩

theorem runResolved_ordinaryHash
    (input : HashInput) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runResolvedFromTable context fuel table ((ordinaryHashImpl input).run cache) =
      ordinaryResolvedResult context fuel table cache <$>
        (randomOracle (spec := HashSpec) input).run (ordinaryQueryCache cache) := by
  change runResolvedFromTable context fuel table ((splitHashQuery (.ordinary input)).run cache) = _
  rw [splitHashQuery_run_eq]
  cases hlookup : cache (.ordinary input) with
  | some output =>
      rw [QueryImpl.withCaching_run_some uniformSampleImpl (show ordinaryQueryCache cache input = some output from hlookup)]
      simp [runResolvedFromTable, ordinaryResolvedResult, replaceOrdinaryCache_self]
  | none =>
      rw [QueryImpl.withCaching_run_none uniformSampleImpl (show ordinaryQueryCache cache input = none from hlookup)]
      rw [LazyRevealProbe.hashOutputQuery, runResolvedFromTable_hashOutput_query_bind]
      change (LazyRevealProbe.sampleHashOutput >>= fun output =>
          pure (some (⟨context, fuel, (output, Function.update cache (.ordinary input) (some output)), table⟩ : ResolvedRunResult (HashOutput × SplitHashCache)))) = _
      simp only [Functor.map_map, ordinaryResolvedResult, replaceOrdinaryCache_cacheQuery]
      rfl

theorem runResolved_simulateQ_ordinaryHashImpl
    (computation : OracleComp HashSpec α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runResolvedFromTable context fuel table ((simulateQ ordinaryHashImpl computation).run cache) =
      ordinaryResolvedResult context fuel table cache <$>
        (simulateQ (randomOracle : QueryImpl HashSpec _) computation).run (ordinaryQueryCache cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value => simp [runResolvedFromTable, ordinaryResolvedResult, replaceOrdinaryCache_self]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, runResolvedFromTable_bind,
        runResolved_ordinaryHash, bind_map_left]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      apply bind_congr
      intro result
      dsimp only [ordinaryResolvedResult]
      rw [ih, ordinaryQueryCache_replaceOrdinaryCache]
      congr 1

end SphincsSecurity.Concrete.OtsProbeSimulation
