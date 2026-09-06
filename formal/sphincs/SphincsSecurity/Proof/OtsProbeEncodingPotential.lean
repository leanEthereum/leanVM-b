import SphincsSecurity.Proof.OtsProbeCachePotential

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def encodingCachePotential (inputs : Finset HashInput) (cache : SplitHashCache) : ENNReal :=
  encodingExhaustionPotential inputs (ordinaryQueryCache cache)

theorem encodingCachePotential_update_hidden
    (inputs : Finset HashInput) (cache : SplitHashCache) (coordinate : Coordinate) (output : HashOutput) :
    encodingCachePotential inputs (Function.update cache (.hidden coordinate) (some output)) = encodingCachePotential inputs cache := by
  rw [encodingCachePotential, ordinaryQueryCache_update_hidden]
  rfl

theorem encodingCachePotential_update_ordinary
    (inputs : Finset HashInput) (cache : SplitHashCache) (input : HashInput) (output : HashOutput) (hnot : input ∉ inputs) :
    encodingCachePotential inputs (Function.update cache (.ordinary input) (some output)) = encodingCachePotential inputs cache := by
  rw [encodingCachePotential, ordinaryQueryCache_update, encodingExhaustionPotential_cacheQuery_of_not_mem inputs _ input output hnot]
  rfl

theorem resolvedCachePotentialBound_splitHashQuery_encoding
    (inputs : Finset HashInput) (key : SplitHashKey) :
    ResolvedCachePotentialBound (encodingCachePotential inputs) (splitHashQuery key) := by
  intro context fuel table cache
  rw [splitHashQuery_run_eq]
  cases hlookup : cache key with
  | some output => simp [runResolvedFromTable, resolvedCachePotential]
  | none =>
      simp only
      unfold LazyRevealProbe.hashOutputQuery
      rw [runResolvedFromTable_hashOutput_query_bind, tsum_probOutput_bind_mul]
      simp only [runResolvedFromTable, construct_pure, tsum_probOutput_pure_mul, resolvedCachePotential]
      cases key with
      | hidden coordinate =>
          simp only [encodingCachePotential_update_hidden]
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left bot_le tsum_probOutput_le_one
      | ordinary input =>
          simp only [encodingCachePotential, ordinaryQueryCache_update]
          exact (expected_encodingExhaustionPotential_fresh inputs (ordinaryQueryCache cache) input hlookup).le

theorem resolvedCachePotentialBound_ordinaryRom_encoding
    (inputs : Finset HashInput) (computation : OracleComp OracleWorld α) :
    ResolvedCachePotentialBound (encodingCachePotential inputs) (simulateQ ordinaryRomImpl computation) := by
  apply resolvedCachePotentialBound_simulateQ
  intro input
  cases input with
  | inl n => exact resolvedCachePotentialBound_lift _ _
  | inr input => exact resolvedCachePotentialBound_splitHashQuery_encoding inputs (.ordinary input)

theorem resolvedCachePotentialBound_ordinaryHash_encoding
    (inputs : Finset HashInput) (computation : OracleComp HashSpec α) :
    ResolvedCachePotentialBound (encodingCachePotential inputs) (simulateQ ordinaryHashImpl computation) :=
  resolvedCachePotentialBound_simulateQ _ _
    (fun input => resolvedCachePotentialBound_splitHashQuery_encoding inputs (.ordinary input)) computation

end SphincsSecurity.Concrete.OtsProbeSimulation
