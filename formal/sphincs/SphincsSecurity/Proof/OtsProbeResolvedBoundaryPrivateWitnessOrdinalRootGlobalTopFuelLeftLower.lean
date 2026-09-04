import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalTopBase

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxRecDepth 100000 in
theorem remaining_eq_fuel_of_doneWitness_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hprobeFree : computation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation)) :
    result.remaining = fuel := by
  have hlower := fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
    computation context fuel table result 0 hprobeFree hresult
  have hdetailed : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation) := by
    rw [← map_erase_runDirectResolvedWitnessFromTable computation context fuel table,
      support_map]
    exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
  have hupper := remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable computation context
    fuel table result hdetailed
  omega

set_option maxHeartbeats 1000000 in
theorem fuel_le_remaining_of_doneWitness_maskedPublishedTreeRoot
    (table : OtsSecretIndex → HashOutput) (fuel : Nat)
    (result : ResolvedRunResult (Digest × SplitHashCache))
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable emptyWitnessDeferredContext fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    fuel ≤ result.remaining := by
  exact (remaining_eq_fuel_of_doneWitness_of_probeFree
    (maskedPublishedTreeRoot.run emptySplitHashCache) emptyWitnessDeferredContext fuel table result
    (maskedPublishedTreeRoot_probeFree emptySplitHashCache) hresult).ge

end SphincsSecurity.Concrete.OtsProbeSimulation
