import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalTopFuelLeftUpper

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxRecDepth 100000 in
theorem remaining_eq_fuel_of_mem_observed_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ObservedCleanRunResult α)
    (hprobeFree : computation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table computation)) :
    result.remaining = fuel := by
  have hlower := fuel_le_remaining_add_of_mem_runObservedCleanFromTable computation observations
    state fuel table result 0 hprobeFree hresult
  have hupper := remaining_le_of_mem_runObservedCleanFromTable computation observations state fuel
    table result hresult
  omega

set_option maxHeartbeats 1000000 in
theorem fuel_le_remaining_of_mem_observed_maskedPublishedTreeRoot
    (table : OtsSecretIndex → HashOutput) (fuel : Nat)
    (result : ResolvedRunResult (Digest × SplitHashCache))
    (hresult : some (observedResolvedResult [] result) ∈ support
      (runObservedCleanFromTable [] LazyRevealProbe.State.empty fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    fuel ≤ result.remaining := by
  have heq := remaining_eq_fuel_of_mem_observed_of_probeFree
    (maskedPublishedTreeRoot.run emptySplitHashCache) [] LazyRevealProbe.State.empty fuel table
    (observedResolvedResult [] result) (maskedPublishedTreeRoot_probeFree emptySplitHashCache)
    hresult
  simpa [observedResolvedResult] using heq.ge

end SphincsSecurity.Concrete.OtsProbeSimulation
