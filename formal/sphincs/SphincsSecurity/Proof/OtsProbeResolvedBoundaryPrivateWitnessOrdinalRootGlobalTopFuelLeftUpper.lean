import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalTopFuelLeftLower

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxHeartbeats 1000000 in
theorem remaining_le_fuel_of_doneWitness_maskedPublishedTreeRoot
    (table : OtsSecretIndex → HashOutput) (fuel : Nat)
    (result : ResolvedRunResult (Digest × SplitHashCache))
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable emptyWitnessDeferredContext fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    result.remaining ≤ fuel := by
  exact (remaining_eq_fuel_of_doneWitness_of_probeFree
    (maskedPublishedTreeRoot.run emptySplitHashCache) emptyWitnessDeferredContext fuel table result
    (maskedPublishedTreeRoot_probeFree emptySplitHashCache) hresult).le

end SphincsSecurity.Concrete.OtsProbeSimulation
