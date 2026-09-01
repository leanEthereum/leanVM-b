import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalLift

namespace SphincsSecurity.Concrete.OtsProbeSimulation

def emptyWitnessDeferredContext : DeferredContext :=
  { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
    values := emptyDeferredStructuralValues }

end SphincsSecurity.Concrete.OtsProbeSimulation
