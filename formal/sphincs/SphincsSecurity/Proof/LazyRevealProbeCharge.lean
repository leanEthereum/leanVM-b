import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.AdaptiveRevealProbe
import SphincsSecurity.Proof.LazyRevealProbe

namespace SphincsSecurity.LazyRevealProbe

open OracleComp OracleSpec ENNReal

variable {Coordinate : Type} [DecidableEq Coordinate]

def pendingProbeCharge (state : State Coordinate) (coordinate : Coordinate) (candidate : Digest) : Nat :=
  if state.values coordinate ≠ none then 0
  else if (coordinate, candidate) ∈ state.pending then 0 else 1

end SphincsSecurity.LazyRevealProbe
