import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeSampling

/-!
# Global root boundary

The early clean failure is split before the delayed witness is classified by ordinal or position.
This module contains the probability rule used by that split. The failure event lives on the
comparison run, while the residual event stays on the original run, so later unions cannot copy
the failure term.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

structure CleanProbeObservation where
  coordinate : Coordinate
  candidate : Digest
  valueAtProbe : Option HashOutput
  revealedAtProbe : Bool
deriving DecidableEq

structure ObservedCleanRunResult (alpha : Type) where
  state : LazyRevealProbe.State Coordinate
  remaining : Nat
  value : alpha
  table : OtsSecretIndex → HashOutput
  observations : List CleanProbeObservation

end SphincsSecurity.Concrete.OtsProbeSimulation
