import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobal

/-!
# Sound global root classification

Guarded finalization conflates a fresh completion hit with a probe that matches a hidden value
materialized by an earlier outer query. This file keeps that distinction explicit. The ordinary
unguarded finalizer accounts for the fresh branch, while a Boolean records whether the state was
already non-completable before finalization. The latter branch is retained for the delayed-root
classification instead of being charged as fresh randomness.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

structure ObservedMaterializedDiagnostic (alpha : Type) where
  before : Option (ObservedCleanRunResult alpha)
  final : Option (ObservedCleanRunResult alpha)
  wasDoomed : Bool

def ObservedMaterializedDiagnostic.Bad
    (outcome : ObservedMaterializedDiagnostic alpha) : Prop :=
  outcome.final = none ∨ outcome.wasDoomed = true

end SphincsSecurity.Concrete.OtsProbeSimulation
