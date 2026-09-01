import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassification

/-!
# Fixed-table diagnostic root kernel

The operational root-or-doomed coupling is composed with the diagnostic finalizer in this separate
module so the resulting relational proof term is compiled once before table sampling.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_granularAllCanonical_diagnosticRootRel
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    RelTriple
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q)
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table >>=
        finishObservedMaterializedDiagnostic table)
      SnapshotObservedDiagnosticRootRel := by
  exact relTriple_finishObservedDiagnostic_of_rootOrDoomed table _ _
    (relTriple_granularAllCanonical_observedMaterialized_rootOrDoomed adversary parameter
      ftsSecret q table hbound)

end SphincsSecurity.Concrete.OtsProbeSimulation
