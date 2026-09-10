import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePlan
import SphincsSecurity.Proof.OtsProbeResolvedSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

theorem runResolvedFromTable_executeCandidate_zero
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) (candidate : Option Probe) :
    runResolvedFromTable context 0 table ((executeCandidate? candidate).run cache) =
      if candidate.isSome then pure none else pure (some ⟨context, 0, ((), cache), table⟩) := by
  cases candidate with
  | none => simp [executeCandidate?, runResolvedFromTable]
  | some candidate =>
      change runResolvedFromTable context 0 table
        (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate >>= fun _ => pure ((), cache)) = _
      rw [LazyRevealProbe.probeQuery, runResolvedFromTable_probe_query_bind]
      rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
