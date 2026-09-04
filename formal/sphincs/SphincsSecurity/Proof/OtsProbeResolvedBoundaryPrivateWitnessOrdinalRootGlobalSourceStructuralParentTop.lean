import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceStructuralParent

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxRecDepth 100000 in
theorem snapshotsHaveStructuralParents_of_mem_granularCanonicalPrivateWitnessSnapshotObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : ResolvedRunResult (Digest × SplitHashCache))
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (canonicalizeDirectWitnessSnapshotObserve table
        (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter
          table ftsSecret)
        result.context result.remaining result.value [])) :
    SnapshotsHaveStructuralParents output.2 := by
  apply snapshotsHaveStructuralParents_of_mem_canonicalizeDirectWitnessSnapshotObserve table
    (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter table
      ftsSecret)
    result.context result.remaining result.value [] snapshotsHaveStructuralParents_nil
    (output := output) (houtput := houtput)
  intro finalOutput hfinalOutput
  exact snapshotsHaveStructuralParents_of_mem_granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve
    adversary parameter table ftsSecret
    (canonicalizeMaterializedValues table result.context) result.remaining result.value []
    snapshotsHaveStructuralParents_nil finalOutput hfinalOutput

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem snapshotsHaveStructuralParents_of_mem_granularAllCanonicalPrivateWitnessSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel)) :
    SnapshotsHaveStructuralParents output.2 := by
  unfold granularAllCanonicalPrivateWitnessSnapshot runDirectWitnessSnapshotObserve at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨result, _hresult, hfinish⟩ := houtput
  apply snapshotsHaveStructuralParents_of_mem_finishDirectWitnessSnapshotObserve _ [] result
    snapshotsHaveStructuralParents_nil (output := output) (houtput := hfinish)
  intro resolved heq nextOutput hnextOutput
  subst result
  exact snapshotsHaveStructuralParents_of_mem_granularCanonicalPrivateWitnessSnapshotObserve
    adversary parameter table ftsSecret resolved nextOutput hnextOutput

end SphincsSecurity.Concrete.OtsProbeSimulation
