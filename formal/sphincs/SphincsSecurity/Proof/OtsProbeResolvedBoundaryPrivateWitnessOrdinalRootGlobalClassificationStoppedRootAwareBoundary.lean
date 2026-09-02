import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAwareProbability

/-!
# Root-aware selector boundary

The fixed-context root-aware swap bound is lifted through the public top-root computation and the independent high half of the selected layer-root output.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] materializedRootAwareAvoidingOrdinalSelection
  materializedActualRootAwareAvoidingOrdinalSelection
set_option linter.constructorNameAsVariable false

theorem probEvent_uniformActualRoot_materializedRootAwareRootInstalledMatches_le_mul
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (output : Digest → HashOutput)
    (htruncate : ∀ root, truncateHash (output root) = root)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext)
    (hhidden : context.state.values (.position target) = none)
    (hprivate : Coordinate.position target ∉ context.state.revealed)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (baseCache : SplitHashCache)
    (hbase : ∀ leftRoot rightRoot,
      swapCanonicalRootEncodingCache parameter target leftRoot rightRoot baseCache = baseCache) :
    let rootContext := fun root =>
      { context with values := context.values.install target (output root) }
    Pr[fun result : Digest × Digest × Option Probe =>
        materializedOrdinalSelectionMatches target result.1 result.2.2 | do
      let leftRoot ← ($ᵗ Digest : ProbComp Digest)
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      let selection ← materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter
        publicRoot target leftRoot rightRoot ftsSecret computation candidates
        (materializedDeferredState (rootContext leftRoot)) fuel table
        (rootInstalledCache target output baseCache leftRoot)
      pure (leftRoot, rightRoot, selection)] ≤
      Pr[fun result : Digest × Option Probe =>
          materializedOrdinalSelectionAt target result.2 | do
        let leftRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter
          publicRoot target leftRoot leftRoot ftsSecret computation candidates
          (materializedDeferredState (rootContext leftRoot)) fuel table
          (rootInstalledCache target output baseCache leftRoot)
        pure (leftRoot, selection)] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply probEvent_uniformActualRoot_materializedRootAwareSelectionFamilyMatches_le_mul ordinal
    parameter publicRoot target hroot output htruncate ftsSecret computation candidates context
    hhidden hprivate fuel table (rootInstalledCache target output baseCache)
  · exact rootInstalledCache_target target output baseCache
  · intro leftRoot rightRoot
    exact fullSwapRootCache_rootInstalledCache parameter target output baseCache leftRoot rightRoot
      (hbase leftRoot rightRoot)

end SphincsSecurity.Concrete.OtsProbeSimulation

