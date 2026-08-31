import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionWeaken

/-!
# Root-indexed materialized selection family

A family of deferred contexts and split caches that is covariant under the complete root swap
instantiates the generic two-root one-guess theorem.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

set_option maxRecDepth 100000 in
theorem evalDist_materializedActualRootAvoidingOrdinalSelection_family_swap
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
    (cache : Digest → SplitHashCache)
    (htargetCache : ∀ root,
      cache root (.hidden (.position target)) = some (output root))
    (hcacheSwap : ∀ leftRoot rightRoot,
      fullSwapRootCache parameter target leftRoot rightRoot (output rightRoot)
        (cache leftRoot) = cache rightRoot)
    (leftRoot rightRoot : Digest) :
    let rootContext := fun root =>
      { context with values := context.values.install target (output root) }
    evalDist
        (materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target
          leftRoot rightRoot ftsSecret computation candidates
          (materializedDeferredState (rootContext leftRoot)) fuel table (cache leftRoot)) =
      evalDist
        (materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target
          rightRoot leftRoot ftsSecret computation candidates
          (materializedDeferredState (rootContext rightRoot)) fuel table (cache rightRoot)) := by
  dsimp only
  have hswap := evalDist_materializedRootAvoidingOrdinalSelection_fullSwap ordinal parameter
    publicRoot target hroot (output leftRoot) (output rightRoot) ftsSecret computation candidates
    context hhidden hprivate fuel table (cache leftRoot) (htargetCache leftRoot)
  rw [htruncate leftRoot, htruncate rightRoot] at hswap
  simpa only [hcacheSwap leftRoot rightRoot] using hswap

set_option maxRecDepth 100000 in
theorem probEvent_uniformActualRoot_materializedSelectionFamilyMatches_le
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
    (cache : Digest → SplitHashCache)
    (htargetCache : ∀ root,
      cache root (.hidden (.position target)) = some (output root))
    (hcacheSwap : ∀ leftRoot rightRoot,
      fullSwapRootCache parameter target leftRoot rightRoot (output rightRoot)
        (cache leftRoot) = cache rightRoot) :
    let rootContext := fun root =>
      { context with values := context.values.install target (output root) }
    Pr[fun result : Digest × Digest × Option Probe =>
        materializedOrdinalSelectionMatches target result.1 result.2.2 | do
      let leftRoot ← ($ᵗ Digest : ProbComp Digest)
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      let selection ← materializedActualRootAvoidingOrdinalSelection ordinal parameter
        publicRoot target leftRoot rightRoot ftsSecret computation candidates
        (materializedDeferredState (rootContext leftRoot)) fuel table (cache leftRoot)
      pure (leftRoot, rightRoot, selection)] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  dsimp only
  apply probEvent_uniformActualRoot_materializedActualSelectionMatches_le ordinal parameter
    publicRoot target ftsSecret computation candidates
    (fun root => materializedDeferredState
      { context with values := context.values.install target (output root) })
    fuel table cache
  intro leftRoot rightRoot
  exact evalDist_materializedActualRootAvoidingOrdinalSelection_family_swap ordinal parameter
    publicRoot target hroot output htruncate ftsSecret computation candidates context hhidden
    hprivate fuel table cache htargetCache hcacheSwap leftRoot rightRoot

set_option maxRecDepth 100000 in
theorem probEvent_uniformActualRoot_materializedSelectionFamilyMatches_le_mul
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
    (cache : Digest → SplitHashCache)
    (htargetCache : ∀ root,
      cache root (.hidden (.position target)) = some (output root))
    (hcacheSwap : ∀ leftRoot rightRoot,
      fullSwapRootCache parameter target leftRoot rightRoot (output rightRoot)
        (cache leftRoot) = cache rightRoot) :
    let rootContext := fun root =>
      { context with values := context.values.install target (output root) }
    Pr[fun result : Digest × Digest × Option Probe =>
        materializedOrdinalSelectionMatches target result.1 result.2.2 | do
      let leftRoot ← ($ᵗ Digest : ProbComp Digest)
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      let selection ← materializedActualRootAvoidingOrdinalSelection ordinal parameter
        publicRoot target leftRoot rightRoot ftsSecret computation candidates
        (materializedDeferredState (rootContext leftRoot)) fuel table (cache leftRoot)
      pure (leftRoot, rightRoot, selection)] ≤
      Pr[fun result : Digest × Option Probe =>
          materializedOrdinalSelectionAt target result.2 | do
        let leftRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← materializedActualRootAvoidingOrdinalSelection ordinal parameter
          publicRoot target leftRoot leftRoot ftsSecret computation candidates
          (materializedDeferredState (rootContext leftRoot)) fuel table (cache leftRoot)
        pure (leftRoot, selection)] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  dsimp only
  let run : Digest → Digest → ProbComp (Option Probe) :=
    fun leftRoot rightRoot =>
      materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target leftRoot
        rightRoot ftsSecret computation candidates
        (materializedDeferredState
          { context with values := context.values.install target (output leftRoot) })
        fuel table (cache leftRoot)
  let reference : Digest → ProbComp (Option Probe) :=
    fun leftRoot =>
      materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target leftRoot
        leftRoot ftsSecret computation candidates
        (materializedDeferredState
          { context with values := context.values.install target (output leftRoot) })
        fuel table (cache leftRoot)
  apply probEvent_uniformActualRoot_match_le_of_swap_of_comparison_mul target run reference
  · intro leftRoot rightRoot
    exact evalDist_materializedActualRootAvoidingOrdinalSelection_family_swap ordinal parameter
      publicRoot target hroot output htruncate ftsSecret computation candidates context hhidden
      hprivate fuel table cache htargetCache hcacheSwap leftRoot rightRoot
  · intro leftRoot
    exact probEvent_sampledComparisonRoot_materializedSelectionMatches_le_mul ordinal parameter
      target leftRoot (maskedSign parameter publicRoot ftsSecret) computation candidates
      (materializedDeferredState
        { context with values := context.values.install target (output leftRoot) })
      fuel table (cache leftRoot)

end SphincsSecurity.Concrete.OtsProbeSimulation
