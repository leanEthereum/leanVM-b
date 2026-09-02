import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveAfterRoot
import SphincsSecurity.Proof.OtsProbeResolvedPrivateRetainedCommutation

/-!
# Adaptive selected-root normalization

The selected-root computation resolves its target only when the chosen candidate is reached. This
module moves that same resolution to the start of the deferred prefix. The post-selection suffix is
already handled by the adaptive selected-root bridge, so the normalization stops at that boundary.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

noncomputable def eagerDirectDelayedSelectedRootIndicator
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) : ProbComp Bool :=
  if ordinal < snapshots.length then
    directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
      computation snapshots observations context fuel cache
  else do
    let resolved ← resolveDeferredPositionValue target context
    match resolved with
    | none => pure false
    | some resolved =>
        directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
          computation snapshots observations resolved.toDeferredContext fuel cache

set_option maxRecDepth 100000 in
theorem evalDist_eagerDirectDelayedSelectedRootIndicator_eq_of_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hselected : ordinal < snapshots.length) :
    evalDist
        (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot computation snapshots observations context fuel cache) =
      evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot computation snapshots observations context fuel cache) := by
  simp [eagerDirectDelayedSelectedRootIndicator, hselected]

theorem evalDist_eagerDirectDelayedSelectedRootIndicator_pure_eq
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (value : α) (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hselected : ¬ordinal < snapshots.length) :
    evalDist
        (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot (pure value) snapshots observations context fuel cache) =
      evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot (pure value) snapshots observations context fuel cache) := by
  simp only [eagerDirectDelayedSelectedRootIndicator, hselected, ↓reduceIte,
    directDelayedSelectedRootIndicator, OracleComp.construct_pure, ↓reduceDIte]
  calc
    _ = evalDist
        (resolveDeferredPositionValue target context >>= fun _ ↦
          (pure false : ProbComp Bool)) := by
      apply evalDist_bind_congr
      intro resolved _hresolved
      cases resolved <;> rfl
    _ = evalDist (pure false : ProbComp Bool) :=
      OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (resolveDeferredPositionValue target context)
        (by simp [resolveDeferredPositionValue, LazyRevealProbe.sampleHashOutput])
        (pure false)

theorem evalDist_eagerDirectDelayedSelectedRootIndicator_of_resolved
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (resolved : DeferredResolution)
    (fuel : Nat) (cache : SplitHashCache)
    (hresolved : some resolved ∈ support
      (resolveDeferredPositionValue target context)) :
    evalDist
        (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot computation snapshots observations resolved.toDeferredContext fuel cache) =
      evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot computation snapshots observations resolved.toDeferredContext fuel cache) := by
  by_cases hselected : ordinal < snapshots.length
  · exact evalDist_eagerDirectDelayedSelectedRootIndicator_eq_of_selected ordinal parameter
      root ftsSecret table target rightRoot computation snapshots observations
      resolved.toDeferredContext fuel cache hselected
  · unfold eagerDirectDelayedSelectedRootIndicator
    simp only [hselected, ↓reduceIte]
    rw [resolveDeferredPositionValue_of_resolved target context resolved hresolved]
    rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
