import SphincsSecurity.Proof.OtsProbeNativeStoredRootCutRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def clearNativeRootPending (target : Position) (context : DeferredContext) : DeferredContext :=
  { context with state := context.state.clearPending (.position target) }

theorem replaceNativePosition_clearPending_eq_completePrivatePosition
    (target : Position) (output : HashOutput) (context : DeferredContext)
    (hstate : context.state.values (.position target) = none) :
    replaceNativePosition target output (clearNativeRootPending target context) =
      (completePrivatePosition target context output).toDeferredContext := by
  rw [replaceNativePosition_of_private target output (clearNativeRootPending target context) hstate]
  rfl

noncomputable def runResolvedNativeRootCut
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (ordinal : Nat) : ProbComp (HashOutput × Option Digest) := do
  let resolved ← resolveDeferredPositionValue target context
  match resolved with
  | none => pure (0, none)
  | some resolved =>
      if truncateHash resolved.output ∈ initialHistory then pure (resolved.output, none) else
        let trace ← runNativeQueryTrace parameter root ftsSecret (outerHashQueryCutAt computation ordinal)
          resolved.toDeferredContext fuel table cache
        pure (resolved.output, if NativeRootTraceCompatible parameter target resolved.output resolved.output trace then
          nativeRootTraceCutCandidate parameter target trace.1 else none)

theorem probEvent_runResolvedNativeRootCut_eq_sampled
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (ordinal : Nat)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hpending : context.state.pendingAt (.position target) ⊆ initialHistory)
    (event : HashOutput × Option Digest → Prop) (hnone : ∀ output, ¬event (output, none)) :
    Pr[event | runResolvedNativeRootCut parameter root target ftsSecret computation context fuel table cache initialHistory ordinal] =
      Pr[event | sampleNativeStoredRootCut parameter root target ftsSecret computation
        (clearNativeRootPending target context) fuel table cache initialHistory ordinal] := by
  simp only [runResolvedNativeRootCut, resolveDeferredPositionValue, hstate, hvalue, bind_assoc, sampleNativeStoredRootCut]
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro output
  congr 1
  by_cases hhit : context.state.hitAt (.position target) output
  · have hinitial := hpending hhit
    simp [hhit, hinitial, probEvent_pure, hnone]
  · simp only [hhit, ↓reduceIte, pure_bind]
    by_cases hinitial : truncateHash output ∈ initialHistory
    · simp [hinitial]
    · simp only [hinitial, ↓reduceIte]
      rw [replaceNativePosition_clearPending_eq_completePrivatePosition target output context hstate]
      rfl

theorem probEvent_runResolvedNativeRootCut_hit_le_occurrence
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (hconsistent : context.ValuesConsistent)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hpending : context.state.pendingAt (.position target) ⊆ initialHistory)
    (hcache : ∀ digest, digest ∉ initialHistory → NoEncodingRootGuessCached parameter target digest cache)
    (ordinal : Nat) (hbudget : initialHistory.card + ordinal ≤ 2 ^ 126) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) |
      runResolvedNativeRootCut parameter root target ftsSecret computation context fuel table cache initialHistory ordinal] ≤
    Pr[fun pair => pair.2 ≠ none |
      runResolvedNativeRootCut parameter root target ftsSecret computation context fuel table cache initialHistory ordinal] *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  rw [probEvent_runResolvedNativeRootCut_eq_sampled parameter root target ftsSecret computation context fuel table cache initialHistory ordinal
    hstate hvalue hpending _ (by simp),
    probEvent_runResolvedNativeRootCut_eq_sampled parameter root target ftsSecret computation context fuel table cache initialHistory ordinal
      hstate hvalue hpending _ (by simp)]
  apply probEvent_sampleNativeStoredRootCut_hit_le_occurrence parameter root target hroot ftsSecret computation
    (clearNativeRootPending target context) fuel table cache initialHistory hconsistent _ hcache ordinal hbudget
  intro digest hmem
  exact False.elim (not_hitAt_clearPending_self context.state (.position target) (hashOutputOfDigest digest)
    (by simpa only [clearNativeRootPending, LazyRevealProbe.State.hitAt, truncateHash_hashOutputOfDigest] using hmem))

end SphincsSecurity.Concrete.OtsProbeSimulation
