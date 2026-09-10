import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeChargedRootAdaptiveRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_originalChargedRootCutObservation_occurrence_le_trace
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (ordinal : Nat) :
    Pr[fun b => b = false | originalChargedRootCutObservation parameter root target ftsSecret computation
      context fuel table cache initialHistory ordinal (fun pair => pair.2 ≠ none)] ≤
    Pr[fun trace => chargedNativeRootTraceCutCandidate parameter target trace.1 ≠ none |
      runNativeQueryTrace parameter root ftsSecret (outerHashQueryCutAt computation ordinal) context fuel table cache] := by
  unfold originalChargedRootCutObservation
  apply probEvent_bind_le_probEvent
  rintro ⟨option, history⟩ _ hmiss
  cases option with
  | none => simp [finishNativeRootHistoryTrace]
  | some result =>
      have hnone : chargedNativeRootCutCandidate parameter target result.context result.value.1 = none := by
        simpa only [chargedNativeRootTraceCutCandidate, not_not] using hmiss
      unfold finishNativeRootHistoryTrace privateResolutionObserve
      rw [probEvent_bind_eq_tsum]
      apply ENNReal.tsum_eq_zero.mpr
      intro resolved
      by_cases hresolved : resolved ∈ support (resolveDeferredPositionValue target result.context)
      · cases resolved with
        | none => simp
        | some resolved =>
            by_cases hcomplete : DeferredCompletable table resolved.toDeferredContext
            · simp [hcomplete, observeChargedRootCut,
                chargedNativeRootCutCandidate_resolvePositionValue parameter target target result.context result.value.1 resolved hresolved, hnone]
            · simp [hcomplete]
      · simp [probOutput_eq_zero_of_not_mem_support hresolved]

theorem probEvent_originalChargedRootCutObservation_hit_le_trace_occurrence
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hpending : context.state.pendingAt (.position target) ⊆ initialHistory)
    (hcache : ∀ digest, digest ∉ initialHistory → NoEncodingRootGuessCached parameter target digest cache)
    (ordinal : Nat) (hbudget : initialHistory.card + ordinal ≤ 2 ^ 126) :
    Pr[fun b => b = false | originalChargedRootCutObservation parameter root target ftsSecret computation
      context fuel table cache initialHistory ordinal (fun pair => pair.2 = some (truncateHash pair.1))] ≤
    Pr[fun trace => chargedNativeRootTraceCutCandidate parameter target trace.1 ≠ none |
      runNativeQueryTrace parameter root ftsSecret (outerHashQueryCutAt computation ordinal) context fuel table cache] *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :=
  (probEvent_originalChargedRootCutObservation_hit_le_occurrence parameter root target hroot ftsSecret computation
    context fuel table cache initialHistory hvalid hcomplete hensured hstate hvalue hpending hcache ordinal hbudget).trans
      (mul_le_mul_left (probEvent_originalChargedRootCutObservation_occurrence_le_trace parameter root target ftsSecret computation
        context fuel table cache initialHistory ordinal) _)

end SphincsSecurity.Concrete.OtsProbeSimulation
