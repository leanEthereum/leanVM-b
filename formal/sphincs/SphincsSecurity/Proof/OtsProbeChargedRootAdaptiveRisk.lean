import SphincsSecurity.Proof.OtsProbeChargedRootCutRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_finishNativeRootHistoryTrace_charged_of_stored
    (parameter : PublicParameter) (root : Digest) (target : Position) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) (OuterQueryCut α))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (event : HashOutput × Option Digest → Prop) (hnone : ∀ output, ¬event (output, none))
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (output : HashOutput) (hknown : context.positionValue target = some output)
    (trace : Option (ResolvedRunResult (OuterQueryCut α × SplitHashCache)) × List CanonicalQuerySelection)
    (htrace : trace ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    Pr[fun b => b = false | finishNativeRootHistoryTrace parameter target table (observeChargedRootCut parameter target event) initialHistory trace] =
      Pr[event | (pure (output, if truncateHash output ∉ initialHistory ∧ NativeRootTraceCompatible parameter target output output trace then
        chargedNativeRootTraceCutCandidate parameter target trace.1 else none) : ProbComp (HashOutput × Option Digest))] := by
  rcases trace with ⟨option, history⟩
  cases option with
  | none => simp [finishNativeRootHistoryTrace, NativeRootTraceCompatible, probEvent_pure, hnone]
  | some result =>
      rw [finishNativeRootHistoryTrace_charged_of_stored parameter root target ftsSecret computation context fuel table cache initialHistory event
        hconsistent hstarts output hknown result history htrace]
      by_cases hhidden : .position target ∉ result.context.state.revealed <;>
        by_cases hinitial : truncateHash output ∉ initialHistory <;>
        by_cases hhistory : truncateHash output ∉ nativeRootCandidateHistory parameter target history <;>
        by_cases hevent : event (output, chargedNativeRootCutCandidate parameter target result.context result.value.1) <;>
        simp [NativeRootTraceCompatible, chargedNativeRootTraceCutCandidate, probEvent_pure, Finset.mem_union,
          hhidden, hinitial, hhistory, hevent, hnone]

noncomputable def originalChargedRootCutObservation
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (ordinal : Nat) (event : HashOutput × Option Digest → Prop) : ProbComp Bool :=
  runNativeQueryTrace parameter root ftsSecret (outerHashQueryCutAt computation ordinal) context fuel table cache >>=
    finishNativeRootHistoryTrace parameter target table (observeChargedRootCut parameter target event) initialHistory

theorem probEvent_originalChargedRootCutObservation_eq_sampled
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (ordinal : Nat) (event : HashOutput × Option Digest → Prop) (hnone : ∀ output, ¬event (output, none))
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hpending : context.state.pendingAt (.position target) ⊆ initialHistory) :
    Pr[fun b => b = false | originalChargedRootCutObservation parameter root target ftsSecret computation context fuel table cache initialHistory ordinal event] =
      Pr[event | sampleChargedNativeRootCut parameter root target ftsSecret computation
        (clearNativeRootPending target context) fuel table cache initialHistory ordinal] := by
  have hdist := evalDist_nativeHistoryTrace_eq_uniform parameter root target ftsSecret table (observeChargedRootCut parameter target event)
    (outerHashQueryCutAt computation ordinal) context fuel cache initialHistory hvalid hcomplete hensured hstate hvalue
  rw [probEvent_eq_eq_probOutput, originalChargedRootCutObservation, _root_.OracleComp.probOutput_congr rfl hdist,
    ← probEvent_eq_eq_probOutput, sampleChargedNativeRootCut, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro output
  congr 1
  by_cases hhit : context.state.hitAt (.position target) output
  · have hinitial := hpending hhit
    simp [hhit, hinitial, probEvent_pure, hnone]
  · simp only [if_neg hhit]
    have hreplace := replaceNativePosition_clearPending_eq_completePrivatePosition target output context hstate
    rw [hreplace]
    let stored := (completePrivatePosition target context output).toDeferredContext
    change Pr[fun b => b = false | runNativeQueryTrace parameter root ftsSecret (outerHashQueryCutAt computation ordinal) stored fuel table cache >>= _] = _
    have hbase : (clearNativeRootPending target context).ValuesConsistent := hvalid.valuesConsistent
    have hconsistent : stored.ValuesConsistent := by
      change (completePrivatePosition target context output).toDeferredContext.ValuesConsistent
      rw [← hreplace]
      exact hbase.of_replaceNativePosition target output
    have hstarts : StartTableAgrees stored.state table := (show StartTableAgrees context.state table from startTableAgrees_of_deferredCompletable hcomplete)
    have hknown : stored.positionValue target = some output := by
      simp [stored, completePrivatePosition, DeferredContext.positionValue, hstate, DeferredStructuralValues.install]
    by_cases hinitial : truncateHash output ∈ initialHistory
    · rw [if_pos hinitial, probEvent_bind_eq_tsum]
      simp only [probEvent_pure, hnone, ↓reduceIte]
      apply ENNReal.tsum_eq_zero.mpr
      intro trace
      by_cases htrace : trace ∈ support (runNativeQueryTrace parameter root ftsSecret (outerHashQueryCutAt computation ordinal) stored fuel table cache)
      · rw [probEvent_finishNativeRootHistoryTrace_charged_of_stored parameter root target ftsSecret _ stored fuel table cache initialHistory event hnone
          hconsistent hstarts output hknown trace htrace]
        simp [hinitial, probEvent_pure, hnone]
      · dsimp only [stored] at htrace ⊢
        simp only [probOutput_eq_zero_of_not_mem_support htrace, zero_mul]
    · rw [if_neg hinitial, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      apply tsum_congr
      intro trace
      by_cases htrace : trace ∈ support (runNativeQueryTrace parameter root ftsSecret (outerHashQueryCutAt computation ordinal) stored fuel table cache)
      · rw [probEvent_finishNativeRootHistoryTrace_charged_of_stored parameter root target ftsSecret _ stored fuel table cache initialHistory event hnone
          hconsistent hstarts output hknown trace htrace]
        simp only [hinitial, not_false_eq_true, true_and]
        rfl
      · dsimp only [stored] at htrace ⊢
        simp only [probOutput_eq_zero_of_not_mem_support htrace, zero_mul]

theorem probEvent_originalChargedRootCutObservation_hit_le_occurrence
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
    Pr[fun b => b = false | originalChargedRootCutObservation parameter root target ftsSecret computation
      context fuel table cache initialHistory ordinal (fun pair => pair.2 ≠ none)] *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  rw [probEvent_originalChargedRootCutObservation_eq_sampled parameter root target ftsSecret computation
    context fuel table cache initialHistory ordinal _ (by simp) hvalid hcomplete hensured hstate hvalue hpending,
    probEvent_originalChargedRootCutObservation_eq_sampled parameter root target ftsSecret computation
      context fuel table cache initialHistory ordinal _ (by simp) hvalid hcomplete hensured hstate hvalue hpending]
  apply probEvent_sampleChargedNativeRootCut_hit_le_occurrence parameter root target hroot ftsSecret computation
    (clearNativeRootPending target context) fuel table cache initialHistory hvalid.valuesConsistent _ hcache ordinal hbudget
  intro digest hmem
  exact False.elim (not_hitAt_clearPending_self context.state (.position target) (hashOutputOfDigest digest)
    (by simpa only [clearNativeRootPending, LazyRevealProbe.State.hitAt, truncateHash_hashOutputOfDigest] using hmem))

end SphincsSecurity.Concrete.OtsProbeSimulation
