import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeChargedRootAdaptiveRisk
import SphincsSecurity.Proof.OtsProbeChargedRootSelection
import SphincsSecurity.Proof.OtsProbeKnownRootTraceSource
import SphincsSecurity.Proof.OtsProbeNativeHashHistorySelection
import SphincsSecurity.Proof.OtsProbeNativeQueryTraceProjection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem nativeTrace_finalCore
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache)) (history : List CanonicalQuerySelection)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (htrace : (some result, history) ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    result.table = table ∧ result.context.ValuesConsistent ∧ DeferredCompletable table result.context := by
  have hm : some result ∈ support (Prod.fst <$>
      runNativeQueryTrace parameter root ftsSecret computation context fuel table cache) := by
    rw [support_map]
    exact ⟨(some result, history), htrace, rfl⟩
  rw [mem_support_iff_of_evalDist_eq (runNativeQueryTrace_result_projection parameter root ftsSecret computation context fuel table cache
    hconsistent hstarts)] at hm
  rw [support_map] at hm
  obtain ⟨raw, hraw, hretain⟩ := hm
  cases raw with
  | none => simp [retainCompletableResult] at hretain
  | some raw =>
      simp only [retainCompletableResult] at hretain
      split_ifs at hretain with hcomplete
      · have heq := Option.some.inj hretain
        subst result
        have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table raw hconsistent hstarts hraw
        exact ⟨hcore.1, hcore.2.1, by simpa only [hcore.1] using hcomplete⟩

def NativeRootHistorySelectionHit (parameter : PublicParameter) (target : Position)
    (selected : Option (List CanonicalQuerySelection × CanonicalQuerySelection)) : Prop :=
  ∃ prior selection output, selected = some (prior, selection) ∧
    selection.context.positionValue target = some output ∧ .position target ∉ selection.context.state.revealed ∧
    truncateHash output ∉ nativeRootCandidateHistory parameter target prior ∧
    chargedNativeRootQueryCandidate parameter target selection.input selection.context = some (truncateHash output)

theorem nativeTraceHashCutHistory_hit_finishes_false
    (parameter : PublicParameter) (root : Digest) (target : Position) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) (OuterQueryCut α))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (trace : Option (ResolvedRunResult (OuterQueryCut α × SplitHashCache)) × List CanonicalQuerySelection)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (htrace : trace ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache))
    (hhit : NativeRootHistorySelectionHit parameter target (nativeTraceHashCutHistory trace)) :
    finishNativeRootHistoryTrace parameter target table
      (observeChargedRootCut parameter target (fun pair => pair.2 = some (truncateHash pair.1))) ∅ trace = pure false := by
  rcases trace with ⟨option, history⟩
  cases option with
  | none => simp [NativeRootHistorySelectionHit, nativeTraceHashCutHistory] at hhit
  | some result =>
      obtain ⟨prior, selection, output, hselected, hknown, hhidden, hprior, hcandidate⟩ := hhit
      cases hinput : result.value.1.input? with
      | none => simp [nativeTraceHashCutHistory, hinput] at hselected
      | some input =>
          simp only [nativeTraceHashCutHistory, hinput, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hselected
          obtain ⟨rfl, rfl⟩ := hselected
          have hfacts := nativeTrace_finalCore parameter root ftsSecret computation context fuel table cache result history
            hconsistent hstarts htrace
          have hcut : chargedNativeRootCutCandidate parameter target result.context result.value.1 = some (truncateHash output) := by
            rw [chargedNativeRootCutCandidate_eq_query, hinput, Option.bind_some]
            exact hcandidate
          rw [finishNativeRootHistoryTrace, privateResolutionObserve_chargedRootCut_of_known parameter target table _ _
            result.context result.remaining result.value hfacts.2.1 hfacts.2.2 output hknown,
            observeChargedRootCut_of_known parameter target _ _ _ _ _ output hknown]
          simp only [nativeRootCandidateHistory_hashHistory] at hprior
          simp [hhidden, hcut, hprior]

theorem probEvent_nativeHistorySelectionHit_le_originalChargedRootCut
    (parameter : PublicParameter) (root : Digest) (target : Position) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    Pr[fun trace => NativeRootHistorySelectionHit parameter target (nativeHashHistorySelection trace.2 ordinal) |
      runNativeQueryTrace parameter root ftsSecret computation context fuel table cache] ≤
    Pr[fun b => b = false | originalChargedRootCutObservation parameter root target ftsSecret computation
      context fuel table cache ∅ ordinal (fun pair => pair.2 = some (truncateHash pair.1))] := by
  have hdist := runNativeQueryTrace_hashHistory_projection parameter root ftsSecret computation ordinal context fuel table cache
  have hprob := probEvent_congr' (fun _ _ => Iff.rfl) hdist (p := NativeRootHistorySelectionHit parameter target)
  simp only [probEvent_map, Function.comp_def] at hprob
  rw [hprob, originalChargedRootCutObservation, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro trace
  by_cases htrace : trace ∈ support (runNativeQueryTrace parameter root ftsSecret (outerHashQueryCutAt computation ordinal) context fuel table cache)
  · by_cases hhit : NativeRootHistorySelectionHit parameter target (nativeTraceHashCutHistory trace)
    · rw [if_pos hhit, nativeTraceHashCutHistory_hit_finishes_false parameter root target ftsSecret _ context fuel table cache trace
        hconsistent hstarts htrace hhit]
      simp
    · simp [hhit]
  · simp [probOutput_eq_zero_of_not_mem_support htrace]

def NativeFinalRootHistoryMatch (parameter : PublicParameter) (target : Position)
    (trace : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection) : Prop :=
  ∃ result output, trace.1 = some result ∧ result.context.positionValue target = some output ∧
    .position target ∉ result.context.state.revealed ∧
    truncateHash output ∈ nativeRootCandidateHistory parameter target trace.2 ∧
    ¬UnknownSourceFinalRootMatch parameter trace

end SphincsSecurity.Concrete.OtsProbeSimulation
