import SphincsSecurity.Proof.OtsProbeNativeStoredRootRisk
import SphincsSecurity.Proof.OtsProbeNativeRootCandidateNormalization
import SphincsSecurity.Proof.OuterHashQueryCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeRootCutCandidate (parameter : PublicParameter) (target : Position)
    (context : DeferredContext) (cut : OuterQueryCut α) : Option Digest := do
  let input ← cut.input?
  match input with
  | .inl (.inr input) =>
      let candidate ← nativeRootCandidate? parameter input context
      if candidate.coordinate = .position target then some candidate.candidate else none
  | _ => none

theorem nativeRootCutCandidate_replaceNativePosition
    (parameter : PublicParameter) (target : Position) (output : HashOutput) (context : DeferredContext) (cut : OuterQueryCut α) :
    nativeRootCutCandidate parameter target context cut =
      nativeRootCutCandidate parameter target (replaceNativePosition target output context) cut := by
  unfold nativeRootCutCandidate
  apply congrArg (fun next => cut.input?.bind next)
  funext input
  cases input with
  | inl query =>
      cases query with
      | inl n => rfl
      | inr input =>
          simp only
          rw [nativeRootCandidate_replaceNativePosition parameter target output context input]
  | inr message => rfl

noncomputable def nativeRootTraceCutCandidate (parameter : PublicParameter) (target : Position) :
    Option (ResolvedRunResult (OuterQueryCut α × SplitHashCache)) → Option Digest
  | none => none
  | some result => nativeRootCutCandidate parameter target result.context result.value.1

noncomputable def nativeStoredRootRecordCutCandidate (parameter : PublicParameter) (target : Position)
    (record : ResolvedRunResult (OuterQueryCut α) × Finset Digest) : Option Digest :=
  nativeRootCutCandidate parameter target record.1.context record.1.value

theorem nativeStoredRootRecordCutCandidate_observe
    (parameter : PublicParameter) (target : Position) (before after : HashOutput)
    (trace : Option (ResolvedRunResult (OuterQueryCut α × SplitHashCache)) × List CanonicalQuerySelection) :
    (observeCompatibleNativeRootTrace parameter target before after trace).bind (nativeStoredRootRecordCutCandidate parameter target) =
      if NativeRootTraceCompatible parameter target before after trace then nativeRootTraceCutCandidate parameter target trace.1 else none := by
  unfold observeCompatibleNativeRootTrace
  split_ifs with hcompatible
  · rcases trace with ⟨option, history⟩
    cases option with
    | none => contradiction
    | some result =>
        simp only [normalizeNativeRootResult, Option.map_some, Option.bind_some, nativeStoredRootRecordCutCandidate,
          nativeRootTraceCutCandidate]
        exact (nativeRootCutCandidate_replaceNativePosition parameter target 0 result.context result.value.1).symm
  · rfl

noncomputable def sampleNativeStoredRootCut
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (ordinal : Nat) : ProbComp (HashOutput × Option Digest) := do
  let output ← LazyRevealProbe.sampleHashOutput
  if truncateHash output ∈ initialHistory then pure (output, none) else
    let trace ← runNativeQueryTrace parameter root ftsSecret (outerHashQueryCutAt computation ordinal)
      (replaceNativePosition target output context) fuel table cache
    pure (output, if NativeRootTraceCompatible parameter target output output trace then
      nativeRootTraceCutCandidate parameter target trace.1 else none)

theorem sampleNativeStoredRootCut_eq_records
    (parameter : PublicParameter) (root : Digest) (target : Position)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (ordinal : Nat) :
    sampleNativeStoredRootCut parameter root target ftsSecret computation context fuel table cache initialHistory ordinal =
      samplePrivateHistoryGuess
        (runNativeStoredRootRecords parameter root target ftsSecret (outerHashQueryCutAt computation ordinal)
          context fuel table cache initialHistory) (nativeStoredRootRecordCutCandidate parameter target) := by
  unfold sampleNativeStoredRootCut samplePrivateHistoryGuess
  apply bind_congr
  intro output
  unfold runNativeStoredRootRecords
  by_cases hinitial : truncateHash output ∈ initialHistory
  · simp [hinitial]
  · simp only [hinitial, ↓reduceIte, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
      nativeStoredRootRecordCutCandidate_observe]

theorem probEvent_sampleNativeStoredRootCut_hit_le_occurrence
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (hconsistent : context.ValuesConsistent)
    (hpending : context.state.pendingAt (.position target) ⊆ initialHistory)
    (hcache : ∀ digest, digest ∉ initialHistory → NoEncodingRootGuessCached parameter target digest cache)
    (ordinal : Nat) (hbudget : initialHistory.card + ordinal ≤ 2 ^ 126) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) |
      sampleNativeStoredRootCut parameter root target ftsSecret computation context fuel table cache initialHistory ordinal] ≤
    Pr[fun pair => pair.2 ≠ none |
      sampleNativeStoredRootCut parameter root target ftsSecret computation context fuel table cache initialHistory ordinal] *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  rw [sampleNativeStoredRootCut_eq_records]
  exact probEvent_sampleNativeStoredRootRecords_hit_le_occurrence parameter root target hroot ftsSecret
    (outerHashQueryCutAt computation ordinal) context fuel table cache initialHistory hconsistent hpending hcache
    ordinal (outerHashQueryCutAt_hashBound computation ordinal) hbudget _

end SphincsSecurity.Concrete.OtsProbeSimulation
