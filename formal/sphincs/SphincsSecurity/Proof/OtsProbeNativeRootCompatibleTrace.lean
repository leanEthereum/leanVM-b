import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootTraceSafety

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open _root_.OracleComp.DeferredSampling

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def insertNativeRootGuess (guess : Option Digest) (history : Finset Digest) : Finset Digest :=
  match guess with
  | none => history
  | some guess => insert guess history

theorem nativeRootCandidateHistory_cons
    (parameter : PublicParameter) (target : Position) (selection : CanonicalQuerySelection) (history : List CanonicalQuerySelection) :
    nativeRootCandidateHistory parameter target (selection :: history) =
      insertNativeRootGuess (nativeRootSelectionGuess? parameter target selection) (nativeRootCandidateHistory parameter target history) := by
  cases hinput : selection.input with
  | inl query =>
      cases query with
      | inl n => simp [nativeRootCandidateHistory, nativeHashQueryHistory, IsOuterHash, hinput,
          nativeRootSelectionGuess?, nativeRootSelectionCandidate?, insertNativeRootGuess]
      | inr input =>
          cases hguess : nativeRootSelectionGuess? parameter target selection <;>
            simp [nativeRootCandidateHistory, nativeHashQueryHistory, IsOuterHash, hinput, hguess, insertNativeRootGuess]
  | inr message => simp [nativeRootCandidateHistory, nativeHashQueryHistory, IsOuterHash, hinput,
      nativeRootSelectionGuess?, nativeRootSelectionCandidate?, insertNativeRootGuess]

noncomputable def observeCompatibleNativeRootTrace
    (parameter : PublicParameter) (target : Position) (before after : HashOutput)
    (trace : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection) :
    Option (ResolvedRunResult α × Finset Digest) :=
  if NativeRootTraceCompatible parameter target before after trace then
    (normalizeNativeRootResult target trace.1).map fun result => (result, nativeRootCandidateHistory parameter target trace.2)
  else none

noncomputable def prependCompatibleNativeRootGuess (before after : HashOutput) (guess : Option Digest) :
    Option (ResolvedRunResult α × Finset Digest) → Option (ResolvedRunResult α × Finset Digest)
  | none => none
  | some (result, history) =>
      if truncateHash before ∉ insertNativeRootGuess guess history ∧ truncateHash after ∉ insertNativeRootGuess guess history then
        some (result, insertNativeRootGuess guess history)
      else none

theorem observeCompatibleNativeRootTrace_prepend
    (parameter : PublicParameter) (target : Position) (before after : HashOutput)
    (selection : CanonicalQuerySelection)
    (trace : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection) :
    observeCompatibleNativeRootTrace parameter target before after (trace.1, selection :: trace.2) =
      prependCompatibleNativeRootGuess before after (nativeRootSelectionGuess? parameter target selection)
        (observeCompatibleNativeRootTrace parameter target before after trace) := by
  rcases trace with ⟨option, history⟩
  cases option with
  | none => simp [observeCompatibleNativeRootTrace, NativeRootTraceCompatible, prependCompatibleNativeRootGuess]
  | some result =>
      cases hguess : nativeRootSelectionGuess? parameter target selection <;>
        by_cases hhidden : .position target ∉ result.context.state.revealed <;>
        by_cases hbefore : truncateHash before ∈ nativeRootCandidateHistory parameter target history <;>
        by_cases hafter : truncateHash after ∈ nativeRootCandidateHistory parameter target history <;>
        simp [observeCompatibleNativeRootTrace, NativeRootTraceCompatible, nativeRootCandidateHistory_cons,
          prependCompatibleNativeRootGuess, insertNativeRootGuess, hguess, hhidden, hbefore, hafter,
          normalizeNativeRootResult]

theorem observeCompatibleNativeRootTrace_eq_none_of_not_compatible
    (parameter : PublicParameter) (target : Position) (before after : HashOutput)
    (trace : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (h : ¬NativeRootTraceCompatible parameter target before after trace) :
    observeCompatibleNativeRootTrace parameter target before after trace = none := by
  simp [observeCompatibleNativeRootTrace, h]

theorem evalDist_observeCompatibleNativeRootTrace_eq_none_of_unsafe
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (before after : HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (h : NativePositionReplaceable target before after context)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hunsafe : ¬NativeRootOuterSafe parameter target before after input context) :
    evalDist (observeCompatibleNativeRootTrace parameter target before after <$>
      runNativeQueryTrace parameter root ftsSecret (OracleSpec.query input >>= next) context fuel table cache) =
      evalDist (pure none : ProbComp (Option (ResolvedRunResult α × Finset Digest))) := by
  have hzero := probEvent_nativeRootTraceCompatible_eq_zero_of_unsafe parameter root target hroot before after ftsSecret
    input next context h fuel table cache hunsafe
  have hnot := probEvent_eq_zero_iff.mp hzero
  rw [map_eq_bind_pure_comp]
  calc
    _ = evalDist (runNativeQueryTrace parameter root ftsSecret (OracleSpec.query input >>= next) context fuel table cache >>=
        fun _ => pure none) := by
      apply evalDist_bind_congr
      intro trace htrace
      rw [Function.comp_apply, observeCompatibleNativeRootTrace_eq_none_of_not_compatible parameter target before after trace (hnot trace htrace)]
    _ = _ := evalDist_bind_const_neverFails _ (by simp [runNativeQueryTrace]) _

theorem NativeRootContextRel.symm
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) :
    NativeRootContextRel target after before right left := by
  rw [h.right_eq]
  exact ⟨h.replaceable.reverse, (replaceNativePosition_inverse h.replaceable).symm⟩

theorem nativeRootActionSafe_symm
    (parameter : PublicParameter) (target : Position) (input : HashInput)
    (left right : DeferredContext) (action : PlannedHashAction) :
    NativeRootActionSafe parameter target input left right action ↔
      NativeRootActionSafe parameter target input right left action := by
  cases action with
  | ordinary => rfl
  | resolve coordinate => simp only [NativeRootActionSafe, eq_comm, and_comm]

theorem NativeRootContextRel.hashSafe_swap_iff
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) (parameter : PublicParameter) (input : HashInput) :
    NativeRootHashSafe parameter target before after input left ↔ NativeRootHashSafe parameter target after before input right := by
  have hreverse := h.symm
  simp only [NativeRootHashSafe, h.replaceable.replace_self, hreverse.replaceable.replace_self,
    ← h.right_eq, ← hreverse.right_eq]
  rw [← purePlanProbingHashQuery_eq_of_nativeRootContextRel h]
  have hprobe (candidate : Probe) :
      IsPrivateValueExposure target before after (.probe candidate.coordinate candidate.candidate) ↔
        IsPrivateValueExposure target after before (.probe candidate.coordinate candidate.candidate) := by
    simp only [IsPrivateValueExposure, or_comm]
  have haction := nativeRootActionSafe_symm parameter target input left right
    (purePlanProbingHashQuery parameter input left.state).action
  constructor
  · rintro ⟨hencoding, hprobes, hsafe⟩
    exact ⟨⟨hencoding.2, hencoding.1⟩,
      fun candidate hcandidate hexposure => hprobes candidate hcandidate ((hprobe candidate).mpr hexposure), haction.mp hsafe⟩
  · rintro ⟨hencoding, hprobes, hsafe⟩
    exact ⟨⟨hencoding.2, hencoding.1⟩,
      fun candidate hcandidate hexposure => hprobes candidate hcandidate ((hprobe candidate).mp hexposure), haction.mpr hsafe⟩

theorem NativeRootContextRel.outerSafe_swap_iff
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) :
    NativeRootOuterSafe parameter target before after input left ↔ NativeRootOuterSafe parameter target after before input right := by
  cases input with
  | inl query =>
      cases query with
      | inl n => rfl
      | inr input => exact h.hashSafe_swap_iff parameter input
  | inr message => rfl

theorem observeCompatibleNativeRootTrace_swap
    (parameter : PublicParameter) (target : Position) (before after : HashOutput)
    (trace : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection) :
    observeCompatibleNativeRootTrace parameter target before after trace = observeCompatibleNativeRootTrace parameter target after before trace := by
  have heq : NativeRootTraceCompatible parameter target before after trace ↔ NativeRootTraceCompatible parameter target after before trace := by
    rcases trace with ⟨option, history⟩
    cases option <;> simp only [NativeRootTraceCompatible, and_comm]
  simp only [observeCompatibleNativeRootTrace, heq]

end SphincsSecurity.Concrete.OtsProbeSimulation
