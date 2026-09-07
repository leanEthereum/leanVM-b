import SphincsSecurity.Proof.JointProbeOriginalFailureComparison
import SphincsSecurity.Proof.JointProbeOriginalParentFailure
import SphincsSecurity.Proof.JointProbeResolvedRetained

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

private theorem expected_evalDist_eq (computation : ProbComp α) (cost : α → ENNReal) :
    (∑' value, Pr[= value | evalDist computation] * cost value) =
      ∑' value, Pr[= value | computation] * cost value := rfl

theorem rootFrame_none_iff_jointCompletionFailure
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat)
    (result) (hresult : result ∈ support (sharedRoot otsTable ftsTable q fuel)) :
    rootFrame otsTable q result = none ↔ JointCompletionFailure result := by
  cases result with
  | stopped hit => simp [rootFrame, JointCompletionFailure, cleanJointResolved]
  | done hit state entry =>
      cases hit with
      | true => simp [rootFrame, JointCompletionFailure, cleanJointResolved]
      | false =>
          cases entry with
          | none => simp [rootFrame, JointCompletionFailure, cleanJointResolved]
          | some entry =>
              have hf := resolvedFacts_of_mem_jointDetailed ftsTable _ AdaptiveRevealProbe.State.empty state q
                (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable entry
                (OtsProbeSimulation.ensuredInitialContext_valid ∅).valuesConsistent
                (OtsProbeSimulation.startTableAgrees_of_deferredCompletable (OtsProbeSimulation.ensuredInitialContext_completable ∅ otsTable))
                hresult
              simp [rootFrame, JointCompletionFailure, cleanJointResolved, hf.1]

theorem resumeJointResolved_eq_of_rootFrame
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q : Nat)
    (next : Digest → JointSource α) (frame : Frame) (actual : Digest × QueryCache HashSpec)
    (result) (hrel : JointOriginalRunRel parameter otsTable ftsTable result actual)
    (hframe : rootFrame otsTable q result = some frame) :
    resumeJointResolved ftsTable q next result = AdaptiveRevealProbe.runDetailed ftsTable frame.state frame.ftsFuel
      (runJointResolved ((next actual.1).run frame.cache) frame.context frame.fuel otsTable) := by
  cases result with
  | stopped hit => simp [rootFrame] at hframe
  | done hit state entry =>
      cases hit with
      | true => simp [rootFrame] at hframe
      | false =>
          cases entry with
          | none => simp [rootFrame] at hframe
          | some entry =>
              by_cases hc : OtsProbeSimulation.DeferredCompletable otsTable entry.context
              · simp only [rootFrame, if_pos hc, Option.some.injEq] at hframe
                subst frame
                let projected : ResolvedRunResult (Digest × OtsProbeSimulation.SplitHashCache) :=
                  { entry with value := (entry.value.1,
                    OtsProbeSimulation.replaceOrdinaryCache entry.value.2.1 (mergedCache parameter ftsTable entry.value.2.2)) }
                have hi := hrel.of_completable (entry := projected) rfl
                  (by simp [projectJointResolvedCache, cleanJointResolved, projected]) hc
                change entry.table = otsTable ∧ entry.value.1 = actual.1 ∧ _ at hi
                simp only [resumeJointResolved, hi.1, hi.2.1]
              · simp [rootFrame, hc] at hframe

theorem jointResolvedRetainedDetailed_eq_root_bind
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    jointResolvedRetainedDetailed adversary parameter otsTable ftsTable q fuel =
      sharedRoot otsTable ftsTable q fuel >>= resumeJointResolved ftsTable q
        (fun root => jointSourceComputation parameter root (retainedComputation adversary parameter root q)) :=
  runDetailed_jointResolved_bind_probeFree ftsTable AdaptiveRevealProbe.State.empty q
    (jointSourceNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot)
    (fun root => jointSourceComputation parameter root (retainedComputation adversary parameter root q))
    (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache)
    (runJointResolved_nativeBlock_probeFree _ _ _ _ _)

private theorem probEvent_after_root_le_fullShared
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) (raw) (hr : raw ∈ support (rootCoupling parameter otsTable ftsTable q fuel).1) :
    Pr[fun result => result.2 = true | runWithFailure exception parameter raw.2.1 otsTable ftsTable
      (retainedComputation adversary parameter raw.2.1 q) (rootFrame otsTable q raw.1) raw.2.2 false
      (rootFrame otsTable q raw.1).isNone] ≤
    Pr[JointCompletionFailure | resumeJointResolved ftsTable q
      (fun root => jointSourceComputation parameter root (retainedComputation adversary parameter root q)) raw.1] := by
  let continuation := fun root => jointSourceComputation parameter root (retainedComputation adversary parameter root q)
  have hs := rootCoupling_support parameter otsTable ftsTable q fuel raw hr
  cases hf : rootFrame otsTable q raw.1 with
  | none =>
      have hc := (OtsProbeSimulation.ensuredInitialContext_valid ∅).valuesConsistent
      have ht := OtsProbeSimulation.startTableAgrees_of_deferredCompletable (OtsProbeSimulation.ensuredInitialContext_completable ∅ otsTable)
      rw [probEvent_jointCompletionFailure_resume_eq_one ftsTable (jointSourceNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot)
        continuation AdaptiveRevealProbe.State.empty q q (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable
        (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache) hc ht raw.1 hs.2.1
        ((rootFrame_none_iff_jointCompletionFailure otsTable ftsTable q fuel raw.1 hs.2.1).1 hf)]
      exact probEvent_le_one
  | some frame =>
      rw [resumeJointResolved_eq_of_rootFrame parameter otsTable ftsTable q continuation frame raw.2 raw.1 hs.1 hf]
      have hi : (some frame, raw.2) ∈ support (initializeRoot parameter otsTable ftsTable q fuel) := by
        rw [initializeRoot, support_map]
        exact ⟨raw, hr, by simp [hf]⟩
      have hv := initializeRoot_valid parameter otsTable ftsTable q fuel (some frame, raw.2) hi frame rfl
      apply probEvent_runWithFailure_le_fullShared exception parameter raw.2.1 otsTable ftsTable _ frame raw.2.2 hv.2
      rw [hv.1.1]
      exact retainedComputation_hashBound adversary parameter raw.2.1 q

theorem probEvent_runRetainedWithFailure_le_fullShared
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    Pr[fun result => result.2 = true | runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel] ≤
      Pr[JointCompletionFailure | jointResolvedRetainedDetailed adversary parameter otsTable ftsTable q fuel] := by
  let continuation := fun root => jointSourceComputation parameter root (retainedComputation adversary parameter root q)
  rw [runRetainedWithFailure, probEvent_bind_eq_tsum, initializeRoot, tsum_probOutput_map_mul]
  rw [jointResolvedRetainedDetailed_eq_root_bind, probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' raw, Pr[= raw | (rootCoupling parameter otsTable ftsTable q fuel).1] *
        Pr[JointCompletionFailure | resumeJointResolved ftsTable q continuation raw.1] := by
      apply ENNReal.tsum_le_tsum
      intro raw
      by_cases hr : raw ∈ support (rootCoupling parameter otsTable ftsTable q fuel).1
      · exact mul_le_mul' le_rfl (probEvent_after_root_le_fullShared exception adversary parameter otsTable ftsTable q fuel raw hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = _ := by
      have hm := tsum_probOutput_map_mul (rootCoupling parameter otsTable ftsTable q fuel).1 Prod.fst
        (fun result => Pr[JointCompletionFailure | resumeJointResolved ftsTable q continuation result])
      rw [(rootCoupling parameter otsTable ftsTable q fuel).2.map_fst] at hm
      exact hm.symm.trans (expected_evalDist_eq (sharedRoot otsTable ftsTable q fuel) _)

theorem finishResolvedRun_eq_none_of_jointCompletionFailure
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult α)))
    (hfailed : JointCompletionFailure result) :
    OtsProbeSimulation.finishResolvedRun (cleanJointResolved result) = pure none := by
  cases he : cleanJointResolved result with
  | none => rfl
  | some entry => exact OtsProbeSimulation.finishResolvedRun_of_not_deferredCompletable entry (hfailed entry he)

theorem probEvent_jointCompletionFailure_le_finish
    (computation : ProbComp (AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult α)))) :
    Pr[JointCompletionFailure | computation] ≤
      Pr[fun result => result = none | computation >>= fun result => OtsProbeSimulation.finishResolvedRun (cleanJointResolved result)] := by
  rw [probEvent_eq_tsum_ite, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hf : JointCompletionFailure result
  · rw [if_pos hf, finishResolvedRun_eq_none_of_jointCompletionFailure result hf]
    simp
  · simp [hf]

theorem probEvent_runRetainedWithFailure_le_nativeCompletion
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    Pr[fun result => result.2 = true | runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel] ≤
      Pr[fun result => result = none | nativeFtsRetainedCompletion adversary parameter otsTable ftsTable q fuel] := by
  apply (probEvent_runRetainedWithFailure_le_fullShared exception adversary parameter otsTable ftsTable q fuel).trans
  rw [← jointResolvedRetainedCompletion_eq_native]
  exact probEvent_jointCompletionFailure_le_finish _

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
