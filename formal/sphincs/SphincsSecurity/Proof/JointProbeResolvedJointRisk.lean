import SphincsSecurity.Proof.JointProbeResolvedFtsWitness

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex sampleOtsHashTable)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem resolvedRetainedJointEvent_imp_failure_or_witness
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult (Option RetainedGameResult × JointSourceCache))))
    (hevent : ResolvedRetainedJointEvent parameter table (projectJointResolvedCache parameter table result)) :
    OtsProbeSimulation.retainCompletableResult (cleanJointResolved result) = none ∨
      ∃ value, OtsProbeSimulation.resolvedPrefixValue (cleanJointResolved result) = some value ∧
        JointSourceFtsWitness parameter table value := by
  unfold ResolvedRetainedJointEvent projectJointResolvedCache at hevent
  cases hresult : cleanJointResolved result with
  | none => exact Or.inl rfl
  | some entry =>
      by_cases hcomplete : OtsProbeSimulation.DeferredCompletable entry.table entry.context
      · simp only [hresult, Option.map_some, OtsProbeSimulation.retainCompletableResult, if_pos hcomplete,
          reduceCtorEq, false_or, OtsProbeSimulation.resolvedPrefixValue, Option.some.injEq] at hevent
        rcases hevent with ⟨value, rfl, retained, hretained, hwitness⟩
        cases hvalue : entry.value.1 with
        | none => simp [flattenRetainedCache, hvalue] at hretained
        | some value =>
            simp only [flattenRetainedCache, hvalue, Option.map_some, Option.some.injEq] at hretained
            subst retained
            exact Or.inr ⟨entry.value, rfl, value, hvalue, hwitness⟩
      · exact Or.inl (if_neg hcomplete)

theorem probEvent_retain_none_le_finish
    (computation : ProbComp (Option (ResolvedRunResult α))) :
    Pr[fun result => OtsProbeSimulation.retainCompletableResult result = none | computation] ≤
      Pr[fun result => result = none | computation >>= OtsProbeSimulation.finishResolvedRun] := by
  calc
    _ = Pr[fun result => OtsProbeSimulation.retainCompletableResult result = none | computation >>= pure] := by rw [bind_pure]
    _ ≤ _ := by
      apply probEvent_bind_le_bind_of_forall_le
      intro result _
      cases result with
      | none => simp [OtsProbeSimulation.retainCompletableResult, OtsProbeSimulation.finishResolvedRun]
      | some entry =>
          by_cases hcomplete : OtsProbeSimulation.DeferredCompletable entry.table entry.context <;>
            simp [OtsProbeSimulation.retainCompletableResult, OtsProbeSimulation.finishResolvedRun, hcomplete]

theorem probEvent_jointResolved_joint_le_completion_add_witness
    (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (table : Coordinate → Digest) (q fuel : Nat) :
    Pr[fun result => ResolvedRetainedJointEvent parameter table (projectJointResolvedCache parameter table result) |
      jointResolvedRetainedDetailed adversary parameter otsTable table q fuel] ≤
      Pr[fun result => result = none | jointResolvedRetainedCompletion adversary parameter otsTable table q fuel] +
      Pr[fun result => ∃ value, OtsProbeSimulation.resolvedPrefixValue (cleanJointResolved result) = some value ∧
        JointSourceFtsWitness parameter table value | jointResolvedRetainedDetailed adversary parameter otsTable table q fuel] := by
  apply (probEvent_mono (fun result _ => resolvedRetainedJointEvent_imp_failure_or_witness parameter table result)).trans
  apply (probEvent_or_le _ _ _).trans
  apply add_le_add _ le_rfl
  have h := probEvent_retain_none_le_finish
    (cleanJointResolved <$> jointResolvedRetainedDetailed adversary parameter otsTable table q fuel)
  simpa only [probEvent_map, Function.comp_def, bind_map_left, jointResolvedRetainedCompletion] using h

theorem probEvent_sampled_native_joint_le_nativeFts_completion
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : Coordinate → Digest)
    (hfts : (fun index tree leaf => table (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    (∑' otsTable, Pr[= otsTable | sampleOtsHashTable] *
      Pr[fun trace => trace.1 = none ∨ OtsProbeSimulation.NativeFtsTraceEvent parameter otsTable
          (fun index tree leaf => table (index, tree, leaf)) trace |
        OtsProbeSimulation.nativeRetainedParentTrace adversary parameter otsTable
          (fun index tree leaf => table (index, tree, leaf)) fuel]) ≤
      ∑' otsTable, Pr[= otsTable | sampleOtsHashTable] *
        Pr[fun result => result = none | nativeFtsRetainedCompletion adversary parameter otsTable table q fuel] := by
  apply (ENNReal.tsum_le_tsum fun otsTable => mul_le_mul' le_rfl
    ((probEvent_native_joint_le_jointResolved adversary q hq parameter hparameter otsTable table hfts fuel).trans
      (probEvent_jointResolved_joint_le_completion_add_witness adversary parameter otsTable table q fuel))).trans_eq
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, probEvent_sampled_jointResolved_ftsWitness_eq_zero, add_zero]
  exact tsum_congr fun otsTable => congrArg (fun risk => Pr[= otsTable | sampleOtsHashTable] * risk)
    (congrArg (fun computation => Pr[fun result => result = none | computation])
      (jointResolvedRetainedCompletion_eq_native adversary parameter otsTable table q fuel))

end SphincsSecurity.Concrete.FtsProbeSimulation
