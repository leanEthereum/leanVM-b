import SphincsSecurity.Proof.JointProbeErasedTotal
import SphincsSecurity.Proof.SecurityJointResolvedEndpoint

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex sampleOtsHashTable)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem finish_flatten_none_le_native_add_value_none
    (result : Option (ResolvedRunResult (Option α))) :
    Pr[fun verdict => verdict = true | OtsProbeSimulation.finishResolvedRunIsNone (flattenOptionalResolved result)] ≤
      Pr[fun verdict => verdict = true | OtsProbeSimulation.finishResolvedRunIsNone result] +
        if OtsProbeSimulation.resolvedPrefixValue result = some none then 1 else 0 := by
  cases result with
  | none => simp [flattenOptionalResolved, OtsProbeSimulation.resolvedPrefixValue,
      OtsProbeSimulation.finishResolvedRunIsNone, OtsProbeSimulation.finishResolvedRun]
  | some entry =>
      cases hvalue : entry.value with
      | none =>
          rw [show flattenOptionalResolved (some entry) = none by simp [flattenOptionalResolved, hvalue]]
          simp [OtsProbeSimulation.resolvedPrefixValue, hvalue,
            OtsProbeSimulation.finishResolvedRunIsNone, OtsProbeSimulation.finishResolvedRun]
      | some value =>
          simp only [flattenOptionalResolved, hvalue, Option.map_some, OtsProbeSimulation.resolvedPrefixValue,
            Option.some.injEq, reduceCtorEq, if_false, add_zero]
          exact le_of_eq (congrArg (fun computation => Pr[fun verdict => verdict = true | computation])
            (OtsProbeSimulation.finishResolvedRunIsNone_value_eq entry.context entry.remaining entry.table value entry.value))

theorem probEvent_finish_flatten_none_le_native_add_value_none
    (computation : ProbComp (Option (ResolvedRunResult (Option α)))) :
    Pr[fun result => result = none | computation >>= fun result => OtsProbeSimulation.finishResolvedRun (flattenOptionalResolved result)] ≤
      Pr[fun result => result = none | computation >>= OtsProbeSimulation.finishResolvedRun] +
        Pr[fun result => OtsProbeSimulation.resolvedPrefixValue result = some none | computation] := by
  have h := ENNReal.tsum_le_tsum fun result => mul_le_mul' (show Pr[= result | computation] ≤ Pr[= result | computation] from le_rfl)
    (finish_flatten_none_le_native_add_value_none result)
  simp only [mul_add, ENNReal.tsum_add, OtsProbeSimulation.finishResolvedRunIsNone, probEvent_map,
    Function.comp_def, Option.isNone_iff_eq_none, mul_ite, mul_one, mul_zero] at h
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  exact h

theorem probEvent_sampled_nativeFtsResolved_value_none_le_hit
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q fuel : Nat) :
    (∑' otsTable, Pr[= otsTable | sampleOtsHashTable] *
      Pr[fun result => OtsProbeSimulation.resolvedPrefixValue result = some none |
        nativeFtsRetainedResolved adversary parameter otsTable table q fuel]) ≤
      jointRetainedFtsHitRisk adversary parameter table q :=
  (OtsProbeSimulation.probEvent_sampled_resolved_value_le_erased_history ∅
    (nativeFtsRetainedSource adversary parameter table q) fuel (fun result => result = some none) (by simp)).trans
    (probEvent_nativeFtsErased_value_none_le_hit adversary parameter table q)

theorem probEvent_sampled_nativeFts_completion_le_ots_add_fts_hit
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q fuel : Nat) :
    (∑' otsTable, Pr[= otsTable | sampleOtsHashTable] *
      Pr[fun result => result = none | nativeFtsRetainedCompletion adversary parameter otsTable table q fuel]) ≤
      (∑' otsTable, Pr[= otsTable | sampleOtsHashTable] *
        Pr[fun result => result = none | nativeFtsRetainedResolved adversary parameter otsTable table q fuel >>=
          OtsProbeSimulation.finishResolvedRun]) + jointRetainedFtsHitRisk adversary parameter table q := by
  apply (ENNReal.tsum_le_tsum fun otsTable => mul_le_mul' le_rfl
    (probEvent_finish_flatten_none_le_native_add_value_none
      (nativeFtsRetainedResolved adversary parameter otsTable table q fuel))).trans
  simp only [mul_add, ENNReal.tsum_add]
  exact add_le_add le_rfl (probEvent_sampled_nativeFtsResolved_value_none_le_hit adversary parameter table q fuel)

end SphincsSecurity.Concrete.FtsProbeSimulation
