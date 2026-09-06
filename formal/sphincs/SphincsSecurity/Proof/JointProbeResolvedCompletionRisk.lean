import SphincsSecurity.Proof.JointProbeResolvedGameCoupling

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem finishJointResolved_project_eq
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult (α × JointSourceCache)))) :
    OtsProbeSimulation.finishResolvedRunIsNone (projectJointResolvedCache parameter table result) =
      OtsProbeSimulation.finishResolvedRunIsNone (cleanJointResolved result) := by
  unfold projectJointResolvedCache
  cases hresult : cleanJointResolved result with
  | none => rfl
  | some entry => exact OtsProbeSimulation.finishResolvedRunIsNone_value_eq entry.context entry.remaining entry.table _ _

theorem probEvent_native_completion_le_joint_of_coupled
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (joint : ProbComp (AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult (α × JointSourceCache)))))
    (native : ProbComp (Option (ResolvedRunResult (α × OtsProbeSimulation.SplitHashCache))))
    (h : RelTriple joint native (JointResolvedCleanRel parameter table)) :
    Pr[fun verdict => verdict = true | native >>= OtsProbeSimulation.finishResolvedRunIsNone] ≤
      Pr[fun verdict => verdict = true | joint >>= fun result => OtsProbeSimulation.finishResolvedRunIsNone (cleanJointResolved result)] := by
  have hcost := expected_cost_le_of_relTriple (relTriple_symm h)
    (fun result => Pr[fun verdict => verdict = true | OtsProbeSimulation.finishResolvedRunIsNone result])
    (fun result => Pr[fun verdict => verdict = true | OtsProbeSimulation.finishResolvedRunIsNone (cleanJointResolved result)])
    (fun _ => 0) (by
      intro nativeResult jointResult hrel
      rw [add_zero]
      rcases hrel with hhit | heq
      · rw [cleanJointResolved_eq_none_of_hit jointResult hhit]
        simp [OtsProbeSimulation.finishResolvedRunIsNone, OtsProbeSimulation.finishResolvedRun]
      · rw [← heq, finishJointResolved_project_eq])
  simpa only [probEvent_bind_eq_tsum, mul_zero, tsum_zero, add_zero] using hcost

theorem probEvent_outerCappedNative_completion_le_jointResolved
    (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (table : Coordinate → Digest) (q fuel : Nat) :
    Pr[fun verdict => verdict = true |
      OtsProbeSimulation.runResolvedFromTable (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable
        ((outerCappedNativeRetained adversary parameter (fun index tree leaf => table (index, tree, leaf)) q).run
          OtsProbeSimulation.emptySplitHashCache) >>= OtsProbeSimulation.finishResolvedRunIsNone] ≤
      Pr[fun result => result = none | jointResolvedRetainedCompletion adversary parameter otsTable table q fuel] := by
  have h := probEvent_native_completion_le_joint_of_coupled parameter table _ _
    (relTriple_jointResolvedRetainedDetailed adversary parameter otsTable table q fuel)
  simpa only [jointResolvedRetainedCompletion, OtsProbeSimulation.finishResolvedRunIsNone,
    probEvent_bind_eq_tsum, probEvent_map, Function.comp_def, Option.isNone_iff_eq_none] using h

theorem probEvent_outerCappedNative_completion_le_nativeFts
    (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (table : Coordinate → Digest) (q fuel : Nat) :
    Pr[fun verdict => verdict = true |
      OtsProbeSimulation.runResolvedFromTable (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable
        ((outerCappedNativeRetained adversary parameter (fun index tree leaf => table (index, tree, leaf)) q).run
          OtsProbeSimulation.emptySplitHashCache) >>= OtsProbeSimulation.finishResolvedRunIsNone] ≤
      Pr[fun result => result = none | nativeFtsRetainedCompletion adversary parameter otsTable table q fuel] := by
  rw [← jointResolvedRetainedCompletion_eq_native]
  exact probEvent_outerCappedNative_completion_le_jointResolved adversary parameter otsTable table q fuel

end SphincsSecurity.Concrete.FtsProbeSimulation
