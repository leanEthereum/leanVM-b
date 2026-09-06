import SphincsSecurity.Proof.JointProbeResolvedFinalization

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] jointSourceRetained

noncomputable def jointResolvedRetainedDetailed (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) :=
  AdaptiveRevealProbe.runDetailed ftsTable AdaptiveRevealProbe.State.empty q
    (runJointResolved ((jointSourceRetained adversary parameter q).run
      (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache))
      (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable)

noncomputable def nativeFtsRetainedResolved (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) :=
  OtsProbeSimulation.runResolvedFromTable (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable
    (nativeFtsRetainedSource adversary parameter ftsTable q)

theorem jointResolvedRetained_clean_eq_native (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) :
    cleanJointResolved <$> jointResolvedRetainedDetailed adversary parameter otsTable ftsTable q fuel =
      flattenOptionalResolved <$> nativeFtsRetainedResolved adversary parameter otsTable ftsTable q fuel := by
  unfold jointResolvedRetainedDetailed nativeFtsRetainedResolved nativeFtsRetainedSource
  exact runJointFts_resolved_commute ftsTable _ AdaptiveRevealProbe.State.empty q _ fuel otsTable

theorem jointResolvedRetained_not_stopped_false (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) :
    AdaptiveRevealProbe.DetailedResult.stopped false ∉
      support (jointResolvedRetainedDetailed adversary parameter otsTable ftsTable q fuel) :=
  AdaptiveRevealProbe.stopped_false_not_mem_support_runDetailed ftsTable AdaptiveRevealProbe.State.empty q _
    (runJointResolved_probeBound _ q (jointSourceRetained_probeBound adversary parameter q _) _ fuel otsTable)

def JointResolvedFailure (result : AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult α))) : Prop :=
  result.hit = true ∨ ∃ state, result = .done false state none

theorem jointResolvedRetained_failure_iff_clean_none (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat)
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult
      (Option RetainedGameResult × JointSourceCache))))
    (hresult : result ∈ support (jointResolvedRetainedDetailed adversary parameter otsTable ftsTable q fuel)) :
    JointResolvedFailure result ↔ cleanJointResolved result = none := by
  cases result with
  | stopped hit =>
      cases hit with
      | false => exact False.elim (jointResolvedRetained_not_stopped_false adversary parameter otsTable ftsTable q fuel hresult)
      | true => simp [JointResolvedFailure, cleanJointResolved, AdaptiveRevealProbe.DetailedResult.hit]
  | done hit state value =>
      cases hit <;> cases value <;>
        simp [JointResolvedFailure, cleanJointResolved, AdaptiveRevealProbe.DetailedResult.hit]

theorem probEvent_jointResolvedRetained_failure_eq_native (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) :
    Pr[JointResolvedFailure | jointResolvedRetainedDetailed adversary parameter otsTable ftsTable q fuel] =
      Pr[fun result => flattenOptionalResolved result = none |
        nativeFtsRetainedResolved adversary parameter otsTable ftsTable q fuel] := by
  calc
    _ = Pr[fun result => cleanJointResolved result = none |
        jointResolvedRetainedDetailed adversary parameter otsTable ftsTable q fuel] := by
      apply probEvent_congr' _ rfl
      exact jointResolvedRetained_failure_iff_clean_none adversary parameter otsTable ftsTable q fuel
    _ = Pr[fun result => result = none |
        cleanJointResolved <$> jointResolvedRetainedDetailed adversary parameter otsTable ftsTable q fuel] := by
      simp only [probEvent_map, Function.comp_def]
    _ = _ := by
      rw [jointResolvedRetained_clean_eq_native]
      simp only [probEvent_map, Function.comp_def]

noncomputable def jointResolvedRetainedCompletion (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) :=
  jointResolvedRetainedDetailed adversary parameter otsTable ftsTable q fuel >>= fun result =>
    OtsProbeSimulation.finishResolvedRun (cleanJointResolved result)

noncomputable def nativeFtsRetainedCompletion (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) :=
  nativeFtsRetainedResolved adversary parameter otsTable ftsTable q fuel >>= fun result =>
    OtsProbeSimulation.finishResolvedRun (flattenOptionalResolved result)

theorem jointResolvedRetainedCompletion_eq_native (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) :
    jointResolvedRetainedCompletion adversary parameter otsTable ftsTable q fuel =
      nativeFtsRetainedCompletion adversary parameter otsTable ftsTable q fuel := by
  have h := congrArg (fun computation => computation >>= OtsProbeSimulation.finishResolvedRun)
    (jointResolvedRetained_clean_eq_native adversary parameter otsTable ftsTable q fuel)
  simpa only [bind_map_left, jointResolvedRetainedCompletion, nativeFtsRetainedCompletion] using h

end SphincsSecurity.Concrete.FtsProbeSimulation
