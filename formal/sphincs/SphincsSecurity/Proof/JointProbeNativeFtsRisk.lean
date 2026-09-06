import SphincsSecurity.Proof.JointProbeInterpretedBudget
import SphincsSecurity.Proof.FtsProbeJointWitnessClassification

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (HistoryResolvedPrefix)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] jointSourceRetained jointRetainedDetailed OtsProbeSimulation.maskedPublishedTreeRoot

noncomputable def nativeFtsRetainedSource (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → Digest) (q : Nat) :
    OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) (Option (Option RetainedGameResult × JointSourceCache)) :=
  runJointFts table ((jointSourceRetained adversary parameter q).run
    (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache)) AdaptiveRevealProbe.State.empty q

theorem nativeFtsRetainedSource_probeBound (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → Digest) (q : Nat) :
    (nativeFtsRetainedSource adversary parameter table q).IsQueryBoundP LazyRevealProbe.IsProbe q :=
  runJointFts_probeBound table _ q (jointSourceRetained_probeBound adversary parameter q _)
    AdaptiveRevealProbe.State.empty q

noncomputable def nativeFtsRetainedErasedHistory (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → Digest) (q : Nat) :=
  OtsProbeSimulation.runResolvedHistoryPrefix
    (OtsProbeSimulation.eraseProbeQueries (nativeFtsRetainedSource adversary parameter table q))
    (OtsProbeSimulation.ensuredInitialContext ∅) 0 []

def jointRetainedCleanHistory
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (NativeStepResult (Option RetainedGameResult) × SplitHashCache)) :=
  cleanJointHistory (result.mapValue packJointStepResult)

def JointRetainedFailure
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (NativeStepResult (Option RetainedGameResult) × SplitHashCache)) : Prop :=
  result.hit = true ∨ ∃ state cache, result = .done false state (none, cache)

theorem jointRetainedCleanHistory_eq_nativeFts (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → Digest) (q : Nat) :
    jointRetainedCleanHistory <$> jointRetainedDetailed adversary parameter table q =
      flattenOptionalHistory <$> nativeFtsRetainedErasedHistory adversary parameter table q := by
  unfold nativeFtsRetainedErasedHistory nativeFtsRetainedSource
  rw [← runJointFts_erasedHistory_commute, runDetailed_jointSourceRetained, Functor.map_map]
  rfl

theorem jointRetainedFailure_iff_cleanHistory_none
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat)
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (NativeStepResult (Option RetainedGameResult) × SplitHashCache))
    (hresult : result ∈ support (jointRetainedDetailed adversary parameter table q)) :
    JointRetainedFailure result ↔ jointRetainedCleanHistory result = none := by
  cases result with
  | stopped hit =>
      cases hit with
      | false => exact False.elim (jointRetainedDetailed_not_stopped_false adversary parameter table q hresult)
      | true => simp [JointRetainedFailure, jointRetainedCleanHistory, cleanJointHistory, AdaptiveRevealProbe.DetailedResult.hit,
          AdaptiveRevealProbe.DetailedResult.mapValue]
  | done hit state value =>
      rcases value with ⟨entry, cache⟩
      cases hit <;> cases entry <;>
        simp [JointRetainedFailure, jointRetainedCleanHistory, cleanJointHistory, packJointStepResult,
          AdaptiveRevealProbe.DetailedResult.hit, AdaptiveRevealProbe.DetailedResult.mapValue]

theorem probEvent_jointRetainedFailure_eq_nativeFts (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → Digest) (q : Nat) :
    Pr[JointRetainedFailure | jointRetainedDetailed adversary parameter table q] =
      Pr[fun result => flattenOptionalHistory result = none | nativeFtsRetainedErasedHistory adversary parameter table q] := by
  calc
    _ = Pr[fun result => jointRetainedCleanHistory result = none | jointRetainedDetailed adversary parameter table q] := by
      apply probEvent_congr' _ rfl
      exact jointRetainedFailure_iff_cleanHistory_none adversary parameter table q
    _ = Pr[fun output => output = none | jointRetainedCleanHistory <$> jointRetainedDetailed adversary parameter table q] := by simp only [probEvent_map, Function.comp_def]
    _ = Pr[fun output => output = none | flattenOptionalHistory <$> nativeFtsRetainedErasedHistory adversary parameter table q] := by
      rw [jointRetainedCleanHistory_eq_nativeFts]
    _ = _ := by simp only [probEvent_map, Function.comp_def]

theorem jointRetainedFtsHitRisk_le_nativeFts_failure (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → Digest) (q : Nat) :
    jointRetainedFtsHitRisk adversary parameter table q ≤
      Pr[fun result => flattenOptionalHistory result = none | nativeFtsRetainedErasedHistory adversary parameter table q] := by
  rw [← probEvent_jointRetainedFailure_eq_nativeFts]
  exact probEvent_mono (fun _ _ hhit => Or.inl hhit)

end SphincsSecurity.Concrete.FtsProbeSimulation
