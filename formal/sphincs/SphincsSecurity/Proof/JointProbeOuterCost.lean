import SphincsSecurity.Proof.JointProbeNativeBlockCost
import SphincsSecurity.Proof.AdaptiveRevealProbeRawRemaining
import SphincsSecurity.Proof.FtsProbeJointOuterCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] maskedJointSign

theorem runRaw_jointOuterQuery_eq_detailed
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (state : AdaptiveRevealProbe.State Coordinate)
    (ftsFuel : Nat) (hpositive : OtsProbeSimulation.IsOuterHash input → 0 < ftsFuel)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache) :
    AdaptiveRevealProbe.runRaw table state ftsFuel ((jointOuterQuery parameter root input context fuel history cache).run ftsCache) =
      AdaptiveRevealProbe.rawResultWithRemaining (jointOuterRemaining parameter input ftsFuel) <$>
        AdaptiveRevealProbe.runDetailed table state ftsFuel ((jointOuterQuery parameter root input context fuel history cache).run ftsCache) := by
  cases input with
  | inl input =>
      cases input with
      | inl n =>
          exact AdaptiveRevealProbe.runRaw_eq_detailed_of_probeFree table state ftsFuel _
            (liftNativeBlock_probeFree _ context fuel history cache ftsCache)
      | inr input =>
          change AdaptiveRevealProbe.runRaw table state ftsFuel ((maskedJointHashQuery parameter input context fuel history cache).run ftsCache) = _
          cases hdecode : decodeProbe? parameter input with
          | none =>
              simp only [jointOuterRemaining, hdecode, Option.isSome_none, Bool.false_eq_true, if_false,
                jointOuterQuery, maskedJointHashQuery]
              exact AdaptiveRevealProbe.runRaw_eq_detailed_of_probeFree table state ftsFuel _
                (liftNativeBlock_probeFree _ context fuel history cache ftsCache)
          | some probe =>
              have hpos := hpositive (by trivial)
              cases ftsFuel with
              | zero => omega
              | succ remaining =>
                  simp only [jointOuterRemaining, hdecode, Option.isSome_some, if_true, Nat.add_sub_cancel,
                    jointOuterQuery]
                  rw [maskedJointHashQuery_run_decode_some parameter input probe context fuel history cache ftsCache hdecode]
                  exact AdaptiveRevealProbe.runRaw_eq_detailed_of_probePrefix table state remaining
                    (probe.index, probe.tree, probe.leafIdx) probe.candidate _
                    (liftFtsBlock_probeFree _ context fuel history cache (splitHashQuery_probeFree (.ordinary input)) ftsCache)
  | inr message =>
      exact AdaptiveRevealProbe.runRaw_eq_detailed_of_probeFree table state ftsFuel _
        (maskedJointSign_probeFree parameter root message context fuel history cache ftsCache)

theorem expectedJointNativeProbeCost_outerQuery
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (cache : JointSourceCache) :
    expectedJointNativeProbeCost table ((jointSourceOuterQuery parameter root input).run cache) state ftsFuel context =
      jointOtsQueryCharge parameter input context cache.1 state cache.2 := by
  cases input with
  | inl input =>
      cases input with
      | inl n =>
          exact expectedJointNativeProbeCost_eq_zero_of_probeFree table _
            (jointSourceNativeBlock_probeBound _ 0 (OtsProbeSimulation.splitUniformImpl_probeFree n) cache) state ftsFuel context
      | inr input =>
          change expectedJointNativeProbeCost table ((jointSourceHashQuery parameter input).run cache) state ftsFuel context = _
          unfold jointSourceHashQuery
          cases hdecode : decodeProbe? parameter input with
          | none => exact expectedJointNativeProbeCost_nativeBlock table _ state ftsFuel context cache
          | some probe =>
              rw [expectedJointNativeProbeCost_ftsBlock]
              unfold jointOtsQueryCharge
              dsimp only
              rw [nativeProbingHashQuery_eq_ordinary_of_decodeProbe parameter input probe hdecode]
              exact (OtsProbeSimulation.expectedErasedHistoryProbeCost_eq_zero_of_probeFree _ context
                (OtsProbeSimulation.splitHashQuery_probeFree (.ordinary input) _)).symm
  | inr message =>
      exact expectedJointNativeProbeCost_eq_zero_of_probeFree table _
        (jointSourceSign_probeFree parameter root message cache) state ftsFuel context

theorem expectedJointNativeProbeCost_source_bind
    (table : Coordinate → Digest) (left : JointSource α) (next : α → JointSource β) (step : NativeFtsStep α)
    (hleft : JointSourceImplements left step) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (cache : JointSourceCache) :
    expectedJointNativeProbeCost table ((left >>= next).run cache) state ftsFuel context =
      expectedJointNativeProbeCost table (left.run cache) state ftsFuel context +
        ∑' result, Pr[= result | AdaptiveRevealProbe.runRaw table state ftsFuel ((step context 0 [] cache.1).run cache.2)] *
          match result with
          | .stopped _ => 0
          | .done finalState remaining value => match value.1 with
            | none => 0
            | some entry => expectedJointNativeProbeCost table ((next entry.value.1).run (entry.value.2, value.2))
                finalState remaining entry.context := by
  rw [StateT.run_bind, expectedJointNativeProbeCost_bind, hleft, AdaptiveRevealProbe.runRaw_mapValue, tsum_probOutput_map_mul]
  congr 1
  apply tsum_congr
  intro result
  congr 1
  cases result with
  | stopped hit => rfl
  | done finalState remaining value => rcases value with ⟨entry, finalCache⟩; cases entry <;> rfl

end SphincsSecurity.Concrete.FtsProbeSimulation
