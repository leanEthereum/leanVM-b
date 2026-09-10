import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeFresh
import SphincsSecurity.Proof.FewTimeOriginSampler

/-! Weighted forest-pattern counting for budgets up to `2^125`. The bound retains the number of selected signatures in each origin weight. -/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

set_option exponentiation.threshold 600

abbrev OriginConfiguration.RawTargetSample {signatures distinct : Nat}
    {pattern : FewTimePattern signatures distinct} {sources : Nat}
    (configuration : OriginConfiguration pattern sources) :=
  ((pattern.selected → FewTimeView) × HashOutput) × BitVec (127 * configuration.prehit.card)

def OriginConfiguration.RawTargetHit {signatures distinct : Nat}
    {pattern : FewTimePattern signatures distinct} {sources : Nat}
    (configuration : OriginConfiguration pattern sources)
    (sample : configuration.RawTargetSample) : Prop :=
  (signAttemptResultOfOutput sample.1.2 ≠ none ∧
    FixedFewTimePatternHit pattern.assignment (sample.1.1, hashOutputFewTimeView sample.1.2)) ∧
      sample.2 = 0

theorem probEvent_rawTargetPatternHit_eq_admissible_mul
    {Selected : Type} [Fintype Selected] [DecidableEq Selected] [Nonempty Selected]
    (assignment : FtsTree → Selected) :
    Pr[fun sample : (Selected → FewTimeView) × HashOutput =>
      signAttemptResultOfOutput sample.2 ≠ none ∧
        FixedFewTimePatternHit assignment (sample.1, hashOutputFewTimeView sample.2) |
      ($ᵗ ((Selected → FewTimeView) × HashOutput) : ProbComp _)] =
    ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
      Pr[FixedFewTimePatternHit assignment |
        ($ᵗ ((Selected → FewTimeView) × FewTimeView) : ProbComp _)] := by
  let rawEvent := fun sample : (Selected → FewTimeView) × HashOutput =>
    signAttemptResultOfOutput sample.2 ≠ none ∧
      FixedFewTimePatternHit assignment (sample.1, hashOutputFewTimeView sample.2)
  have hraw : Pr[rawEvent | ($ᵗ ((Selected → FewTimeView) × HashOutput) : ProbComp _)] =
      Pr[rawEvent | (($ᵗ (Selected → FewTimeView) : ProbComp _) >>= fun views =>
        Prod.mk views <$> ($ᵗ HashOutput : ProbComp _))] := by
    apply probEvent_congr' (fun _ _ => Iff.rfl)
    simpa only [map_eq_bind_pure_comp, Function.comp_apply, evalDist_bind, evalDist_pure, evalDist_uniformSample] using
      (evalDist_independent_uniform_pair (α := Selected → FewTimeView) (β := HashOutput)).symm
  have hviews : Pr[FixedFewTimePatternHit assignment |
      ($ᵗ ((Selected → FewTimeView) × FewTimeView) : ProbComp _)] =
      Pr[FixedFewTimePatternHit assignment |
        (($ᵗ (Selected → FewTimeView) : ProbComp _) >>= fun views =>
          Prod.mk views <$> ($ᵗ FewTimeView : ProbComp _))] := by
    apply probEvent_congr' (fun _ _ => Iff.rfl)
    simpa only [map_eq_bind_pure_comp, Function.comp_apply, evalDist_bind, evalDist_pure, evalDist_uniformSample] using
      (evalDist_independent_uniform_pair (α := Selected → FewTimeView) (β := FewTimeView)).symm
  change Pr[rawEvent | _] = _
  rw [hraw, hviews]
  dsimp only [rawEvent]
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  simp only [probEvent_map, Function.comp_def]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro views
  have hview := probEvent_uniformHashOutput_admissible_view
    (fun target => FixedFewTimePatternHit assignment (views, target))
  simp only [probEvent_uniformSample] at hview ⊢
  rw [hview]
  ring

theorem probEvent_originConfiguration_rawTargetHit
    {signatures distinct : Nat} {pattern : FewTimePattern signatures distinct} {sources : Nat}
    (configuration : OriginConfiguration pattern sources) :
    Pr[configuration.RawTargetHit |
      ($ᵗ configuration.RawTargetSample : ProbComp configuration.RawTargetSample)] =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        Pr[configuration.Hit | ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
  classical
  letI : Nonempty pattern.selected := ⟨pattern.assignment ⟨0, by decide⟩⟩
  have hraw : Pr[configuration.RawTargetHit |
      ($ᵗ configuration.RawTargetSample : ProbComp configuration.RawTargetSample)] =
      Pr[fun sample : (pattern.selected → FewTimeView) × HashOutput =>
        signAttemptResultOfOutput sample.2 ≠ none ∧
          FixedFewTimePatternHit pattern.assignment (sample.1, hashOutputFewTimeView sample.2) |
        ($ᵗ ((pattern.selected → FewTimeView) × HashOutput) : ProbComp _)] *
      Pr[fun value : BitVec (127 * configuration.prehit.card) => value = 0 |
        ($ᵗ BitVec (127 * configuration.prehit.card) : ProbComp _)] := by
    apply probEvent_seq_map_eq_mul
    intro _ _ _ _
    rfl
  have hideal : Pr[configuration.Hit | ($ᵗ configuration.Sample : ProbComp configuration.Sample)] =
      Pr[FixedFewTimePatternHit pattern.assignment |
        ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) : ProbComp _)] *
      Pr[fun value : BitVec (127 * configuration.prehit.card) => value = 0 |
        ($ᵗ BitVec (127 * configuration.prehit.card) : ProbComp _)] := by
    apply probEvent_seq_map_eq_mul
    intro _ _ _ _
    rfl
  rw [hraw, hideal]
  have hpattern := probEvent_rawTargetPatternHit_eq_admissible_mul pattern.assignment
  simp only [probEvent_uniformSample] at hpattern ⊢
  rw [hpattern, mul_assoc]

noncomputable def rawTargetOriginUnionBound (signatures sources : Nat) : ℝ≥0∞ :=
  ∑ distinct ∈ Finset.Icc 1 14,
    ∑ pattern : FewTimePattern signatures distinct,
      ∑ configuration : OriginConfiguration pattern sources,
        Pr[configuration.RawTargetHit |
          ($ᵗ configuration.RawTargetSample : ProbComp configuration.RawTargetSample)]

theorem rawTargetOriginUnionBound_eq (signatures sources : Nat) :
    rawTargetOriginUnionBound signatures sources =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * idealOriginUnionBound signatures sources := by
  classical
  unfold rawTargetOriginUnionBound idealOriginUnionBound
  simp_rw [probEvent_originConfiguration_rawTargetHit, ← Finset.mul_sum]

end SphincsSecurity.Concrete
