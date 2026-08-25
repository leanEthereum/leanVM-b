import SphincsSecurity.Proof.FewTimeOriginSampler
import SphincsSecurity.Proof.FewTimePadding

/-!
# Candidate targets for the origin-weighted few-time bound

The forgery's message-digest view can be identified only after the adversary returns.  This module
allows the origin-weighted ideal count to expose a finite table of candidate target views and pays
once for each candidate.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

abbrev OriginConfiguration.CandidateSample {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (candidates : Nat) :=
  ((pattern.selected → FewTimeView) × (Fin candidates → FewTimeView)) ×
    BitVec (127 * configuration.prehit.card)

def OriginConfiguration.HitCandidates {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (candidates : Nat)
    (sample : configuration.CandidateSample candidates) : Prop :=
  ∃ candidate,
    FixedFewTimePatternHit pattern.assignment
      (sample.1.1, sample.1.2 candidate) ∧ sample.2 = 0

noncomputable instance {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (candidates : Nat) :
    DecidablePred (configuration.HitCandidates candidates) :=
  fun sample => Classical.propDecidable (configuration.HitCandidates candidates sample)

noncomputable def originCandidateViewsSample {signatures distinct : Nat}
    (pattern : FewTimePattern signatures distinct) (candidates : Nat) :
    ProbComp ((pattern.selected → FewTimeView) × (Fin candidates → FewTimeView)) := do
  let views ← $ᵗ (pattern.selected → FewTimeView)
  let targets ← $ᵗ (Fin candidates → FewTimeView)
  pure (views, targets)

noncomputable def originCandidateSample {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (candidates : Nat) :
    ProbComp (configuration.CandidateSample candidates) := do
  let views ← originCandidateViewsSample pattern candidates
  let activation ← $ᵗ BitVec (127 * configuration.prehit.card)
  pure (views, activation)

theorem evalDist_originCandidateViews_target {signatures distinct candidates : Nat}
    (pattern : FewTimePattern signatures distinct) (candidate : Fin candidates) :
    𝒟[(fun sample => (sample.1, sample.2 candidate)) <$>
        originCandidateViewsSample pattern candidates] =
      𝒟[($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) :
        ProbComp ((pattern.selected → FewTimeView) × FewTimeView))] := by
  calc
    _ = 𝒟[(do
        let views ← $ᵗ (pattern.selected → FewTimeView)
        let target ← $ᵗ FewTimeView
        pure (views, target))] := by
      rw [originCandidateViewsSample]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      apply evalDist_bind_congr
      intro views _
      change 𝒟[(fun targets : Fin candidates → FewTimeView =>
          (views, targets candidate)) <$>
            ($ᵗ (Fin candidates → FewTimeView) :
              ProbComp (Fin candidates → FewTimeView))] =
        𝒟[(fun target : FewTimeView => (views, target)) <$>
          ($ᵗ FewTimeView : ProbComp FewTimeView)]
      calc
        _ = 𝒟[(fun target : FewTimeView => (views, target)) <$>
            ((fun targets : Fin candidates → FewTimeView => targets candidate) <$>
              ($ᵗ (Fin candidates → FewTimeView) :
                ProbComp (Fin candidates → FewTimeView)))] := by
          simp [Functor.map_map]
        _ = _ := by
          rw [evalDist_map, evalDist_uniformCandidateFunctionEval candidate, ← evalDist_map]
    _ = _ := evalDist_independent_uniform_pair

theorem evalDist_originCandidateSample_target {signatures distinct sources candidates : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (candidate : Fin candidates) :
    𝒟[(fun sample => ((sample.1.1, sample.1.2 candidate), sample.2)) <$>
        originCandidateSample configuration candidates] =
      𝒟[($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
  let activationSampler :=
    ($ᵗ BitVec (127 * configuration.prehit.card) :
      ProbComp (BitVec (127 * configuration.prehit.card)))
  calc
    _ = 𝒟[(do
        let views ← (fun sample :
            (pattern.selected → FewTimeView) × (Fin candidates → FewTimeView) =>
          (sample.1, sample.2 candidate)) <$>
          originCandidateViewsSample pattern candidates
        let activation ← activationSampler
        pure (views, activation))] := by
      simp [originCandidateSample, activationSampler, map_eq_bind_pure_comp, bind_assoc]
    _ = 𝒟[(do
        let views ← $ᵗ ((pattern.selected → FewTimeView) × FewTimeView)
        let activation ← activationSampler
        pure (views, activation))] := by
      rw [evalDist_bind, evalDist_originCandidateViews_target pattern candidate,
        ← evalDist_bind]
    _ = _ := by
      simpa [activationSampler] using
        (evalDist_independent_uniform_pair
          (α := (pattern.selected → FewTimeView) × FewTimeView)
          (β := BitVec (127 * configuration.prehit.card)))

theorem probEvent_originConfiguration_hitCandidate {signatures distinct sources candidates : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (candidate : Fin candidates) :
    Pr[fun sample =>
        FixedFewTimePatternHit pattern.assignment
          (sample.1.1, sample.1.2 candidate) ∧ sample.2 = 0 |
      originCandidateSample configuration candidates] =
      Pr[configuration.Hit |
        ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
  calc
    _ = Pr[configuration.Hit |
        (fun sample => ((sample.1.1, sample.1.2 candidate), sample.2)) <$>
          originCandidateSample configuration candidates] := by
      rw [probEvent_map]
      rfl
    _ = _ := probEvent_congr' (fun _ _ => Iff.rfl)
      (evalDist_originCandidateSample_target configuration candidate)

theorem probEvent_originConfiguration_hitCandidates_le
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (candidates : Nat) :
    Pr[configuration.HitCandidates candidates |
        originCandidateSample configuration candidates] ≤
      candidates * Pr[configuration.Hit |
        ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
  classical
  let sampler := originCandidateSample configuration candidates
  calc
    Pr[configuration.HitCandidates candidates | sampler] =
        Pr[fun sample => ∃ candidate ∈ (Finset.univ : Finset (Fin candidates)),
          FixedFewTimePatternHit pattern.assignment
            (sample.1.1, sample.1.2 candidate) ∧ sample.2 = 0 | sampler] := by
      congr 1
      funext sample
      simp [OriginConfiguration.HitCandidates]
    _ ≤ ∑ candidate ∈ (Finset.univ : Finset (Fin candidates)),
          Pr[fun sample => FixedFewTimePatternHit pattern.assignment
              (sample.1.1, sample.1.2 candidate) ∧ sample.2 = 0 | sampler] :=
      probEvent_exists_finset_le_sum Finset.univ sampler
        (fun candidate sample => FixedFewTimePatternHit pattern.assignment
          (sample.1.1, sample.1.2 candidate) ∧ sample.2 = 0)
    _ = ∑ _candidate ∈ (Finset.univ : Finset (Fin candidates)),
          Pr[configuration.Hit |
            ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
      apply Finset.sum_congr rfl
      intro candidate _
      exact probEvent_originConfiguration_hitCandidate configuration candidate
    _ = candidates * Pr[configuration.Hit |
          ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

noncomputable def idealOriginCandidateUnionBound
    (signatures sources candidates : Nat) : ℝ≥0∞ :=
  ∑ distinct ∈ Finset.Icc 1 14,
    ∑ pattern : FewTimePattern signatures distinct,
      ∑ configuration : OriginConfiguration pattern sources,
        Pr[configuration.HitCandidates candidates |
          originCandidateSample configuration candidates]

theorem idealOriginCandidateUnionBound_le_origin
    (signatures sources candidates : Nat) :
    idealOriginCandidateUnionBound signatures sources candidates ≤
      candidates * idealOriginUnionBound signatures sources := by
  classical
  rw [idealOriginCandidateUnionBound, idealOriginUnionBound]
  calc
    _ ≤ ∑ distinct ∈ Finset.Icc 1 14,
        ∑ pattern : FewTimePattern signatures distinct,
          ∑ configuration : OriginConfiguration pattern sources,
            candidates * Pr[configuration.Hit |
              ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
      apply Finset.sum_le_sum
      intro distinct _
      apply Finset.sum_le_sum
      intro pattern _
      apply Finset.sum_le_sum
      intro configuration _
      exact probEvent_originConfiguration_hitCandidates_le configuration candidates
    _ = _ := by
      simp_rw [← Finset.mul_sum]

theorem idealOriginCandidateUnionBound_le {signatures sources candidates : Nat}
    (hsignatures : signatures ≤ signatureLimit) (hsources : sources ≤ 2 ^ 120) :
    idealOriginCandidateUnionBound signatures sources candidates ≤
      candidates * ((2 ^ 121 : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ candidates * idealOriginUnionBound signatures sources :=
      idealOriginCandidateUnionBound_le_origin signatures sources candidates
    _ ≤ _ := by
      gcongr
      exact idealOriginUnionBound_le hsignatures hsources

end SphincsSecurity.Concrete
