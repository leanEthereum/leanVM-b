import SphincsSecurity.Proof.JointPrimitiveTerminal
import SphincsSecurity.Proof.TightEncodingRefinedBound

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def residualPrimitiveEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  result.1.2.2 = true ∧ ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
    ¬ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result ∧
    (cleanOtsOpeningEvent parameter otsSecret ftsSecret result ∨
      cleanUncoveredEvent parameter otsSecret ftsSecret result)

noncomputable def residualPrimitiveQueryCharge (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : ℝ≥0∞ :=
  3 - TightEncoding.refinedStructuralEncodingQueryCharge secretKey cache input

noncomputable def sampledQueryCharge
    (charge : SecretKey → QueryCache HashSpec → HashInput → ℝ≥0∞)
    (adversary : Adversary) : ℝ≥0∞ :=
  ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
    expectedQueryCharge (charge (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret))
      (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅

theorem structural_add_residual_queryCharge (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) :
    TightEncoding.refinedStructuralEncodingQueryCharge secretKey cache input +
      residualPrimitiveQueryCharge secretKey cache input = 3 := by
  exact add_tsub_cancel_of_le
    (TightEncoding.refinedStructuralEncodingQueryCharge_le_three secretKey cache input)

theorem sampled_structural_add_residual_queryCharge_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) :
    sampledQueryCharge TightEncoding.refinedStructuralEncodingQueryCharge adversary +
      sampledQueryCharge residualPrimitiveQueryCharge adversary ≤ 3 * q := by
  rw [sampledQueryCharge, sampledQueryCharge, ← ENNReal.tsum_add]
  calc
    _ ≤ ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] * (3 * q : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro secrets
      rw [← mul_add, ← expectedQueryCharge_add]
      have heq : (fun cache input =>
          TightEncoding.refinedStructuralEncodingQueryCharge
            (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret) cache input +
            residualPrimitiveQueryCharge
              (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret) cache input) = fun _ _ => (3 : ℝ≥0∞) := by
        funext cache input
        exact structural_add_residual_queryCharge
          (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret) cache input
      rw [heq]
      by_cases hsecrets : secrets ∈ support sampleSecrets
      · obtain ⟨hparameter, hots, hfts⟩ := secrets.support_components hsecrets
        exact mul_le_mul' le_rfl (expectedQueryCharge_le_queryBound _ 3 (fun _ _ => le_rfl)
          (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) q
          (isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts) ∅)
      · rw [probOutput_eq_zero_of_not_mem_support hsecrets, zero_mul, zero_mul]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one

theorem probEvent_jointPrimitive_le_structural_charge_add_residual
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[jointPrimitiveEvent parameter otsSecret ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      expectedQueryCharge (TightEncoding.refinedStructuralEncodingQueryCharge
        (primitiveAccountingKey parameter otsSecret ftsSecret))
        (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ +
      Pr[residualPrimitiveEvent parameter otsSecret ftsSecret |
        gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] := by
  calc
    _ ≤ Pr[fun result =>
        (Bad parameter otsSecret ftsSecret result.2.cache ∨
          ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result) ∨
        residualPrimitiveEvent parameter otsSecret ftsSecret result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] := by
      apply probEvent_mono
      intro result _ hevent
      obtain ⟨hwin, hevent⟩ := hevent
      by_cases hbad : Bad parameter otsSecret ftsSecret result.2.cache
      · exact Or.inl (Or.inl hbad)
      by_cases hencoding : ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result
      · exact Or.inl (Or.inr hencoding)
      exact Or.inr ⟨hwin, hbad, hencoding, (hevent.resolve_left hbad).resolve_left hencoding⟩
    _ ≤ _ := (probEvent_or_le _ _ _).trans
      (add_le_add (probEvent_bad_or_viewedEncodingCollision_le_refined_queryCharge
        adversary parameter otsSecret ftsSecret) le_rfl)

theorem probEvent_sampled_jointPrimitive_le_charge_add_residual
    (adversary : Adversary) :
    Pr[SampledViewedEvent jointPrimitiveEvent | sampledViewedGame adversary] ≤
      sampledQueryCharge TightEncoding.refinedStructuralEncodingQueryCharge adversary *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ +
      Pr[SampledViewedEvent residualPrimitiveEvent | sampledViewedGame adversary] := by
  rw [probEvent_sampledViewedGame_eq_weighted,
    probEvent_sampledViewedGame_eq_weighted]
  calc
    _ ≤ ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
        (expectedQueryCharge (TightEncoding.refinedStructuralEncodingQueryCharge
          (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret))
          (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ *
            (Fintype.card Digest : ℝ≥0∞)⁻¹ +
          Pr[residualPrimitiveEvent secrets.parameter secrets.otsSecret secrets.ftsSecret |
            gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret secrets.ftsSecret]) :=
      ENNReal.tsum_le_tsum fun secrets => mul_le_mul' le_rfl
        (probEvent_jointPrimitive_le_structural_charge_add_residual adversary secrets.parameter
          secrets.otsSecret secrets.ftsSecret)
    _ = _ := by
      simp_rw [mul_add, ← mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      rfl

theorem probEvent_sampled_jointPrimitive_le_three_mul_of_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hresidual : Pr[SampledViewedEvent residualPrimitiveEvent | sampledViewedGame adversary] ≤
      sampledQueryCharge residualPrimitiveQueryCharge adversary *
        (Fintype.card Digest : ℝ≥0∞)⁻¹) :
    Pr[SampledViewedEvent jointPrimitiveEvent | sampledViewedGame adversary] ≤
      ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := by
  apply (probEvent_sampled_jointPrimitive_le_charge_add_residual adversary).trans
  calc
    _ ≤ sampledQueryCharge TightEncoding.refinedStructuralEncodingQueryCharge adversary *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        sampledQueryCharge residualPrimitiveQueryCharge adversary *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ := add_le_add le_rfl hresidual
    _ = (sampledQueryCharge TightEncoding.refinedStructuralEncodingQueryCharge adversary +
        sampledQueryCharge residualPrimitiveQueryCharge adversary) *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ := (add_mul ..).symm
    _ ≤ (3 * q : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
      mul_le_mul' (sampled_structural_add_residual_queryCharge_le adversary q hq) le_rfl
    _ = _ := by simp [digestBits]

end SphincsSecurity.Concrete
