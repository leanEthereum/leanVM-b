import SphincsSecurity.Proof.JointProbeCollisionInitialization
import SphincsSecurity.Proof.StructuralCacheCount

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] answerPotential parentReserve collisionAnswerEncodingPotential
set_option backward.isDefEq.respectTransparency false

noncomputable def collisionTerminalReserve
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool) : ENNReal :=
  if SurvivingStructuralFailure parameter otsTable ftsTable result then 0
  else collisionSurvivingStructuralPotential (secretKey parameter default otsTable ftsTable)
    result.1.2.1.2 result.1.2.2 result.2

theorem structuralFailure_add_collisionTerminalReserve_le_potential
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool)
    (hfinite : Finite result.1.2.1.2) :
    (if SurvivingStructuralFailure parameter otsTable ftsTable result then 1 else 0) +
      collisionTerminalReserve parameter otsTable ftsTable result ≤
      collisionSurvivingStructuralPotential (secretKey parameter default otsTable ftsTable)
        result.1.2.1.2 result.1.2.2 result.2 := by
  by_cases he : SurvivingStructuralFailure parameter otsTable ftsTable result
  · simp only [collisionTerminalReserve, if_pos he, add_zero]
    obtain ⟨hf, hh | hb⟩ := he
    · simp [collisionSurvivingStructuralPotential, hf, hh]
    · cases hh : result.1.2.2 with
      | true => simp [collisionSurvivingStructuralPotential, hf]
      | false =>
          simp only [collisionSurvivingStructuralPotential, hf, Bool.false_eq_true, if_false]
          exact collisionStructuralRecordPotential_none_ge_bad _ _ hfinite hb
  · simp only [collisionTerminalReserve, if_neg he, zero_add, le_refl]

theorem answer_parent_reserves_le_collisionRecordPotential
    (key : SecretKey) (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    min 1 ((answerPotential key.parameter key.otsSecret key.ftsSecret cache : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) +
      (parentReserve key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) cache : ENNReal) *
        (Fintype.card Digest : ENNReal)⁻¹ ≤ collisionStructuralRecordPotential key cache none := by
  simp only [collisionStructuralRecordPotential, collisionAnswerEncodingMonitorPotential, Option.isSome_none,
    Bool.false_eq_true, if_false, collisionAnswerEncodingAdaptivePotential_eq hfinite,
    ftsParentSelectionPotential, firstExceptionSelectionPotential]
  apply add_le_add ?_ le_rfl
  rw [collisionAnswerEncodingTotalPotential]
  split_ifs
  · exact min_le_left _ _
  · apply min_le_min_left 1
    apply le_trans ?_ le_self_add
    apply mul_le_mul' ?_ le_rfl
    apply Nat.cast_le.mpr
    rw [collisionAnswerEncodingPotential]
    exact Nat.le_add_right _ _

theorem answer_parent_reserves_scaled_le_collisionTerminalReserve
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool)
    (hfinite : Finite result.1.2.1.2) (hh : result.1.2.2 = false) (hf : result.2 = false)
    (hclean : ¬ SurvivingStructuralFailure parameter otsTable ftsTable result)
    (hcap : QueryCache.enncard result.1.2.1.2 ≤ (Fintype.card Digest : ENNReal)) :
    ((answerPotential parameter (secretKey parameter default otsTable ftsTable).otsSecret
        (secretKey parameter default otsTable ftsTable).ftsSecret result.1.2.1.2 : ENNReal) +
      (parentReserve parameter (secretKey parameter default otsTable ftsTable).otsSecret
        (secretKey parameter default otsTable ftsTable).ftsSecret
        (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) result.1.2.1.2 : ENNReal)) *
      (Fintype.card Digest : ENNReal)⁻¹ ≤ collisionTerminalReserve parameter otsTable ftsTable result := by
  let key := secretKey parameter default otsTable ftsTable
  have hanswer : (answerPotential parameter key.otsSecret key.ftsSecret result.1.2.1.2 : ENNReal) ≤
      (Fintype.card Digest : ENNReal) := by
    have h := Nat.cast_le (α := ENNReal).mpr (answerPotential_le_cachedInputs parameter key.otsSecret key.ftsSecret hfinite)
    rw [hfinite.cachedInputs_ncard_toENNReal_eq_enncard] at h
    exact h.trans hcap
  have hsmall : (answerPotential parameter key.otsSecret key.ftsSecret result.1.2.1.2 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ ≤ 1 :=
    (mul_le_mul' hanswer le_rfl).trans_eq (ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (by finiteness))
  have h := answer_parent_reserves_le_collisionRecordPotential key result.1.2.1.2 hfinite
  rw [show key.parameter = parameter from rfl] at h
  rw [min_eq_right hsmall] at h
  simpa only [collisionTerminalReserve, if_neg hclean, collisionSurvivingStructuralPotential, hf, hh,
    Bool.false_eq_true, if_false, add_mul] using h

theorem twice_parentReserve_scaled_le_collisionTerminalReserve
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool)
    (hfinite : Finite result.1.2.1.2) (hh : result.1.2.2 = false) (hf : result.2 = false)
    (hclean : ¬ SurvivingStructuralFailure parameter otsTable ftsTable result)
    (hcap : QueryCache.enncard result.1.2.1.2 ≤ (Fintype.card Digest : ENNReal)) :
    2 * (parentReserve parameter (secretKey parameter default otsTable ftsTable).otsSecret
      (secretKey parameter default otsTable ftsTable).ftsSecret
      (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) result.1.2.1.2 : ENNReal) *
      (Fintype.card Digest : ENNReal)⁻¹ ≤ collisionTerminalReserve parameter otsTable ftsTable result := by
  apply le_trans ?_ (answer_parent_reserves_scaled_le_collisionTerminalReserve parameter otsTable ftsTable result hfinite hh hf hclean hcap)
  rw [two_mul]
  apply mul_le_mul' ?_ le_rfl
  apply add_le_add ?_ le_rfl
  exact Nat.cast_le.mpr (parentReserve_le_answerPotential parameter _ _ _ _)

noncomputable def initializedCollisionTerminalReserve
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : ENNReal :=
  ∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable)
    adversary parameter otsTable ftsTable q fuel] * collisionTerminalReserve parameter otsTable ftsTable result

theorem probEvent_structuralFailure_add_terminalReserve_le_beforeFailureCollisionCharge
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    Pr[SurvivingStructuralFailure parameter otsTable ftsTable |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] +
      initializedCollisionTerminalReserve adversary parameter otsTable ftsTable q fuel ≤
      initializedBeforeFailureCollisionCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ := by
  apply le_trans _ (expected_collisionSurvivingStructuralPotential_retained_le adversary parameter otsTable ftsTable q fuel)
  rw [probEvent_eq_tsum_ite, initializedCollisionTerminalReserve, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable)
      adversary parameter otsTable ftsTable q fuel)
  · have h := mul_le_mul' (le_refl (Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable)
        adversary parameter otsTable ftsTable q fuel]))
      (structuralFailure_add_collisionTerminalReserve_le_potential parameter otsTable ftsTable result
        (runRetainedWithFailure_cache_finite _ adversary parameter otsTable ftsTable q fuel result hr))
    simpa only [mul_add, mul_ite, mul_one, mul_zero] using h
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    split_ifs <;> simp

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
