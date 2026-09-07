import SphincsSecurity.Proof.JointProbeOriginalStructuralInitialization
import SphincsSecurity.Proof.EncodingMessageConservation

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] answerPotential answerEncodingPotential encodingMessageReserve
set_option backward.isDefEq.respectTransparency false

noncomputable def structuralTerminalReserve
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool) : ENNReal :=
  if SurvivingStructuralFailure parameter otsTable ftsTable result then 0
  else survivingStructuralPotential (secretKey parameter default otsTable ftsTable)
    result.1.2.1.2 result.1.2.2 result.2

theorem structuralFailure_add_terminalReserve_le_potential
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool)
    (hfinite : Finite result.1.2.1.2) :
    (if SurvivingStructuralFailure parameter otsTable ftsTable result then 1 else 0) +
      structuralTerminalReserve parameter otsTable ftsTable result ≤
      survivingStructuralPotential (secretKey parameter default otsTable ftsTable)
        result.1.2.1.2 result.1.2.2 result.2 := by
  by_cases he : SurvivingStructuralFailure parameter otsTable ftsTable result
  · simp only [structuralTerminalReserve, if_pos he, add_zero]
    obtain ⟨hf, hh | hb⟩ := he
    · simp [survivingStructuralPotential, hf, hh]
    · cases hh : result.1.2.2 with
      | true => simp [survivingStructuralPotential, hf]
      | false =>
          simp only [survivingStructuralPotential, hf, Bool.false_eq_true, if_false]
          exact structuralRecordPotential_none_ge_bad _ _ hfinite hb
  · simp only [structuralTerminalReserve, if_neg he, zero_add, le_refl]

theorem encodingMessageReserve_le_terminalReserve
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool)
    (hfinite : Finite result.1.2.1.2) (hh : result.1.2.2 = false) (hf : result.2 = false)
    (hclean : ¬ SurvivingStructuralFailure parameter otsTable ftsTable result) :
    min 1 ((encodingMessageReserve result.1.2.1.2 (secretKey parameter default otsTable ftsTable) : ENNReal) *
      (Fintype.card Digest : ENNReal)⁻¹) ≤ structuralTerminalReserve parameter otsTable ftsTable result := by
  let key := secretKey parameter default otsTable ftsTable
  have hbad : ¬ Bad key.parameter key.otsSecret key.ftsSecret result.1.2.1.2 :=
    fun hb => hclean ⟨hf, Or.inr (Or.inl hb)⟩
  simp only [structuralTerminalReserve, if_neg hclean, survivingStructuralPotential, hf, hh,
    Bool.false_eq_true, if_false, structuralRecordPotential, answerEncodingMonitorPotential,
    Option.isSome_none, answerEncodingAdaptivePotential_eq hfinite]
  apply le_trans _ le_self_add
  rw [answerEncodingTotalPotential, if_neg hbad]
  apply min_le_min_left 1
  apply le_trans _ le_self_add
  apply mul_le_mul' _ le_rfl
  apply Nat.cast_le.mpr
  rw [answerEncodingPotential]
  exact Nat.le_add_left _ _

theorem encodingMessageReserve_scaled_le_terminalReserve
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool)
    (hfinite : Finite result.1.2.1.2) (hh : result.1.2.2 = false) (hf : result.2 = false)
    (hclean : ¬ SurvivingStructuralFailure parameter otsTable ftsTable result)
    (hcap : QueryCache.enncard result.1.2.1.2 ≤ (Fintype.card Digest : ENNReal)) :
    (encodingMessageReserve result.1.2.1.2 (secretKey parameter default otsTable ftsTable) : ENNReal) *
      (Fintype.card Digest : ENNReal)⁻¹ ≤ structuralTerminalReserve parameter otsTable ftsTable result := by
  have hreserve : (encodingMessageReserve result.1.2.1.2 (secretKey parameter default otsTable ftsTable) : ENNReal) ≤
      (Fintype.card Digest : ENNReal) := by
    have h := Nat.cast_le (α := ENNReal).mpr (encodingMessageReserve_le_cachedInputs hfinite
      (secretKey parameter default otsTable ftsTable))
    rw [hfinite.cachedInputs_ncard_toENNReal_eq_enncard] at h
    exact h.trans hcap
  have hsmall : (encodingMessageReserve result.1.2.1.2 (secretKey parameter default otsTable ftsTable) : ENNReal) *
      (Fintype.card Digest : ENNReal)⁻¹ ≤ 1 := by
    apply (mul_le_mul' hreserve le_rfl).trans_eq
    exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (by finiteness)
  simpa only [min_eq_right hsmall] using
    encodingMessageReserve_le_terminalReserve parameter otsTable ftsTable result hfinite hh hf hclean

noncomputable def initializedStructuralTerminalReserve
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : ENNReal :=
  ∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable)
    adversary parameter otsTable ftsTable q fuel] * structuralTerminalReserve parameter otsTable ftsTable result

theorem probEvent_structuralFailure_add_terminalReserve_le_beforeFailureCharge
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    Pr[SurvivingStructuralFailure parameter otsTable ftsTable |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] +
      initializedStructuralTerminalReserve adversary parameter otsTable ftsTable q fuel ≤
      initializedBeforeFailureStructuralCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ := by
  apply le_trans _ (expected_survivingStructuralPotential_retained_le adversary parameter otsTable ftsTable q fuel)
  rw [probEvent_eq_tsum_ite, initializedStructuralTerminalReserve, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable)
      adversary parameter otsTable ftsTable q fuel)
  · have h := mul_le_mul' (le_refl (Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable)
        adversary parameter otsTable ftsTable q fuel]))
      (structuralFailure_add_terminalReserve_le_potential parameter otsTable ftsTable result
        (runRetainedWithFailure_cache_finite _ adversary parameter otsTable ftsTable q fuel result hr))
    simpa only [mul_add, mul_ite, mul_one, mul_zero] using h
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    split_ifs <;> simp

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
