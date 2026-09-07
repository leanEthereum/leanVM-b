import SphincsSecurity.Proof.SigningOrderMajorant

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
set_option backward.isDefEq.respectTransparency false

theorem mixedSigningIncrement_scale (uniform reuse scalar : ENNReal) (moments : MixedMomentVector) :
    mixedSigningIncrement (scalar * uniform) (scalar * reuse) moments =
      fun p o => scalar * mixedSigningIncrement uniform reuse moments p o := by
  funext power order
  simp only [mixedSigningIncrement]
  ring

theorem mixedSigningIncrement_iterate_scale (uniform reuse scalar : ENNReal) (moments : MixedMomentVector) (steps : Nat) :
    (mixedSigningIncrement (scalar * uniform) (scalar * reuse))^[steps] moments =
      fun p o => scalar ^ steps * (mixedSigningIncrement uniform reuse)^[steps] moments p o := by
  induction steps with
  | zero => funext p o; simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
  | succ steps ih =>
      rw [Function.iterate_succ_apply', ih, mixedSigningIncrement_scale, mixedSigningIncrement_mul]
      funext power order
      simp only [Function.iterate_succ_apply', pow_succ]
      ring

theorem signatureLimit_uniform_scaled : (signatureLimit : ENNReal) * (Fintype.card Index : ENNReal)⁻¹ = 1 / 4 := by
  have hindex : (Fintype.card Index : ENNReal) ≠ 0 := by norm_num [Index, totalHeight]
  have hleft : (signatureLimit : ENNReal) * (Fintype.card Index : ENNReal)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top signatureLimit) (ENNReal.inv_ne_top.mpr hindex)
  have hright : (1 / 4 : ENNReal) ≠ ∞ := by norm_num
  apply (ENNReal.toReal_eq_toReal_iff' hleft hright).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, signatureLimit, Index, totalHeight]

noncomputable def signingFactorialEnvelope : ENNReal :=
  ∑ degree ∈ Finset.range 29, (signingOrderMajorant^[degree]
    (fun order => (1025 / 1024 : ENNReal) * initialMixedDerivativeVector 0 order)) 0 / (degree.factorial : ENNReal)

theorem finiteInitialMixedEnvelope_le_signingFactorial (q : Nat) (hq : q ≤ 2 ^ 127) :
    finiteInitialMixedEnvelope q ≤ signingFactorialEnvelope := by
  unfold finiteInitialMixedEnvelope signingFactorialEnvelope
  apply Finset.sum_le_sum
  intro degree _
  let moments := finiteMixedQueryEnvelope
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) q initialMixedDerivativeVector
  have hdom : MixedOrderDominated moments (fun order => (1025 / 1024 : ENNReal) * initialMixedDerivativeVector 0 order) := by
    dsimp only [moments]
    rw [← mixedQueryEnvelope_iterate_eq_finite]
    exact queryInitial_mixedOrderDominated q hq
  have hscaled := (mixedSigningIncrement_iterate_dominated q hq moments _ hdom degree).bound 0 0 le_rfl
  simp only [pow_zero, one_mul] at hscaled
  have hscale := congrArg (fun v => v 0 0) (mixedSigningIncrement_iterate_scale
    (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q) (signatureLimit : ENNReal) moments degree)
  rw [signatureLimit_uniform_scaled] at hscale
  dsimp only at hscale
  calc
    _ ≤ ((signatureLimit : ENNReal) ^ degree / (degree.factorial : ENNReal)) *
        (mixedSigningIncrement (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q))^[degree] moments 0 0 :=
      mul_le_mul_left (ennreal_choose_le_pow_div_factorial signatureLimit degree) _
    _ = ((signatureLimit : ENNReal) ^ degree *
        (mixedSigningIncrement (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q))^[degree] moments 0 0) / (degree.factorial : ENNReal) := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ _ := ENNReal.div_le_div_right (by rw [← hscale]; exact hscaled) _

theorem expected_adaptive_validOccupancy_le_signingFactorial {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      (if SigningTranscript.Valid result.2.2 then observedLogOccupancy key result.2 else 0)) ≤ signingFactorialEnvelope :=
  (expected_adaptive_validOccupancy_le_finiteInitialEnvelope key q hq computation cache hnone hbudget).trans
    (finiteInitialMixedEnvelope_le_signingFactorial q hq)

end SphincsSecurity.Concrete
