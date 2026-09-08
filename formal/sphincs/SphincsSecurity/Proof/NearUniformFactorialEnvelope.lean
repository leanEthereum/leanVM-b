import SphincsSecurity.Proof.NearUniformSigningOrder
import SphincsSecurity.Proof.SigningFactorialEnvelope
import SphincsSecurity.Proof.IndexDifferenceEnvelope
import SphincsSecurity.Proof.IndexDifferenceInitial

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def finiteNearUniformInitialMixedEnvelope (q : Nat) : ENNReal :=
  ∑ degree ∈ Finset.range 29, (signatureLimit.choose degree : ENNReal) *
    (mixedSigningIncrement (Fintype.card Index : ENNReal)⁻¹ nearUniformDigestReuseWeight)^[degree]
      (finiteMixedQueryEnvelope (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) q
        initialMixedDerivativeVector) 0 0

theorem initialNearUniformTargetIndexEnvelope_eq_finite (q : Nat) :
    targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ nearUniformDigestReuseWeight
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) q signatureLimit
      initialTargetIndexVector 0 14 = finiteNearUniformInitialMixedEnvelope q := by
  rw [targetIndexEnvelope_fourteen_eq_mixed, indexDifferenceTransform_initial]
  simpa only [finiteNearUniformInitialMixedEnvelope, div_eq_mul_inv] using
    mixedRemainingEnvelope_zero_zero_eq_finite (Fintype.card Index : ENNReal)⁻¹ nearUniformDigestReuseWeight
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) q signatureLimit
      initialMixedDerivativeVector initialMixedDerivativeVector_order_zero

noncomputable def nearUniformSigningFactorialEnvelope : ENNReal :=
  ∑ degree ∈ Finset.range 29, (nearUniformSigningOrderMajorant^[degree]
    (fun order => (1025 / 1024 : ENNReal) * initialMixedDerivativeVector 0 order)) 0 / (degree.factorial : ENNReal)

theorem finiteNearUniformInitialMixedEnvelope_le_signingFactorial (q : Nat) (hq : q ≤ 2 ^ 127) :
    finiteNearUniformInitialMixedEnvelope q ≤ nearUniformSigningFactorialEnvelope := by
  unfold finiteNearUniformInitialMixedEnvelope nearUniformSigningFactorialEnvelope
  apply Finset.sum_le_sum
  intro degree _
  let moments := finiteMixedQueryEnvelope
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) q initialMixedDerivativeVector
  have hdom : MixedOrderDominated moments (fun order => (1025 / 1024 : ENNReal) * initialMixedDerivativeVector 0 order) := by
    dsimp only [moments]
    rw [← mixedQueryEnvelope_iterate_eq_finite]
    exact queryInitial_mixedOrderDominated q hq
  have hscaled := (nearUniformMixedSigningIncrement_iterate_dominated moments _ hdom degree).bound 0 0 le_rfl
  simp only [pow_zero, one_mul] at hscaled
  have hscale := congrArg (fun v => v 0 0) (mixedSigningIncrement_iterate_scale
    (Fintype.card Index : ENNReal)⁻¹ nearUniformDigestReuseWeight (signatureLimit : ENNReal) moments degree)
  rw [signatureLimit_uniform_scaled] at hscale
  dsimp only at hscale
  calc
    _ ≤ ((signatureLimit : ENNReal) ^ degree / (degree.factorial : ENNReal)) *
        (mixedSigningIncrement (Fintype.card Index : ENNReal)⁻¹ nearUniformDigestReuseWeight)^[degree] moments 0 0 :=
      mul_le_mul_left (ennreal_choose_le_pow_div_factorial signatureLimit degree) _
    _ = ((signatureLimit : ENNReal) ^ degree *
        (mixedSigningIncrement (Fintype.card Index : ENNReal)⁻¹ nearUniformDigestReuseWeight)^[degree] moments 0 0) / (degree.factorial : ENNReal) := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ _ := ENNReal.div_le_div_right (by rw [← hscale]; exact hscaled) _

end SphincsSecurity.Concrete
