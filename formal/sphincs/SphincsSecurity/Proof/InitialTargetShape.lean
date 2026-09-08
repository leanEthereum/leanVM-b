import SphincsSecurity.Proof.TargetIndexEnvelope127

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem targetShapeMoments_initial (key : SecretKey) (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (payload : HashInput) (target : FewTimeView) :
    targetShapeMoments key cache [] payload target =
      fun groups remaining => (Fintype.card Index : ENNReal)⁻¹ * liftTargetIndexVector initialTargetIndexVector groups remaining := by
  have hlog (tree : FtsTree) : normalizedTargetLogMatch key cache [] payload target tree = 0 := by
    simp [normalizedTargetLogMatch, targetTreeMatchCount]
  have hindex : (Fintype.card Index : ENNReal)⁻¹ * Fintype.card Index = 1 := by
    exact ENNReal.inv_mul_cancel (by norm_num [Index, totalHeight]) (by finiteness)
  funext groups remaining
  simp only [targetShapeMoments, normalizedCachedTargetSubsetMatch_eq_weight,
    cacheMessageWeight_of_no_message key.parameter _ cache hnone, normalizedTargetLogProduct, hlog,
    Finset.prod_const, liftTargetIndexVector, initialTargetIndexVector]
  by_cases hg : groups = ∅ <;> by_cases hr : remaining = ∅ <;> simp [hg, hr]
  simpa only [Index, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using hindex.symm

attribute [local irreducible] targetShapeMoments targetShapeEnvelope targetIndexEnvelope targetIndexMoments

theorem TargetShapeValid.empty (remaining : Finset FtsTree) : TargetShapeValid ∅ remaining := by
  constructor <;> intro group hgroup <;> exact (Finset.notMem_empty group hgroup).elim

private theorem envelope_of_eq_scalar_index
    (uniform reuse arrival scalar : ENNReal) (queries signings : Nat)
    (shape : TargetShapeVector) (index : TargetIndexVector)
    (heq : shape = fun groups remaining => scalar * liftTargetIndexVector index groups remaining)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    targetShapeEnvelope uniform reuse arrival queries signings shape groups remaining =
      scalar * targetIndexEnvelope uniform reuse arrival queries signings index groups.card remaining.card := by
  rw [heq, targetShapeEnvelope_mul, targetShapeEnvelope_lift uniform reuse arrival queries signings index groups remaining hvalid]

theorem targetShapeEnvelope_initial (key : SecretKey) (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (payload : HashInput) (target : FewTimeView) (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    targetShapeEnvelope uniform reuse arrival queries signings (targetShapeMoments key cache [] payload target) groups remaining =
      (Fintype.card Index : ENNReal)⁻¹ *
        targetIndexEnvelope uniform reuse arrival queries signings initialTargetIndexVector groups.card remaining.card := by
  exact envelope_of_eq_scalar_index uniform reuse arrival (Fintype.card Index : ENNReal)⁻¹ queries signings
    (targetShapeMoments key cache [] payload target) initialTargetIndexVector
    (targetShapeMoments_initial key cache hnone payload target) groups remaining hvalid

theorem initialTargetShape_scaled_le_signingAllowance (key : SecretKey) (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (reference : HashInput) (source : FewTimeView) (q : Nat) (hq : q ≤ 2 ^ 127) :
    targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) q signatureLimit
      (targetShapeMoments key cache [] reference source) ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ ≤
        28504 * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [targetShapeEnvelope_initial key cache hnone reference source _ _ _ _ _ ∅ Finset.univ (TargetShapeValid.empty _)]
  have hcard : (Finset.univ : Finset FtsTree).card = 14 := by norm_num [FtsTree, ftsTrees]
  rw [Finset.card_empty, hcard]
  have hshape := mul_le_mul'
    (mul_le_mul' (le_refl ((Fintype.card Index : ENNReal)⁻¹)) (initialTargetIndexEnvelope_le_127 q hq))
    (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹))
  have hnumeric : (Fintype.card Index : ENNReal)⁻¹ * ((29 : ENNReal) * 2 ^ 43) * ((2 ^ 140 : Nat) : ENNReal)⁻¹ ≤
      28504 * (Fintype.card Digest : ENNReal)⁻¹ := by
    have hi : Fintype.card Index = 2 ^ 26 := by simp [Index, totalHeight]
    have hd : Fintype.card Digest = 2 ^ 128 := by simp [Digest, digestBits]
    rw [hi, hd]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]
  exact hshape.trans hnumeric

end SphincsSecurity.Concrete
