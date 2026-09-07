import SphincsSecurity.Proof.CachedTargetEnvelope127

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem targetShapeMoments_full_le_targetCacheEnvelope (key : SecretKey) (q signatures : Nat)
    (state : CoverLogState) (payload : HashInput) (target : FewTimeView) :
    targetShapeMoments key state.1 state.2 payload target ∅ Finset.univ ≤
      targetCacheEnvelope key q payload target signatures state ∅ Finset.univ :=
  le_targetShapeEnvelope _ _ _ _ _ _ ∅ Finset.univ

theorem normalizedTargetLogProduct_full_ge_of_covered (key : SecretKey) (state : CoverLogState)
    (payload : HashInput) (target : FewTimeView)
    (hcover : CoveredFewTimeView (eligibleSigningViews (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root payload state.2) target) :
    ((2 ^ 140 : Nat) : ENNReal) ≤ normalizedTargetLogProduct key state.1 state.2 payload target Finset.univ := by
  have hpower : (Fintype.card FtsLeaf : ENNReal) ^ Fintype.card FtsTree = ((2 ^ 140 : Nat) : ENNReal) := by
    norm_num [FtsLeaf, FtsTree, ftsTreeHeight, ftsTrees]
  calc
    _ = ∏ _tree : FtsTree, (Fintype.card FtsLeaf : ENNReal) := by rw [Finset.prod_const, Finset.card_univ, hpower]
    _ ≤ _ := by
      apply Finset.prod_le_prod'
      intro tree _
      apply le_mul_of_one_le_right'
      exact_mod_cast Nat.succ_le_iff.mpr ((targetTreeMatchCount_pos_iff _ target tree).mpr (hcover tree))

theorem one_le_cappedCachedTargetEnvelope_scaled_of_covered (key : SecretKey) (q : Nat) (state : CoverLogState)
    (hvalid : SigningTranscript.Valid state.2) (hcover : SigningCacheCovered key.parameter key.root state.1 state.2) :
    1 ≤ cappedCachedTargetEnvelope key q state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ := by
  obtain ⟨input, output, hmessage, houtput, hadmissible, hcovered⟩ := hcover
  have hrow := normalizedTargetLogProduct_full_ge_of_covered key state (payloadOf input) (hashOutputFewTimeView output) hcovered
  have hmoment : ((2 ^ 140 : Nat) : ENNReal) ≤ targetShapeMoments key state.1 state.2 (payloadOf input) (hashOutputFewTimeView output) ∅ Finset.univ := by
    simpa only [targetShapeMoments, Finset.prod_empty, one_mul] using hrow
  have hentry : ((2 ^ 140 : Nat) : ENNReal) ≤ cacheMessageEntryWeight key.parameter
      (fun query target => targetCacheEnvelope key q (payloadOf query) target (signatureLimit - state.2.length) state ∅ Finset.univ) state.1 input := by
    simp only [cacheMessageEntryWeight, houtput, hmessage, hadmissible, and_self, if_true]
    exact hmoment.trans (targetShapeMoments_full_le_targetCacheEnvelope key q _ state _ _)
  have htotal : ((2 ^ 140 : Nat) : ENNReal) ≤ cappedCachedTargetEnvelope key q state ∅ Finset.univ := by
    rw [cappedCachedTargetEnvelope, if_pos hvalid]
    exact hentry.trans (ENNReal.le_tsum input)
  have hpositive : ((2 ^ 140 : Nat) : ENNReal) ≠ 0 := by norm_num
  have hfinite : ((2 ^ 140 : Nat) : ENNReal) ≠ ∞ := by finiteness
  rw [← ENNReal.mul_inv_cancel hpositive hfinite]
  exact mul_le_mul' htotal le_rfl

end SphincsSecurity.Concrete
