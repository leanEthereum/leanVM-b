import SphincsSecurity.Proof.UnmatchedRawIndexSigning
import SphincsSecurity.Proof.ExactSigningEnvelopeGap

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def rawIndexUnmatchedSigningGap (key : SecretKey) (cap queries signings : Nat)
    (state : CoverLogState) (message : Message) : TargetShapeVector :=
  fun G R => exactDigestReuseWeight key message state.1 *
    targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
      queries signings (unmatchedRawIndexShape key message state) G R

theorem expected_logTraced_sign_rawIndexEnvelope_add_unmatched_le
    (key : SecretKey) (cap queries signings : Nat) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (observedRawIndexShapeVector key result.2) groups remaining) +
      rawIndexUnmatchedSigningGap key cap queries signings state message groups remaining ≤
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries signings
        (targetShapeSigning (freshDigestSelectionProbability key message state.1 * (Fintype.card Index : ENNReal)⁻¹)
          (exactDigestReuseWeight key message state.1) (observedRawIndexShapeVector key state)) groups remaining := by
  rw [targetShapeEnvelope_expected, rawIndexUnmatchedSigningGap, ← targetShapeEnvelope_mul, ← targetShapeEnvelope_add]
  exact targetShapeEnvelope_mono _ _ _ queries signings
    (fun G R hv => expected_logTraced_sign_rawIndexShape_add_unmatched_le key state hsigned message G R hv)
    groups remaining hvalid

theorem expected_logTraced_sign_rawIndexEnvelope_add_all_selection_gaps_le
    (key : SecretKey) (cap queries signings : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (observedRawIndexShapeVector key result.2) groups remaining) +
      rawIndexNonfreshSigningGap key cap queries signings state message groups remaining +
      rawIndexReuseSigningGap key cap queries signings state message groups remaining +
      rawIndexUnmatchedSigningGap key cap queries signings state message groups remaining +
      signingQueryCommutationGap (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (observedRawIndexShapeVector key state) groups remaining ≤
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries (signings + 1) (observedRawIndexShapeVector key state) groups remaining := by
  have h := (add_le_add (add_le_add (add_le_add
    (expected_logTraced_sign_rawIndexEnvelope_add_unmatched_le key cap queries signings state hsigned message groups remaining hvalid)
      le_rfl) le_rfl) le_rfl).trans_eq
    (targetShapeEnvelope_signing_add_selection_gaps _ _ _ _ _
      (freshDigestSelectionProbability_le_one key message state.1)
      (exactDigestReuseWeight_le_digestReuseWeight key message state.1 cap hcap hcache)
      queries signings (observedRawIndexShapeVector key state) groups remaining hvalid)
  dsimp only [rawIndexNonfreshSigningGap, rawIndexReuseSigningGap]
  convert h using 1 <;> first | rfl | ring

end SphincsSecurity.Concrete
