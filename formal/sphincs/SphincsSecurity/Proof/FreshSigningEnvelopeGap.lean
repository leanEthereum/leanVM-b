import SphincsSecurity.Proof.SigningRawIndexGap

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def targetFreshSigningIncrement (f : TargetShapeVector) : TargetShapeVector :=
  fun G R => targetCacheLower f G R + targetTreeLower f G R +
    targetCacheLower (targetTreeLower f) G R

theorem targetShapeEnvelope_add (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (f g : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetShapeEnvelope uniform reuse arrival queries signings (fun G R => f G R + g G R) groups remaining =
      targetShapeEnvelope uniform reuse arrival queries signings f groups remaining +
        targetShapeEnvelope uniform reuse arrival queries signings g groups remaining := by
  simpa using targetShapeEnvelope_tsum uniform reuse arrival queries signings
    (fun b : Bool => if b then f else g) groups remaining

theorem targetShapeSigning_add_nonfresh (uniform reuse mass : ENNReal) (hmass : mass ≤ 1)
    (f : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetShapeSigning (mass * uniform) reuse f groups remaining +
      ((1 - mass) * uniform) * targetFreshSigningIncrement f groups remaining =
      targetShapeSigning uniform reuse f groups remaining := by
  unfold targetShapeSigning targetFreshSigningIncrement
  calc
    _ = f groups remaining + (mass + (1 - mass)) * uniform *
        (targetCacheLower f groups remaining + targetTreeLower f groups remaining +
          targetCacheLower (targetTreeLower f) groups remaining) +
        reuse * targetReuseStep f groups remaining := by ring
    _ = _ := by rw [add_tsub_cancel_of_le hmass, one_mul]

theorem targetShapeEnvelope_signing_add_nonfresh_gap
    (uniform reuse arrival mass : ENNReal) (hmass : mass ≤ 1) (queries signings : Nat)
    (f : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (hvalid : TargetShapeValid groups remaining) :
    targetShapeEnvelope uniform reuse arrival queries signings
        (targetShapeSigning (mass * uniform) reuse f) groups remaining +
      ((1 - mass) * uniform) * targetShapeEnvelope uniform reuse arrival queries signings
        (targetFreshSigningIncrement f) groups remaining +
      signingQueryCommutationGap uniform reuse arrival queries signings f groups remaining =
      targetShapeEnvelope uniform reuse arrival queries (signings + 1) f groups remaining := by
  have hsplit : (fun G R => targetShapeSigning (mass * uniform) reuse f G R +
      ((1 - mass) * uniform) * targetFreshSigningIncrement f G R) =
      targetShapeSigning uniform reuse f := by
    funext G R
    exact targetShapeSigning_add_nonfresh uniform reuse mass hmass f G R
  calc
    _ = targetShapeEnvelope uniform reuse arrival queries signings
        (fun G R => targetShapeSigning (mass * uniform) reuse f G R +
          ((1 - mass) * uniform) * targetFreshSigningIncrement f G R) groups remaining +
        signingQueryCommutationGap uniform reuse arrival queries signings f groups remaining := by
      rw [targetShapeEnvelope_add, targetShapeEnvelope_mul]
    _ = _ := by
      rw [hsplit]
      exact targetShapeEnvelope_signing_gap uniform reuse arrival queries signings f groups remaining hvalid

noncomputable def rawIndexNonfreshSigningGap (key : SecretKey) (cap queries signings : Nat)
    (state : CoverLogState) (message : Message) : TargetShapeVector :=
  fun G R => ((1 - freshDigestSelectionProbability key message state.1) *
    (Fintype.card Index : ENNReal)⁻¹) *
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (targetFreshSigningIncrement (observedRawIndexShapeVector key state)) G R

theorem expected_logTraced_sign_rawIndexEnvelope_add_nonfresh_gap_le
    (key : SecretKey) (cap queries signings : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (observedRawIndexShapeVector key result.2) groups remaining) +
      rawIndexNonfreshSigningGap key cap queries signings state message groups remaining +
      signingQueryCommutationGap (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (observedRawIndexShapeVector key state) groups remaining ≤
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries (signings + 1) (observedRawIndexShapeVector key state) groups remaining := by
  rw [targetShapeEnvelope_expected]
  have hstep := targetShapeEnvelope_mono (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries signings
    (fun G R hv => expected_logTraced_sign_rawIndexShape_le_freshMass key cap hcap state
      hsigned hcache message G R hv) groups remaining hvalid
  exact (add_le_add (add_le_add hstep le_rfl) le_rfl).trans_eq
    (targetShapeEnvelope_signing_add_nonfresh_gap _ _ _ _
      (freshDigestSelectionProbability_le_one key message state.1) queries signings
      (observedRawIndexShapeVector key state) groups remaining hvalid)

theorem expected_logTraced_sign_rawIndexCache_add_nonfresh_gap_le
    (key : SecretKey) (cap signings : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (hafter : ∀ result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state),
      QueryCache.enncard result.2.1 ≤ cap)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      rawIndexCacheEnvelope key cap signings result.2 groups remaining) +
      rawIndexNonfreshSigningGap key cap (messageCacheSlotCount key.parameter cap state.1)
        signings state message groups remaining +
      rawIndexSigningGap key cap signings state groups remaining ≤
      rawIndexCacheEnvelope key cap (signings + 1) state groups remaining := by
  let queries := messageCacheSlotCount key.parameter cap state.1
  have hfreeze : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      rawIndexCacheEnvelope key cap signings result.2 groups remaining) ≤
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
        targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
          queries signings (observedRawIndexShapeVector key result.2) groups remaining := by
    apply ENNReal.tsum_le_tsum
    intro result
    by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
    · exact mul_le_mul' le_rfl (targetShapeEnvelope_queries_mono _ _ _ signings _
        (messageCacheSlotCount_antitone key.parameter cap state.1 result.2.1
          (logTracedMappedAdversaryImpl_cache_le key (.inr message) state result hr)
          (Finite.of_enncard_le (hafter result hr))) groups remaining hvalid)
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
  exact (add_le_add (add_le_add hfreeze le_rfl) le_rfl).trans
    (expected_logTraced_sign_rawIndexEnvelope_add_nonfresh_gap_le key cap queries signings hcap
      state hsigned hcache message groups remaining hvalid)

end SphincsSecurity.Concrete
