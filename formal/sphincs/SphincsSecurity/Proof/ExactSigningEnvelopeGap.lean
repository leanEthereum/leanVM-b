import SphincsSecurity.Proof.ExactRawIndexSigning

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

theorem targetShapeSigning_add_reuse_gap (uniform reuse exactReuse : ENNReal)
    (hreuse : exactReuse ≤ reuse) (f : TargetShapeVector)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetShapeSigning uniform exactReuse f groups remaining +
      (reuse - exactReuse) * targetReuseStep f groups remaining =
      targetShapeSigning uniform reuse f groups remaining := by
  unfold targetShapeSigning
  rw [add_assoc, ← add_mul, add_tsub_cancel_of_le hreuse]

theorem targetShapeEnvelope_signing_add_selection_gaps
    (uniform reuse exactReuse arrival mass : ENNReal) (hmass : mass ≤ 1) (hreuse : exactReuse ≤ reuse)
    (queries signings : Nat) (f : TargetShapeVector)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    targetShapeEnvelope uniform reuse arrival queries signings
        (targetShapeSigning (mass * uniform) exactReuse f) groups remaining +
      ((1 - mass) * uniform) * targetShapeEnvelope uniform reuse arrival queries signings
        (targetFreshSigningIncrement f) groups remaining +
      (reuse - exactReuse) * targetShapeEnvelope uniform reuse arrival queries signings
        (targetReuseStep f) groups remaining +
      signingQueryCommutationGap uniform reuse arrival queries signings f groups remaining =
      targetShapeEnvelope uniform reuse arrival queries (signings + 1) f groups remaining := by
  have hsplit : (fun G R => targetShapeSigning (mass * uniform) exactReuse f G R +
      (reuse - exactReuse) * targetReuseStep f G R) = targetShapeSigning (mass * uniform) reuse f := by
    funext G R
    exact targetShapeSigning_add_reuse_gap _ _ _ hreuse f G R
  have henv := congrArg (fun vector => targetShapeEnvelope uniform reuse arrival queries signings vector groups remaining) hsplit
  rw [targetShapeEnvelope_add, targetShapeEnvelope_mul] at henv
  calc
    _ = (targetShapeEnvelope uniform reuse arrival queries signings
          (targetShapeSigning (mass * uniform) exactReuse f) groups remaining +
        (reuse - exactReuse) * targetShapeEnvelope uniform reuse arrival queries signings
          (targetReuseStep f) groups remaining) +
        ((1 - mass) * uniform) * targetShapeEnvelope uniform reuse arrival queries signings
          (targetFreshSigningIncrement f) groups remaining +
        signingQueryCommutationGap uniform reuse arrival queries signings f groups remaining := by ring
    _ = _ := by
      rw [henv]
      exact targetShapeEnvelope_signing_add_nonfresh_gap uniform reuse arrival mass hmass queries signings f groups remaining hvalid

noncomputable def rawIndexReuseSigningGap (key : SecretKey) (cap queries signings : Nat)
    (state : CoverLogState) (message : Message) : TargetShapeVector :=
  fun G R => (digestReuseWeight cap - exactDigestReuseWeight key message state.1) *
    targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
      queries signings (targetReuseStep (observedRawIndexShapeVector key state)) G R

theorem expected_logTraced_sign_rawIndexEnvelope_add_selection_gaps_le
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
      signingQueryCommutationGap (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (observedRawIndexShapeVector key state) groups remaining ≤
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries (signings + 1) (observedRawIndexShapeVector key state) groups remaining := by
  rw [targetShapeEnvelope_expected]
  have hstep := targetShapeEnvelope_mono (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries signings
    (fun G R hv => expected_logTraced_sign_rawIndexShape_le_exactReuse key state hsigned message G R hv)
    groups remaining hvalid
  exact (add_le_add (add_le_add (add_le_add hstep le_rfl) le_rfl) le_rfl).trans_eq
    (targetShapeEnvelope_signing_add_selection_gaps _ _ _ _ _
      (freshDigestSelectionProbability_le_one key message state.1)
      (exactDigestReuseWeight_le_digestReuseWeight key message state.1 cap hcap hcache)
      queries signings (observedRawIndexShapeVector key state) groups remaining hvalid)

theorem rawIndexNonfreshSigningGap_eq_cached_add_exhaustion
    (key : SecretKey) (cap queries signings : Nat) (state : CoverLogState) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    rawIndexNonfreshSigningGap key cap queries signings state message groups remaining =
      (cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True) *
        exactDigestReuseWeight key message state.1 + digestExhaustionProbability key message state.1) *
        (Fintype.card Index : ENNReal)⁻¹ *
        targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
          queries signings (targetFreshSigningIncrement (observedRawIndexShapeVector key state)) groups remaining := by
  unfold rawIndexNonfreshSigningGap
  have hmass : 1 - freshDigestSelectionProbability key message state.1 =
      cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True) *
        exactDigestReuseWeight key message state.1 + digestExhaustionProbability key message state.1 := by
    apply ENNReal.sub_eq_of_eq_add_rev' (by simp)
    simpa only [add_assoc] using (freshSelection_add_count_exactWeight_add_exhaustion key message state.1).symm
  rw [hmass]

theorem rawIndexSelectionGaps_ge_reuse_mul_min_add_exhaustion
    (key : SecretKey) (cap queries signings : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    let fresh := (Fintype.card Index : ENNReal)⁻¹ *
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (targetFreshSigningIncrement (observedRawIndexShapeVector key state)) groups remaining
    let reused := targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
      queries signings (targetReuseStep (observedRawIndexShapeVector key state)) groups remaining
    digestReuseWeight cap *
        min (cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True) * fresh) reused +
      digestExhaustionProbability key message state.1 * fresh ≤
      rawIndexNonfreshSigningGap key cap queries signings state message groups remaining +
        rawIndexReuseSigningGap key cap queries signings state message groups remaining := by
  dsimp only
  let fresh := (Fintype.card Index : ENNReal)⁻¹ *
    targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
      queries signings (targetFreshSigningIncrement (observedRawIndexShapeVector key state)) groups remaining
  let reused := targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
    queries signings (targetReuseStep (observedRawIndexShapeVector key state)) groups remaining
  let count := cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True)
  have h := add_le_add
    (mul_le_mul' (le_refl (exactDigestReuseWeight key message state.1)) (min_le_left (count * fresh) reused))
    (mul_le_mul' (le_refl (digestReuseWeight cap - exactDigestReuseWeight key message state.1))
      (min_le_right (count * fresh) reused))
  rw [← add_mul, add_tsub_cancel_of_le
    (exactDigestReuseWeight_le_digestReuseWeight key message state.1 cap hcap hcache)] at h
  have hsum := add_le_add h (le_refl (digestExhaustionProbability key message state.1 * fresh))
  rw [rawIndexNonfreshSigningGap_eq_cached_add_exhaustion, rawIndexReuseSigningGap]
  dsimp only [fresh, reused, count] at hsum
  convert hsum using 1 <;> first | rfl | ring

end SphincsSecurity.Concrete
