import SphincsSecurity.Proof.UpperDigestSelection
import SphincsSecurity.Proof.UnmatchedSigningEnvelopeGap

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

theorem unmatchedCachedSignerWeight_le_all (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (weight : HashInput → FewTimeView → ENNReal) :
    unmatchedCachedSignerWeight key message cache weight ≤ cacheMessageWeight key.parameter weight cache :=
  le_add_of_nonneg_left zero_le |>.trans_eq (cachedSignerWeight_add_unmatched key message cache weight)

theorem cachedSignerInputWeight_eq_zero_of_no_cached_selection (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec)
    (hcount : cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) = 0)
    (weight : HashInput → FewTimeView → ENNReal) (input : HashInput) :
    cachedSignerInputWeight key message cache weight input = 0 := by
  have hempty : cachedMessageInputSetWhere cache key.parameter key.root message (fun _ => True) = ∅ := by
    apply Set.encard_eq_zero.mp
    apply ENat.toENNReal_inj.mp
    simpa only [cachedMessageEntryCountWhere, ENat.toENNReal_zero] using hcount
  unfold cachedSignerInputWeight
  cases hc : cache input with
  | none => rfl
  | some output =>
      dsimp only
      split_ifs with hsource
      · have hmem : (⟨input, output⟩ : (t : HashSpec.Domain) × HashSpec.Range t) ∈
          cachedMessageInputSetWhere cache key.parameter key.root message (fun _ => True) :=
          ⟨⟨hc, hsource.1⟩, (signAttemptResultOfOutput_ne_none_iff output).mpr hsource.2, trivial⟩
        rw [hempty] at hmem
        exact hmem.elim
      · rfl

theorem unmatchedCachedSignerWeight_eq_all_of_no_cached_selection (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec)
    (hcount : cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) = 0)
    (weight : HashInput → FewTimeView → ENNReal) :
    unmatchedCachedSignerWeight key message cache weight = cacheMessageWeight key.parameter weight cache := by
  have h := cachedSignerWeight_add_unmatched key message cache weight
  simpa only [cachedSignerInputWeight_eq_zero_of_no_cached_selection key message cache hcount weight,
    tsum_zero, zero_add] using h

theorem unmatchedRawIndexShape_le_reuse (key : SecretKey) (message : Message) (state : CoverLogState)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    unmatchedRawIndexShape key message state groups remaining ≤
      targetReuseStep (observedRawIndexShapeVector key state) groups remaining := by
  rw [observedRawIndexShapeVector, targetReuseStep_lift _ _ _ hvalid]
  simp only [liftTargetIndexVector, targetIndexReuseStep_eq_cached]
  exact unmatchedCachedSignerWeight_le_all key message state.1 _

theorem unmatchedRawIndexShape_eq_reuse_of_no_cached_selection
    (key : SecretKey) (message : Message) (state : CoverLogState)
    (hcount : cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True) = 0)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    unmatchedRawIndexShape key message state groups remaining =
      targetReuseStep (observedRawIndexShapeVector key state) groups remaining := by
  rw [observedRawIndexShapeVector, targetReuseStep_lift _ _ _ hvalid]
  simp only [liftTargetIndexVector, targetIndexReuseStep_eq_cached]
  exact unmatchedCachedSignerWeight_eq_all_of_no_cached_selection key message state.1 hcount _

theorem rawIndexReuse_add_unmatched_eq_all_of_no_cached_selection
    (key : SecretKey) (cap queries signings : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (hcount : cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True) = 0)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    rawIndexReuseSigningGap key cap queries signings state message groups remaining +
      rawIndexUnmatchedSigningGap key cap queries signings state message groups remaining =
      digestReuseWeight cap * targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (targetReuseStep (observedRawIndexShapeVector key state)) groups remaining := by
  rw [rawIndexReuseSigningGap, rawIndexUnmatchedSigningGap,
    targetShapeEnvelope_congr _ _ _ queries signings
      (fun G R hv => unmatchedRawIndexShape_eq_reuse_of_no_cached_selection key message state hcount G R hv)
      groups remaining hvalid,
    ← add_mul, tsub_add_cancel_of_le (exactDigestReuseWeight_le_digestReuseWeight key message state.1 cap hcap hcache)]

theorem inv_pow118_le_digestReuseWeight (q : Nat) :
    ((2 ^ 118 : Nat) : ENNReal)⁻¹ ≤ digestReuseWeight q := by
  have h := ENNReal.div_le_div_left
    (show (1 - ((q + digestAttemptLimit : Nat) : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
        ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ ≤ ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ from
      mul_le_of_le_one_left' tsub_le_self) (((2 ^ randomnessBits : Nat) : ENNReal)⁻¹)
  apply le_of_eq_of_le ?_ h
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness)
    (ENNReal.div_ne_top (by finiteness) (ENNReal.inv_ne_zero.mpr (by finiteness)))).mp
  norm_num [ENNReal.toReal_div, ENNReal.toReal_inv, randomnessBits, ftsTreeHeight]

theorem selection_mixture_lower (fraction fresh reuse scale total unmatched : ENNReal)
    (hfresh : fresh ≤ 1) (hfraction : fraction ≤ 1 - fresh)
    (hscaleZero : scale ≠ 0) (hscaleTop : scale ≠ ⊤)
    (hreuse : fresh ≤ reuse * scale) (hunmatched : unmatched / scale ≤ total) :
    fraction * total + (1 - fraction) * (unmatched / scale) ≤
      (1 - fresh) * total + reuse * unmatched := by
  have hsplit : fraction + (1 - fresh - fraction) = 1 - fresh := add_tsub_cancel_of_le hfraction
  have hcomplement : 1 - fraction = (1 - fresh - fraction) + fresh := by
    apply ENNReal.sub_eq_of_eq_add_rev' (by simp)
    rw [← add_assoc, hsplit, tsub_add_cancel_of_le hfresh]
  have hweight : fresh * (unmatched / scale) ≤ reuse * unmatched := by
    calc
      _ ≤ (reuse * scale) * (unmatched / scale) := mul_le_mul' hreuse le_rfl
      _ = _ := by
        rw [div_eq_mul_inv]
        calc
          _ = reuse * unmatched * (scale * scale⁻¹) := by ring
          _ = _ := by rw [ENNReal.mul_inv_cancel hscaleZero hscaleTop, mul_one]
  calc
    _ = fraction * total + (1 - fresh - fraction) * (unmatched / scale) + fresh * (unmatched / scale) := by
      rw [hcomplement, add_mul, add_assoc]
    _ ≤ fraction * total + (1 - fresh - fraction) * total + reuse * unmatched :=
      add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hunmatched)) hweight
    _ = _ := by rw [← add_mul, hsplit]

theorem selection_fraction_unmatched_lower (count fresh reuse scale total unmatched : ENNReal)
    (hcount : count ≠ ⊤) (hfresh : fresh ≤ 1) (hfraction : count / (count + scale) ≤ 1 - fresh)
    (hscaleZero : scale ≠ 0) (hscaleTop : scale ≠ ⊤)
    (hreuse : fresh ≤ reuse * scale) (hunmatched : unmatched / scale ≤ total) :
    count / (count + scale) * total + unmatched / (count + scale) ≤
      (1 - fresh) * total + reuse * unmatched := by
  have hdenZero : count + scale ≠ 0 :=
    ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hscaleZero) (le_add_of_nonneg_left zero_le))
  have hdenTop : count + scale ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hcount, hscaleTop⟩
  have hcomplement : 1 - count / (count + scale) = scale / (count + scale) := by
    apply ENNReal.sub_eq_of_eq_add_rev' (by simp)
    rw [← ENNReal.add_div, ENNReal.div_self hdenZero hdenTop]
  have heq : (1 - count / (count + scale)) * (unmatched / scale) = unmatched / (count + scale) := by
    rw [hcomplement]
    simp only [div_eq_mul_inv]
    calc
      _ = unmatched * (count + scale)⁻¹ * (scale * scale⁻¹) := by ring
      _ = _ := by rw [ENNReal.mul_inv_cancel hscaleZero hscaleTop, mul_one]
  have h := selection_mixture_lower (count / (count + scale)) fresh reuse scale total unmatched
    hfresh hfraction hscaleZero hscaleTop hreuse hunmatched
  rwa [heq] at h

end SphincsSecurity.Concrete
