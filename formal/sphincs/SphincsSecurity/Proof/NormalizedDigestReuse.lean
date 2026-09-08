import SphincsSecurity.Proof.MessageFreshSelectionScale
import SphincsSecurity.Proof.UnmatchedSelectionWeight

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def normalizedDigestReuseWeight (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (q : Nat) : ENNReal :=
  digestReuseWeight q /
    (1 + cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * digestReuseWeight q)

private theorem matchingCount_ne_top (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (q : Nat) (hcache : QueryCache.enncard cache ≤ q) :
    cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) ≠ ⊤ :=
  ne_top_of_le_ne_top (by finiteness)
    ((cachedMessageEntryCountWhere_le_enncard cache key.parameter key.root message (fun _ => True)).trans hcache)

theorem normalizedDigestReuseWeight_le (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (q : Nat) :
    normalizedDigestReuseWeight key message cache q ≤ digestReuseWeight q := by
  unfold normalizedDigestReuseWeight
  exact (ENNReal.div_le_div_left (show (1 : ENNReal) ≤ 1 +
    cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * digestReuseWeight q from le_self_add) _).trans_eq
      (div_one _)

theorem normalizedDigestReuseWeight_ne_top (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) : normalizedDigestReuseWeight key message cache q ≠ ⊤ :=
  ne_top_of_le_ne_top (digestReuseWeight_ne_top q hq) (normalizedDigestReuseWeight_le key message cache q)

theorem normalizedDigestReuseWeight_add_cached (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    normalizedDigestReuseWeight key message cache q +
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * digestReuseWeight q *
        normalizedDigestReuseWeight key message cache q = digestReuseWeight q := by
  have hcount := matchingCount_ne_top key message cache q hcache
  have hreuse := digestReuseWeight_ne_top q hq
  unfold normalizedDigestReuseWeight
  calc
    _ = (digestReuseWeight q /
        (1 + cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * digestReuseWeight q)) *
        (1 + cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * digestReuseWeight q) := by ring
    _ = _ := ENNReal.div_mul_cancel (by positivity) (by finiteness)

theorem exactDigestReuseWeight_le_normalized (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    exactDigestReuseWeight key message cache ≤ normalizedDigestReuseWeight key message cache q := by
  have hcount := matchingCount_ne_top key message cache q hcache
  have hreuse := digestReuseWeight_ne_top q hq
  have hmass : freshDigestSelectionProbability key message cache +
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache ≤ 1 :=
    le_self_add.trans_eq (freshSelection_add_count_exactWeight_add_exhaustion key message cache)
  unfold normalizedDigestReuseWeight
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
  calc
    _ = exactDigestReuseWeight key message cache +
        (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          digestReuseWeight q := by ring
    _ ≤ freshDigestSelectionProbability key message cache * digestReuseWeight q +
        (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          digestReuseWeight q :=
      add_le_add (exactDigestReuseWeight_le_fresh_mul_digestReuseWeight key message cache q hq hcache) le_rfl
    _ = (freshDigestSelectionProbability key message cache +
        cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          digestReuseWeight q := by rw [add_mul]
    _ ≤ _ := mul_le_of_le_one_left' hmass

theorem inv_matchingCount_add_scale_le_normalized (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) + messageFreshSelectionScale key message cache)⁻¹ ≤
      normalizedDigestReuseWeight key message cache q := by
  let count := cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True)
  let scale := messageFreshSelectionScale key message cache
  have hcount := matchingCount_ne_top key message cache q hcache
  have hreuse := digestReuseWeight_ne_top q hq
  have hscaleZero : scale ≠ 0 := ne_of_gt (messageFreshSelectionScale_pos key message cache q hq hcache)
  have hscaleTop : scale ≠ ⊤ := messageFreshSelectionScale_ne_top key message cache
  have hdenZero : count + scale ≠ 0 := ne_of_gt
    ((pos_iff_ne_zero.mpr hscaleZero).trans_le (le_add_of_nonneg_left zero_le))
  have hdenTop : count + scale ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hcount, hscaleTop⟩
  have hproduct : 1 ≤ digestReuseWeight q * scale :=
    le_of_eq_of_le (ENNReal.inv_mul_cancel hscaleZero hscaleTop).symm
      (mul_le_mul' (inv_messageFreshSelectionScale_le_digestReuseWeight key message cache q hcache) le_rfl)
  change (count + scale)⁻¹ ≤ digestReuseWeight q / (1 + count * digestReuseWeight q)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by dsimp only [count]; finiteness))).mpr
  calc
    _ ≤ (count + scale)⁻¹ * (digestReuseWeight q * scale + count * digestReuseWeight q) :=
      mul_le_mul' le_rfl (add_le_add hproduct le_rfl)
    _ = ((count + scale)⁻¹ * (count + scale)) * digestReuseWeight q := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hdenZero hdenTop, one_mul]

theorem reuse_gap_antitone (exactReuse upper coarse allWeight unmatched : ENNReal)
    (hexact : exactReuse ≠ ⊤) (hupper : exactReuse ≤ upper) (hcoarse : upper ≤ coarse) (hweight : unmatched ≤ allWeight) :
    (coarse - upper) * allWeight + upper * unmatched ≤
      (coarse - exactReuse) * allWeight + exactReuse * unmatched := by
  have hsplit : (coarse - upper) + (upper - exactReuse) = coarse - exactReuse :=
    ENNReal.eq_sub_of_add_eq hexact (by rw [add_assoc, tsub_add_cancel_of_le hupper, tsub_add_cancel_of_le hcoarse])
  calc
    _ = (coarse - upper) * allWeight + (upper - exactReuse) * unmatched + exactReuse * unmatched := by
      rw [add_assoc, ← add_mul, tsub_add_cancel_of_le hupper]
    _ ≤ (coarse - upper) * allWeight + (upper - exactReuse) * allWeight + exactReuse * unmatched :=
      add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hweight)) le_rfl
    _ = _ := by rw [← add_mul, hsplit]

noncomputable def rawIndexNormalizedReuseRefund (key : SecretKey) (cap queries signings : Nat)
    (state : CoverLogState) (message : Message) : TargetShapeVector :=
  fun G R => normalizedDigestReuseWeight key message state.1 cap *
    (cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True) * digestReuseWeight cap *
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (targetReuseStep (observedRawIndexShapeVector key state)) G R +
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (unmatchedRawIndexShape key message state) G R)

theorem rawIndexNormalizedReuseRefund_le_gaps
    (key : SecretKey) (cap queries signings : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    rawIndexNormalizedReuseRefund key cap queries signings state message groups remaining ≤
      rawIndexReuseSigningGap key cap queries signings state message groups remaining +
        rawIndexUnmatchedSigningGap key cap queries signings state message groups remaining := by
  have hcoefficient : digestReuseWeight cap - normalizedDigestReuseWeight key message state.1 cap =
      cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True) * digestReuseWeight cap *
        normalizedDigestReuseWeight key message state.1 cap :=
    ENNReal.sub_eq_of_eq_add_rev (normalizedDigestReuseWeight_ne_top key message state.1 cap hcap)
      (normalizedDigestReuseWeight_add_cached key message state.1 cap hcap hcache).symm
  have h := reuse_gap_antitone (exactDigestReuseWeight key message state.1)
    (normalizedDigestReuseWeight key message state.1 cap) (digestReuseWeight cap) _ _
    (exactDigestReuseWeight_ne_top key message state.1)
    (exactDigestReuseWeight_le_normalized key message state.1 cap hcap hcache)
    (normalizedDigestReuseWeight_le key message state.1 cap)
    (targetShapeEnvelope_mono (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries signings
      (fun G R hv => unmatchedRawIndexShape_le_reuse key message state G R hv) groups remaining hvalid)
  rw [hcoefficient] at h
  unfold rawIndexNormalizedReuseRefund rawIndexReuseSigningGap rawIndexUnmatchedSigningGap
  convert h using 1; first | rfl | ring

theorem rawIndexNormalizedReuseRefund_of_no_cached_selection
    (key : SecretKey) (cap queries signings : Nat) (state : CoverLogState) (message : Message)
    (hcount : cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True) = 0)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    rawIndexNormalizedReuseRefund key cap queries signings state message groups remaining =
      digestReuseWeight cap * targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (targetReuseStep (observedRawIndexShapeVector key state)) groups remaining := by
  simp only [rawIndexNormalizedReuseRefund, normalizedDigestReuseWeight, hcount, zero_mul, add_zero, zero_add, div_one]
  exact congrArg (fun value => digestReuseWeight cap * value)
    (targetShapeEnvelope_congr _ _ _ queries signings
      (fun G R hv => unmatchedRawIndexShape_eq_reuse_of_no_cached_selection key message state hcount G R hv)
      groups remaining hvalid)

end SphincsSecurity.Concrete
