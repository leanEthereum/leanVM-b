import SphincsSecurity.Proof.MessageDigestHazard
import SphincsSecurity.Proof.JointDigestSelectionGap

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

theorem normalized_reuse_mono (count small large : ENNReal) (hcount : count ≠ ⊤)
    (hlarge : large ≠ ⊤) (hle : small ≤ large) :
    small / (1 + count * small) ≤ large / (1 + count * large) := by
  have hsmall : small ≠ ⊤ := ne_top_of_le_ne_top hlarge hle
  have hzero : 1 + count * small ≠ 0 := by positivity
  have htop : 1 + count * small ≠ ⊤ := by finiteness
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
  have hcross : small * (1 + count * large) ≤ large * (1 + count * small) := by
    have h := add_le_add hle (le_refl (count * small * large))
    convert h using 1 <;> first | rfl | ring
  have h := ENNReal.div_le_div_right hcross (1 + count * small)
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, ENNReal.mul_inv_cancel hzero htop, mul_one] using h

noncomputable def normalizedMessageReuseWeight (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  messageDigestReuseWeight key message cache /
    (1 + cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * messageDigestReuseWeight key message cache)

theorem normalizedMessageReuseWeight_le_normalized (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    normalizedMessageReuseWeight key message cache ≤ normalizedDigestReuseWeight key message cache q :=
  normalized_reuse_mono _ _ _
    (ne_top_of_le_ne_top (by finiteness)
      ((cachedMessageEntryCountWhere_le_enncard cache key.parameter key.root message (fun _ => True)).trans hcache))
    (digestReuseWeight_ne_top q hq) (messageDigestReuseWeight_le key message cache q hcache)

theorem normalizedMessageReuseWeight_le (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    normalizedMessageReuseWeight key message cache ≤ digestReuseWeight q :=
  (normalizedMessageReuseWeight_le_normalized key message cache q hq hcache).trans (normalizedDigestReuseWeight_le key message cache q)

theorem normalizedMessageReuseWeight_ne_top (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) : normalizedMessageReuseWeight key message cache ≠ ⊤ :=
  ne_top_of_le_ne_top (digestReuseWeight_ne_top q hq) (normalizedMessageReuseWeight_le key message cache q hq hcache)

theorem normalizedMessageReuseWeight_eq_inv (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    normalizedMessageReuseWeight key message cache =
      (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) +
        messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal))⁻¹ := by
  let count := cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True)
  let reuse := messageDigestReuseWeight key message cache
  have hreuseTop : reuse ≠ ⊤ := messageDigestReuseWeight_ne_top key message cache q hq hcache
  have hreuseZero : reuse ≠ 0 := by
    unfold reuse messageDigestReuseWeight
    rw [div_eq_mul_inv]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (by finiteness))
      (ENNReal.inv_ne_zero.mpr (messageDigestFreshRate_ne_top key message cache))
  have hinv : reuse⁻¹ = messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal) := by
    unfold reuse messageDigestReuseWeight
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr (by finiteness)))
      (Or.inl (ENNReal.inv_ne_top.mpr (by positivity))), inv_inv, inv_inv, mul_comm]
  have hfactor : 1 + count * reuse = reuse * (count + reuse⁻¹) := by
    rw [mul_add, ENNReal.mul_inv_cancel hreuseZero hreuseTop]
    ring
  change reuse * (1 + count * reuse)⁻¹ = _
  rw [hfactor, ENNReal.mul_inv (Or.inl hreuseZero) (Or.inl hreuseTop), ← mul_assoc,
    ENNReal.mul_inv_cancel hreuseZero hreuseTop, one_mul, hinv]

theorem exactDigestReuseWeight_le_normalizedMessage (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    exactDigestReuseWeight key message cache ≤ normalizedMessageReuseWeight key message cache := by
  have hcount : cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness)
      ((cachedMessageEntryCountWhere_le_enncard cache key.parameter key.root message (fun _ => True)).trans hcache)
  have hreuse := messageDigestReuseWeight_ne_top key message cache q hq hcache
  have hmass : freshDigestSelectionProbability key message cache +
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache ≤ 1 :=
    le_self_add.trans_eq (freshSelection_add_count_exactWeight_add_exhaustion key message cache)
  unfold normalizedMessageReuseWeight
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
  calc
    _ = exactDigestReuseWeight key message cache +
        (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          messageDigestReuseWeight key message cache := by ring
    _ ≤ freshDigestSelectionProbability key message cache * messageDigestReuseWeight key message cache +
        (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          messageDigestReuseWeight key message cache :=
      add_le_add (exactDigestReuseWeight_le_fresh_mul_messageReuseWeight key message cache q hq hcache) le_rfl
    _ = (freshDigestSelectionProbability key message cache +
        cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          messageDigestReuseWeight key message cache := by rw [add_mul]
    _ ≤ _ := mul_le_of_le_one_left' hmass

noncomputable def messageReuseUpperBound (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (q : Nat) : ENNReal :=
  min (digestReuseWeight q) (normalizedMessageReuseWeight key message cache)

theorem messageReuseUpperBound_le (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (q : Nat) :
    messageReuseUpperBound key message cache q ≤ digestReuseWeight q := min_le_left _ _

theorem messageReuseUpperBound_le_normalized (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    messageReuseUpperBound key message cache q ≤ normalizedDigestReuseWeight key message cache q :=
  (min_le_right _ _).trans (normalizedMessageReuseWeight_le_normalized key message cache q hq hcache)

theorem messageReuseUpperBound_ne_top (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) : messageReuseUpperBound key message cache q ≠ ⊤ :=
  ne_top_of_le_ne_top (digestReuseWeight_ne_top q hq) (messageReuseUpperBound_le key message cache q)

theorem exactDigestReuseWeight_le_messageUpper (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    exactDigestReuseWeight key message cache ≤ messageReuseUpperBound key message cache q :=
  le_min (exactDigestReuseWeight_le_digestReuseWeight key message cache q hq hcache)
    (exactDigestReuseWeight_le_normalizedMessage key message cache q hq hcache)

noncomputable def rawIndexMessageReuseRefund (key : SecretKey) (cap queries signings : Nat)
    (state : CoverLogState) (message : Message) : TargetShapeVector :=
  fun G R => (digestReuseWeight cap - messageReuseUpperBound key message state.1 cap) *
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (targetReuseStep (observedRawIndexShapeVector key state)) G R +
    messageReuseUpperBound key message state.1 cap *
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (unmatchedRawIndexShape key message state) G R

theorem rawIndexMessageReuseRefund_le_gaps
    (key : SecretKey) (cap queries signings : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    rawIndexMessageReuseRefund key cap queries signings state message groups remaining ≤
      rawIndexReuseSigningGap key cap queries signings state message groups remaining +
        rawIndexUnmatchedSigningGap key cap queries signings state message groups remaining :=
  reuse_gap_antitone _ _ _ _ _ (exactDigestReuseWeight_ne_top key message state.1)
    (exactDigestReuseWeight_le_messageUpper key message state.1 cap hcap hcache)
    (messageReuseUpperBound_le key message state.1 cap)
    (targetShapeEnvelope_mono (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries signings
      (fun G R hv => unmatchedRawIndexShape_le_reuse key message state G R hv) groups remaining hvalid)

theorem rawIndexMessageReuseRefund_ge_normalized
    (key : SecretKey) (cap queries signings : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    rawIndexNormalizedReuseRefund key cap queries signings state message groups remaining ≤
      rawIndexMessageReuseRefund key cap queries signings state message groups remaining := by
  have hcoef : digestReuseWeight cap - normalizedDigestReuseWeight key message state.1 cap =
      cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True) * digestReuseWeight cap *
        normalizedDigestReuseWeight key message state.1 cap :=
    ENNReal.sub_eq_of_eq_add_rev (normalizedDigestReuseWeight_ne_top key message state.1 cap hcap)
      (normalizedDigestReuseWeight_add_cached key message state.1 cap hcap hcache).symm
  have h := reuse_gap_antitone (messageReuseUpperBound key message state.1 cap)
    (normalizedDigestReuseWeight key message state.1 cap) (digestReuseWeight cap) _ _
    (messageReuseUpperBound_ne_top key message state.1 cap hcap)
    (messageReuseUpperBound_le_normalized key message state.1 cap hcap hcache)
    (normalizedDigestReuseWeight_le key message state.1 cap)
    (targetShapeEnvelope_mono (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries signings
      (fun G R hv => unmatchedRawIndexShape_le_reuse key message state G R hv) groups remaining hvalid)
  rw [hcoef] at h
  unfold rawIndexNormalizedReuseRefund rawIndexMessageReuseRefund
  convert h using 1; first | rfl | ring

theorem rawIndexMessageReuseRefund_of_no_cached_selection
    (key : SecretKey) (cap queries signings : Nat) (state : CoverLogState) (message : Message)
    (hcount : cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True) = 0)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    rawIndexMessageReuseRefund key cap queries signings state message groups remaining =
      digestReuseWeight cap * targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (targetReuseStep (observedRawIndexShapeVector key state)) groups remaining := by
  have hweight := targetShapeEnvelope_congr (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries signings
    (fun G R hv => unmatchedRawIndexShape_eq_reuse_of_no_cached_selection key message state hcount G R hv) groups remaining hvalid
  rw [rawIndexMessageReuseRefund, hweight, ← add_mul, tsub_add_cancel_of_le (messageReuseUpperBound_le key message state.1 cap)]

end SphincsSecurity.Concrete
