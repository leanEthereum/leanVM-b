import SphincsSecurity.Proof.NormalizedDigestReuse

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

theorem joint_selection_gap_lower (fresh exactReuse upper coarse count freshWeight allWeight unmatched : ENNReal)
    (hexact : exactReuse ≠ ⊤) (hupper : exactReuse ≤ upper) (hcoarse : upper ≤ coarse)
    (hmass : count * exactReuse ≤ 1 - fresh) :
    min (coarse * allWeight) ((coarse - upper) * allWeight + upper * (count * freshWeight + unmatched)) ≤
      (1 - fresh) * freshWeight + (coarse - exactReuse) * allWeight + exactReuse * unmatched := by
  have hbase : (coarse - exactReuse) * allWeight + exactReuse * (count * freshWeight + unmatched) ≤
      (1 - fresh) * freshWeight + (coarse - exactReuse) * allWeight + exactReuse * unmatched := by
    have h := add_le_add (add_le_add (mul_le_mul' hmass (le_refl freshWeight))
      (le_refl ((coarse - exactReuse) * allWeight))) (le_refl (exactReuse * unmatched))
    convert h using 1 <;> first | rfl | ring
  apply le_trans ?_ hbase
  by_cases hweight : count * freshWeight + unmatched ≤ allWeight
  · exact (min_le_right _ _).trans (reuse_gap_antitone exactReuse upper coarse allWeight
      (count * freshWeight + unmatched) hexact hupper hcoarse hweight)
  · apply (min_le_left _ _).trans
    calc
      coarse * allWeight = (coarse - exactReuse) * allWeight + exactReuse * allWeight := by
        rw [← add_mul, tsub_add_cancel_of_le (hupper.trans hcoarse)]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl (le_of_not_ge hweight))

noncomputable def rawIndexJointSelectionRefund (key : SecretKey) (cap queries signings : Nat)
    (state : CoverLogState) (message : Message) : TargetShapeVector :=
  fun G R => min
    (digestReuseWeight cap * targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
      queries signings (targetReuseStep (observedRawIndexShapeVector key state)) G R)
    (normalizedDigestReuseWeight key message state.1 cap *
      cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True) * (Fintype.card Index : ENNReal)⁻¹ *
        targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
          queries signings (targetFreshSigningIncrement (observedRawIndexShapeVector key state)) G R +
      rawIndexNormalizedReuseRefund key cap queries signings state message G R)

theorem rawIndexJointSelectionRefund_le_gaps
    (key : SecretKey) (cap queries signings : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    rawIndexJointSelectionRefund key cap queries signings state message groups remaining ≤
      rawIndexNonfreshSigningGap key cap queries signings state message groups remaining +
        rawIndexReuseSigningGap key cap queries signings state message groups remaining +
        rawIndexUnmatchedSigningGap key cap queries signings state message groups remaining := by
  have hmass : cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True) *
      exactDigestReuseWeight key message state.1 ≤ 1 - freshDigestSelectionProbability key message state.1 := by
    apply ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top (by finiteness)
      (show freshDigestSelectionProbability key message state.1 ≤ 1 from probEvent_le_one))
    exact le_self_add.trans_eq (freshSelection_add_count_exactWeight_add_exhaustion key message state.1)
  have hcoef : digestReuseWeight cap - normalizedDigestReuseWeight key message state.1 cap =
      cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True) * digestReuseWeight cap *
        normalizedDigestReuseWeight key message state.1 cap :=
    ENNReal.sub_eq_of_eq_add_rev (normalizedDigestReuseWeight_ne_top key message state.1 cap hcap)
      (normalizedDigestReuseWeight_add_cached key message state.1 cap hcap hcache).symm
  have h := joint_selection_gap_lower (freshDigestSelectionProbability key message state.1)
    (exactDigestReuseWeight key message state.1) (normalizedDigestReuseWeight key message state.1 cap) (digestReuseWeight cap)
    (cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True))
    ((Fintype.card Index : ENNReal)⁻¹ * targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
      queries signings (targetFreshSigningIncrement (observedRawIndexShapeVector key state)) groups remaining)
    (targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
      queries signings (targetReuseStep (observedRawIndexShapeVector key state)) groups remaining)
    (targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
      queries signings (unmatchedRawIndexShape key message state) groups remaining)
    (exactDigestReuseWeight_ne_top key message state.1)
    (exactDigestReuseWeight_le_normalized key message state.1 cap hcap hcache)
    (normalizedDigestReuseWeight_le key message state.1 cap) hmass
  rw [hcoef] at h
  unfold rawIndexJointSelectionRefund rawIndexNormalizedReuseRefund rawIndexNonfreshSigningGap
    rawIndexReuseSigningGap rawIndexUnmatchedSigningGap
  convert h using 1 <;> congr 1 <;> ring

theorem rawIndexJointSelectionRefund_of_no_cached_selection
    (key : SecretKey) (cap queries signings : Nat) (state : CoverLogState) (message : Message)
    (hcount : cachedMessageEntryCountWhere state.1 key.parameter key.root message (fun _ => True) = 0)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    rawIndexJointSelectionRefund key cap queries signings state message groups remaining =
      digestReuseWeight cap * targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (targetReuseStep (observedRawIndexShapeVector key state)) groups remaining := by
  rw [rawIndexJointSelectionRefund, rawIndexNormalizedReuseRefund_of_no_cached_selection
    key cap queries signings state message hcount groups remaining hvalid]
  simp only [hcount, mul_zero, zero_mul, zero_add, min_self]

end SphincsSecurity.Concrete
