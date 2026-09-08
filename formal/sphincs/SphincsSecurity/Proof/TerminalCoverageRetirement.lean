import SphincsSecurity.Proof.RemainingCoverageProbability

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def currentCoveragePotential (key : SecretKey) (state : CoverLogState) : ENNReal :=
  if SigningTranscript.Valid state.2 then
    min 1 (cacheMessageWeight key.parameter
      (fun input target => targetShapeMoments key state.1 state.2 (payloadOf input) target ∅ Finset.univ) state.1 *
        ((2 ^ 140 : Nat) : ENNReal)⁻¹)
  else 0

theorem currentCoveragePotential_le_one (key : SecretKey) (state : CoverLogState) :
    currentCoveragePotential key state ≤ 1 := by
  unfold currentCoveragePotential
  split_ifs
  · exact min_le_left _ _
  · exact zero_le

theorem currentCoveragePotential_le_remaining (key : SecretKey) (cap budget : Nat) (state : CoverLogState) :
    currentCoveragePotential key state ≤
      cappedRemainingCachedTargetEnvelope key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ := by
  unfold currentCoveragePotential cappedRemainingCachedTargetEnvelope
  split_ifs
  · apply (min_le_right _ _).trans
    apply mul_le_mul' _ le_rfl
    apply cacheMessageWeight_mono
    intro input target
    exact le_targetShapeEnvelope _ _ _ _ _ _ ∅ Finset.univ
  · simp only [zero_mul, le_refl]

theorem currentCoveragePotential_eq_one_of_covered (key : SecretKey) (state : CoverLogState)
    (hvalid : SigningTranscript.Valid state.2) (hcover : SigningCacheCovered key.parameter key.root state.1 state.2) :
    currentCoveragePotential key state = 1 := by
  obtain ⟨input, output, hmessage, houtput, hadmissible, hcovered⟩ := hcover
  have hrow := normalizedTargetLogProduct_full_ge_of_covered key state (payloadOf input) (hashOutputFewTimeView output) hcovered
  have hmoment : ((2 ^ 140 : Nat) : ENNReal) ≤ targetShapeMoments key state.1 state.2 (payloadOf input) (hashOutputFewTimeView output) ∅ Finset.univ := by
    simpa only [targetShapeMoments, Finset.prod_empty, one_mul] using hrow
  have hentry : ((2 ^ 140 : Nat) : ENNReal) ≤ cacheMessageEntryWeight key.parameter
      (fun query target => targetShapeMoments key state.1 state.2 (payloadOf query) target ∅ Finset.univ) state.1 input := by
    simpa only [cacheMessageEntryWeight, houtput, hmessage, hadmissible, and_self, if_true] using hmoment
  have htotal := hentry.trans (ENNReal.le_tsum input)
  unfold currentCoveragePotential
  rw [if_pos hvalid, min_eq_left]
  have hpositive : ((2 ^ 140 : Nat) : ENNReal) ≠ 0 := by norm_num
  rw [← ENNReal.mul_inv_cancel hpositive (by finiteness)]
  exact mul_le_mul' htotal le_rfl

noncomputable def terminalCoverageRetirement (key : SecretKey) (cap : Nat) (state : CoverLogState) : ENNReal :=
  cappedRemainingCachedTargetEnvelope key cap 0 state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ -
    currentCoveragePotential key state

theorem currentCoveragePotential_eq_zero_of_not_covered (key : SecretKey) (state : CoverLogState)
    (hnot : ¬ SigningCacheCovered key.parameter key.root state.1 state.2) :
    currentCoveragePotential key state = 0 := by
  have hzero : cacheMessageWeight key.parameter
      (fun input target => targetShapeMoments key state.1 state.2 (payloadOf input) target ∅ Finset.univ) state.1 = 0 := by
    apply ENNReal.tsum_eq_zero.mpr
    intro input
    unfold cacheMessageEntryWeight
    cases hout : state.1 input with
    | none => rfl
    | some output =>
        simp only
        split_ifs with hg
        · have hn : ¬ CoveredFewTimeView
              (eligibleSigningViews (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root (payloadOf input) state.2)
              (hashOutputFewTimeView output) := fun hc => hnot ⟨input, output, hg.1, hout, hg.2, hc⟩
          have ha : targetAssignmentCount
              (eligibleSigningViews (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root (payloadOf input) state.2)
              (hashOutputFewTimeView output) = 0 := by
            have hp := mt (targetAssignmentCount_pos_iff _ _).mp hn
            omega
          unfold targetAssignmentCount at ha
          simp only [targetShapeMoments, Finset.prod_empty, normalizedTargetLogProduct, normalizedTargetLogMatch,
            Finset.prod_mul_distrib, ← Nat.cast_prod, ha, Nat.cast_zero, mul_zero]
        · rfl
  simp only [currentCoveragePotential, hzero, zero_mul, min_eq_right zero_le, ite_self]

theorem currentCoveragePotential_eq_indicator (key : SecretKey) (state : CoverLogState) :
    currentCoveragePotential key state =
      if SigningTranscript.Valid state.2 ∧ SigningCacheCovered key.parameter key.root state.1 state.2 then 1 else 0 := by
  by_cases hv : SigningTranscript.Valid state.2
  · by_cases hc : SigningCacheCovered key.parameter key.root state.1 state.2
    · rw [if_pos ⟨hv, hc⟩]
      exact currentCoveragePotential_eq_one_of_covered key state hv hc
    · rw [if_neg (fun h => hc h.2)]
      exact currentCoveragePotential_eq_zero_of_not_covered key state hc
  · simp only [currentCoveragePotential, hv, false_and, if_false]

theorem currentCoveragePotential_add_retirement (key : SecretKey) (cap : Nat) (state : CoverLogState) :
    currentCoveragePotential key state + terminalCoverageRetirement key cap state =
      cappedRemainingCachedTargetEnvelope key cap 0 state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ :=
  add_tsub_cancel_of_le (currentCoveragePotential_le_remaining key cap 0 state)

end SphincsSecurity.Concrete
