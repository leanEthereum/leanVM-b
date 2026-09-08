import SphincsSecurity.Proof.UnmatchedSignerWeight
import SphincsSecurity.Proof.ExactRawIndexSigning

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local irreducible] signWithView observedWeightedPowerMoments

theorem expected_signWithView_weightedPower_eq_add
    (weights : Index → ENNReal) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      observedWeightedPowerMoments weights key (result.2, log ++ [⟨message, result.1.1⟩]) degree) =
      observedWeightedPowerMoments weights key (before, log) degree +
        ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
          successfulSignerViewWeight (fun source => weights source.1 * cachePowerArrival degree ((signingSlotsAtIndex
            (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1).card : ENNReal)) result := by
  calc
    _ = ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        (observedWeightedPowerMoments weights key (before, log) degree +
          successfulSignerViewWeight (fun source => weights source.1 * cachePowerArrival degree ((signingSlotsAtIndex
            (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1).card : ENNReal)) result) := by
      apply tsum_congr
      intro result
      by_cases hr : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
      · rw [signWithView_weightedPower_eq weights key message before log degree hsigned result hr]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

theorem expected_signWithView_weightedPower_add_unmatched_le
    (weights : Index → ENNReal) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      observedWeightedPowerMoments weights key (result.2, log ++ [⟨message, result.1.1⟩]) degree) +
      exactDigestReuseWeight key message before * unmatchedCachedSignerWeight key message before
        (fun _ source => weights source.1 * cachePowerArrival degree ((signingSlotsAtIndex
          (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1).card : ENNReal)) ≤
      observedWeightedPowerMoments weights key (before, log) degree +
        freshDigestSelectionProbability key message before *
          ((∑ index : Index, weights index * cachePowerArrival degree ((signingSlotsAtIndex
            (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) index).card : ENNReal)) / (Fintype.card Index : ENNReal)) +
        cacheMessageWeight key.parameter (fun _ source => weights source.1 * cachePowerArrival degree ((signingSlotsAtIndex
          (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1).card : ENNReal)) before *
          exactDigestReuseWeight key message before := by
  rw [expected_signWithView_weightedPower_eq_add weights key message before log degree hsigned]
  let weight := fun source : FewTimeView => weights source.1 * cachePowerArrival degree ((signingSlotsAtIndex
    (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1).card : ENNReal)
  have h := expected_successfulSignerInputWeight_add_unmatched_le key message before
    (fun _ source => weight source) weight (fun _ _ => le_rfl)
  simp only [successfulSignerInputWeight_const] at h
  dsimp only [weight] at h
  rw [uniform_view_index_weight_expectation (fun index => weights index * cachePowerArrival degree ((signingSlotsAtIndex
    (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) index).card : ENNReal))] at h
  rw [add_assoc, add_assoc]
  exact add_le_add le_rfl h

noncomputable def unmatchedRawIndexReuse (key : SecretKey) (message : Message) (state : CoverLogState)
    (power degree : Nat) : ENNReal :=
  unmatchedCachedSignerWeight key message state.1
    (fun _ source => cachedIndexMultiplicity key.parameter state.1 source.1 ^ power *
      cachePowerArrival degree ((signingSlotsAtIndex
        (observedOptionalSigningViews (messageAnswers key.parameter state.1) key.root state.2) source.1).card : ENNReal))

noncomputable def unmatchedRawIndexShape (key : SecretKey) (message : Message) (state : CoverLogState) : TargetShapeVector :=
  fun G R => unmatchedRawIndexReuse key message state G.card R.card

theorem expected_signWithView_frozenRawIndex_add_unmatched_le
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (power degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      observedWeightedPowerMoments (fun index => cachedIndexMultiplicity key.parameter before index ^ power) key
        (result.2, log ++ [⟨message, result.1.1⟩]) degree) +
      exactDigestReuseWeight key message before * unmatchedRawIndexReuse key message (before, log) power degree ≤
      targetIndexMoments key before log power degree +
        freshDigestSelectionProbability key message before *
          ((Fintype.card Index : ENNReal)⁻¹ * targetIndexTreeLower (targetIndexMoments key before log) power degree) +
          exactDigestReuseWeight key message before * targetIndexReuseStep (targetIndexMoments key before log) power degree := by
  apply (expected_signWithView_weightedPower_add_unmatched_le (fun index => cachedIndexMultiplicity key.parameter before index ^ power)
    key message before log degree hsigned).trans_eq
  rw [← targetIndexTreeLower_eq_weighted, ← targetIndexReuseStep_eq_cached]
  simp only [targetIndexMoments_eq_weightedPower, div_eq_mul_inv]
  ring

theorem expected_signWithView_targetIndexMoments_add_unmatched_le
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (power degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      targetIndexMoments key result.2 (log ++ [⟨message, result.1.1⟩]) power degree) +
      exactDigestReuseWeight key message before * unmatchedRawIndexReuse key message (before, log) power degree ≤
      targetIndexSigning (freshDigestSelectionProbability key message before * (Fintype.card Index : ENNReal)⁻¹)
        (exactDigestReuseWeight key message before) (targetIndexMoments key before log) power degree := by
  have hsplit : (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      targetIndexMoments key result.2 (log ++ [⟨message, result.1.1⟩]) power degree) =
      (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        observedWeightedPowerMoments (fun index => cachedIndexMultiplicity key.parameter before index ^ power) key
          (result.2, log ++ [⟨message, result.1.1⟩]) degree) +
      ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        rawIndexSigningGrowth key before power (result.2, log ++ [⟨message, result.1.1⟩]) degree := by
    rw [← ENNReal.tsum_add]
    apply tsum_congr
    intro result
    by_cases hr : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
    · have hs := targetIndexMoments_eq_frozen_add_growth key before power
        (result.2, log ++ [(⟨message, result.1.1⟩ : SigningEntry)])
        (simulateQ_romImpl_cache_le (signWithView key message) before result hr) degree
      dsimp only at hs
      rw [hs, mul_add]
    · rw [probOutput_eq_zero_of_not_mem_support hr]
      simp only [zero_mul, zero_add]
  have h := add_le_add (expected_signWithView_frozenRawIndex_add_unmatched_le key message before log power degree hsigned)
    ((expected_signWithView_rawIndexGrowth_le_mass_mul_uniform key message before log power degree hsigned).trans_eq
      (congrArg (fun value => freshDigestSelectionProbability key message before * value)
        (expected_newRawIndexWeight key before log power degree)))
  rw [hsplit, add_right_comm]
  apply h.trans_eq
  unfold targetIndexSigning
  ring

attribute [local irreducible] observedRawIndexShapeVector

theorem expected_logTraced_sign_rawIndexShape_add_unmatched_le
    (key : SecretKey) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      observedRawIndexShapeVector key result.2 groups remaining) +
      exactDigestReuseWeight key message state.1 * unmatchedRawIndexShape key message state groups remaining ≤
      targetShapeSigning (freshDigestSelectionProbability key message state.1 * (Fintype.card Index : ENNReal)⁻¹)
        (exactDigestReuseWeight key message state.1) (observedRawIndexShapeVector key state) groups remaining := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  change (∑' result : Option Signature × QueryCache HashSpec,
    Pr[= result | (show ProbComp (Option Signature × QueryCache HashSpec) from
      (unloggedMappedAdversaryImpl key (.inr message)).run state.1)] *
      observedRawIndexShapeVector key (result.2, state.2 ++ [⟨message, result.1⟩]) groups remaining) +
    exactDigestReuseWeight key message state.1 * unmatchedRawIndexShape key message state groups remaining ≤ _
  have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
      (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
    (simulateQ_signWithView_fst_run key message state.1).symm
  rw [hrun, tsum_probOutput_map_mul]
  simp only [observedRawIndexShapeVector, liftTargetIndexVector]
  apply (expected_signWithView_targetIndexMoments_add_unmatched_le key message state.1 state.2 groups.card remaining.card hsigned).trans_eq
  exact (targetShapeSigning_lift _ _ _ groups remaining hvalid).symm

end SphincsSecurity.Concrete
