import SphincsSecurity.Proof.RemainingCoveragePotential

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
open FtsProbeSimulation.JointOriginal (unusedTargetExecutionCost)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem remainingRawIndexEnvelope_cacheQuery_nonmessage (key : SecretKey) (cap budget signatures : Nat)
    (state : CoverLogState) (input : HashInput) (output : HashOutput)
    (hfresh : state.1 input = none) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hmessage : ¬ MessageHashInput key.parameter input) :
    remainingRawIndexEnvelope key cap budget signatures (state.1.cacheQuery input output, state.2) =
      remainingRawIndexEnvelope key cap budget signatures state := by
  have hshape : observedRawIndexShapeVector key (state.1.cacheQuery input output, state.2) = observedRawIndexShapeVector key state := by
    funext groups remaining
    change targetIndexMoments key (state.1.cacheQuery input output) state.2 groups.card remaining.card = _
    rw [targetIndexMoments_cacheQuery key _ _ state.1 state.2 input output hfresh hsigned]
    simp only [hmessage, false_and, if_false, add_zero]
    rfl
  simp only [remainingRawIndexEnvelope, hshape]

theorem remainingTargetEnvelope_cacheQuery_nonmessage (key : SecretKey) (cap budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) (input : HashInput) (output : HashOutput)
    (hfresh : state.1 input = none) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hmessage : ¬ MessageHashInput key.parameter input) :
    remainingTargetEnvelope key cap budget payload target signatures (state.1.cacheQuery input output, state.2) =
      remainingTargetEnvelope key cap budget payload target signatures state := by
  have hshape : observedTargetShapeVector key payload target (state.1.cacheQuery input output, state.2) =
      observedTargetShapeVector key payload target state := by
    funext groups remaining
    exact targetShapeMoments_cacheQuery_unchanged key state.1 state.2 payload target groups remaining input output hfresh hsigned (Or.inl hmessage)
  simp only [remainingTargetEnvelope, hshape]

theorem remainingCoveragePotential_cacheQuery_nonmessage (key : SecretKey) (cap budget : Nat)
    (state : CoverLogState) (input : HashInput) (output : HashOutput)
    (hfresh : state.1 input = none) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hmessage : ¬ MessageHashInput key.parameter input) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    remainingCoveragePotential key cap budget (state.1.cacheQuery input output, state.2) groups remaining =
      remainingCoveragePotential key cap budget state groups remaining := by
  simp only [remainingCoveragePotential, cappedRemainingCachedTargetEnvelope, cappedRemainingRawIndexEnvelope,
    remainingRawIndexEnvelope_cacheQuery_nonmessage key cap budget _ state input output hfresh hsigned hmessage]
  split_ifs
  · simp only [remainingCachedTargetEnvelope,
      remainingTargetEnvelope_cacheQuery_nonmessage key cap budget _ _ _ state input output hfresh hsigned hmessage,
      cacheMessageWeight_cacheQuery key.parameter _ state.1 input output hfresh, hmessage, false_and, if_false, add_zero]
  · rfl

noncomputable def remainingCoverageBudgetGap (key : SecretKey) (cap budget : Nat) (state : CoverLogState)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  (cappedRemainingCachedTargetEnvelope key cap budget state groups remaining -
    cappedRemainingCachedTargetEnvelope key cap (budget - 1) state groups remaining) +
      (cappedRemainingRawIndexEnvelope key cap budget state groups remaining -
        cappedRemainingRawIndexEnvelope key cap (budget - 1) state groups remaining) * ((budget - 1 : Nat) : ENNReal) *
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)

theorem remainingCoveragePotential_add_budgetGap (key : SecretKey) (cap budget : Nat) (hbudget : 1 ≤ budget)
    (state : CoverLogState) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    remainingCoveragePotential key cap (budget - 1) state groups remaining +
      (cappedRemainingRawIndexEnvelope key cap budget state groups remaining *
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) +
          remainingCoverageBudgetGap key cap budget state groups remaining) =
      remainingCoveragePotential key cap budget state groups remaining := by
  have ht : cappedRemainingCachedTargetEnvelope key cap (budget - 1) state groups remaining ≤
      cappedRemainingCachedTargetEnvelope key cap budget state groups remaining := by
    simp only [cappedRemainingCachedTargetEnvelope]
    split_ifs
    · exact remainingCachedTargetEnvelope_budget_mono key cap _ state (Nat.sub_le _ _) groups remaining hvalid
    · exact le_rfl
  have hr : cappedRemainingRawIndexEnvelope key cap (budget - 1) state groups remaining ≤
      cappedRemainingRawIndexEnvelope key cap budget state groups remaining := by
    simp only [cappedRemainingRawIndexEnvelope]
    split_ifs
    · exact remainingRawIndexEnvelope_budget_mono key cap _ state (Nat.sub_le _ _) groups remaining hvalid
    · exact le_rfl
  have hcount : ((budget - 1 : Nat) : ENNReal) + 1 = budget := by
    exact_mod_cast Nat.sub_add_cancel hbudget
  unfold remainingCoveragePotential remainingCoverageBudgetGap
  calc
    _ = (cappedRemainingCachedTargetEnvelope key cap (budget - 1) state groups remaining +
          (cappedRemainingCachedTargetEnvelope key cap budget state groups remaining -
            cappedRemainingCachedTargetEnvelope key cap (budget - 1) state groups remaining)) +
        (cappedRemainingRawIndexEnvelope key cap (budget - 1) state groups remaining +
          (cappedRemainingRawIndexEnvelope key cap budget state groups remaining -
            cappedRemainingRawIndexEnvelope key cap (budget - 1) state groups remaining)) * ((budget - 1 : Nat) : ENNReal) *
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) +
        cappedRemainingRawIndexEnvelope key cap budget state groups remaining *
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) := by ring
    _ = _ := by
      rw [add_tsub_cancel_of_le ht, add_tsub_cancel_of_le hr]
      rw [← hcount]
      ring

noncomputable def remainingUnusedCoverageStepCharge (key : SecretKey) (cap budget : Nat) (state : CoverLogState)
    (input : (OracleWorld + SigningSpec).Domain) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  cappedRemainingRawIndexEnvelope key cap budget state groups remaining * (unusedTargetExecutionCost key.parameter state.1 input : ENNReal) *
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) +
      match input with
      | .inl (.inr hashInput) => if ¬ MessageHashInput key.parameter hashInput then remainingCoverageBudgetGap key cap budget state groups remaining else 0
      | _ => 0

theorem unusedCoverageCharge_le_stepCharge (key : SecretKey) (cap budget : Nat) (state : CoverLogState)
    (input : (OracleWorld + SigningSpec).Domain) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    cappedRemainingRawIndexEnvelope key cap budget state groups remaining * (unusedTargetExecutionCost key.parameter state.1 input : ENNReal) *
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) ≤
      remainingUnusedCoverageStepCharge key cap budget state input groups remaining := le_self_add

theorem expected_logTraced_remainingCoverage_add_stepCharge_le (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (input : (OracleWorld + SigningSpec).Domain)
    (hcost : signingExecutionHashCost input ≤ budget)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      remainingCoveragePotential key cap (budget - signingExecutionHashCost input) result.2 groups remaining) +
      remainingUnusedCoverageStepCharge key cap budget state input groups remaining ≤
      remainingCoveragePotential key cap budget state groups remaining := by
  have hbase := expected_logTraced_remainingCoverage_add_unused_le key cap budget hcap state hsigned hcache input hcost groups remaining hvalid
  cases input with
  | inr message => simpa only [remainingUnusedCoverageStepCharge, add_zero] using hbase
  | inl world =>
      cases world with
      | inl sample => simpa only [remainingUnusedCoverageStepCharge, add_zero] using hbase
      | inr hashInput =>
          by_cases hmessage : MessageHashInput key.parameter hashInput
          · simpa only [remainingUnusedCoverageStepCharge, hmessage, not_true_eq_false, if_false, add_zero] using hbase
          · have hunused : unusedTargetExecutionCost key.parameter state.1 (.inl (.inr hashInput)) = 1 := by
              simp [unusedTargetExecutionCost, unusedSigningExecutionCost,
                unusedTargetHashCost, targetArrivalHashCost, freshWorldTargetHashCost, hmessage, signingMacroHashCost]
            simp only [remainingUnusedCoverageStepCharge, if_pos hmessage, hunused, Nat.cast_one, mul_one]
            apply le_trans ?_ (le_of_eq (remainingCoveragePotential_add_budgetGap key cap budget hcost state groups remaining hvalid))
            apply add_le_add ?_ le_rfl
            rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
            simp only [signingLogFragment, List.append_nil]
            change (∑' result, Pr[= result | (randomOracle hashInput).run state.1] *
              remainingCoveragePotential key cap (budget - 1) (result.2, state.2) groups remaining) ≤ _
            by_cases hfresh : state.1 hashInput = none
            · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
              simp only [remainingCoveragePotential_cacheQuery_nonmessage key cap (budget - 1) state hashInput _ hfresh hsigned hmessage,
                ENNReal.tsum_mul_right]
              exact mul_le_of_le_one_left' tsum_probOutput_le_one
            · obtain ⟨output, ho⟩ := Option.ne_none_iff_exists'.mp hfresh
              rw [randomOracle, QueryImpl.withCaching_run_some _ ho, tsum_probOutput_pure_mul]

end SphincsSecurity.Concrete
