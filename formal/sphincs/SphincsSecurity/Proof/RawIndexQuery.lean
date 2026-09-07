import SphincsSecurity.Proof.FreshTargetShapeAverage
import SphincsSecurity.Proof.CachedMultiplicityPower

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem targetIndexMoments_cacheQuery (key : SecretKey) (power degree : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log) :
    targetIndexMoments key (before.cacheQuery input output) log power degree =
      targetIndexMoments key before log power degree +
        (if MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
          cachePowerArrival power (cachedIndexMultiplicity key.parameter before (hashOutputFewTimeView output).1) *
            ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log)
              (hashOutputFewTimeView output).1).card : ENNReal) ^ degree else 0) := by
  unfold targetIndexMoments
  rw [observedOptionalSigningViews_cache_stable key.parameter key.root before _ log (QueryCache.le_cacheQuery before hfresh) hsigned]
  by_cases hgood : MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output)
  · simp only [cachedIndexMultiplicity_cacheQuery key.parameter before input output hfresh, hgood.1, hgood.2, true_and]
    have hpoint (index : Index) :
        (cachedIndexMultiplicity key.parameter before index + (if (hashOutputFewTimeView output).1 = index then 1 else 0)) ^ power *
            ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) index).card : ENNReal) ^ degree =
          cachedIndexMultiplicity key.parameter before index ^ power *
            ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) index).card : ENNReal) ^ degree +
          (if (hashOutputFewTimeView output).1 = index then
            cachePowerArrival power (cachedIndexMultiplicity key.parameter before (hashOutputFewTimeView output).1) *
              ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log)
                (hashOutputFewTimeView output).1).card : ENNReal) ^ degree else 0) := by
      by_cases heq : (hashOutputFewTimeView output).1 = index
      · subst index
        simp only [if_true, add_one_pow_eq_cachePowerArrival, add_mul]
      · simp only [heq, if_false, add_zero]
    simp only [hpoint, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · have hbad (index : Index) : ¬ (MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) ∧
        (hashOutputFewTimeView output).1 = index) := fun h => hgood ⟨h.1, h.2.1⟩
    simp only [if_neg hgood, cachedIndexMultiplicity_cacheQuery key.parameter before input output hfresh, hbad, if_false, add_zero]

theorem expected_message_targetIndexMoments (key : SecretKey) (power degree : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (hfresh : before input = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (hmessage : MessageHashInput key.parameter input) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      targetIndexMoments key (before.cacheQuery input output) log power degree) =
      targetIndexMoments key before log power degree +
        (∑ lower ∈ Finset.range power, (power.choose lower : ENNReal) * targetIndexMoments key before log lower degree) *
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 := tsum_probOutput_eq_one' (by simp)
  simp only [targetIndexMoments_cacheQuery key power degree before log input _ hfresh hsigned, hmessage, true_and,
    mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
  rw [expected_uniformHashOutput_admissible_weight (fun source : FewTimeView =>
    cachePowerArrival power (cachedIndexMultiplicity key.parameter before source.1) *
      ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1).card : ENNReal) ^ degree)]
  rw [uniform_view_index_weight_expectation (fun index =>
    cachePowerArrival power (cachedIndexMultiplicity key.parameter before index) *
      ((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) index).card : ENNReal) ^ degree),
    weighted_cachePowerArrival_sum]
  unfold targetIndexMoments
  simp only [div_eq_mul_inv]
  ring

end SphincsSecurity.Concrete
