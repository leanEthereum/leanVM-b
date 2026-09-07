import SphincsSecurity.Proof.WeightedPowerSigning
import SphincsSecurity.Proof.SignerMixedGrowthBound
import SphincsSecurity.Proof.FreshTargetShapeAverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def rawIndexSigningGrowth (key : SecretKey) (before : QueryCache HashSpec) (power : Nat) (after : CoverLogState) (degree : Nat) : ENNReal :=
  observedWeightedPowerMoments (fun index => cachedIndexMultiplicity key.parameter after.1 index ^ power -
    cachedIndexMultiplicity key.parameter before index ^ power) key after degree

noncomputable def newRawIndexWeight (key : SecretKey) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (power : Nat) (source : FewTimeView) (degree : Nat) : ENNReal :=
  cachePowerArrival power (cachedIndexMultiplicity key.parameter before source.1) *
    (((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1).card + 1 : Nat) : ENNReal) ^ degree

theorem signWithView_rawIndexGrowth_le_new (key : SecretKey) (message : Message) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (power degree : Nat) (signature : Option Signature) (view : Option FewTimeView)
    (hresult : ((signature, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before))
    (hsigned : SigningDigestsCached key.parameter before key.root log) (payload : HashInput) (output : HashOutput)
    (hfresh : before (tweakableHashInput key.parameter .message payload) = none)
    (hafter : after (tweakableHashInput key.parameter .message payload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) :
    rawIndexSigningGrowth key before power (after, log ++ [⟨message, signature⟩]) degree ≤
      newRawIndexWeight key before log power (hashOutputFewTimeView output) degree := by
  have hcache := simulateQ_romImpl_cache_le (signWithView key message) before ((signature, view), after) hresult
  have hcounts := signWithView_cachedIndexMultiplicity_of_new key message before after signature view hresult payload output hfresh hafter hadmissible
  unfold rawIndexSigningGrowth observedWeightedPowerMoments weightedPowerMoment
  calc
    _ ≤ ∑ index : Index, if (hashOutputFewTimeView output).1 = index then
        newRawIndexWeight key before log power (hashOutputFewTimeView output) degree else 0 := by
      apply Finset.sum_le_sum
      intro index _
      dsimp only
      rw [hcounts index]
      by_cases heq : (hashOutputFewTimeView output).1 = index
      · subst index
        simp only [if_true]
        have hpower : (cachedIndexMultiplicity key.parameter before (hashOutputFewTimeView output).1 + 1) ^ power -
            cachedIndexMultiplicity key.parameter before (hashOutputFewTimeView output).1 ^ power ≤
              cachePowerArrival power (cachedIndexMultiplicity key.parameter before (hashOutputFewTimeView output).1) := by
          rw [add_one_pow_eq_cachePowerArrival]
          exact tsub_le_iff_right.mpr (le_of_eq (add_comm _ _))
        exact mul_le_mul' hpower (pow_le_pow_left' (Nat.cast_le.mpr
          (signingSlotsAtIndex_append_le_add_one key before after log ⟨message, signature⟩ hcache hsigned _)) degree)
      · simp only [heq, if_false, add_zero, tsub_self, zero_mul, le_refl]
    _ = _ := by simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem signWithView_rawIndexGrowth_le_newEvents (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (power degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    rawIndexSigningGrowth key before power (result.2, log ++ [⟨message, result.1.1⟩]) degree ≤
      ∑' source, if NewAdmissibleSignerView before key (· = source) result then newRawIndexWeight key before log power source degree else 0 := by
  by_cases hnew : NewAdmissibleSignerView before key (fun _ => True) result
  · obtain ⟨payload, output, hfresh, hafter, hadmissible, _⟩ := hnew
    have hbound := signWithView_rawIndexGrowth_le_new key message before result.2 log power degree result.1.1 result.1.2
      hresult hsigned payload output hfresh hafter hadmissible
    apply hbound.trans
    have hevent : NewAdmissibleSignerView before key (· = hashOutputFewTimeView output) result :=
      ⟨payload, output, hfresh, hafter, hadmissible, rfl⟩
    exact (le_of_eq (if_pos hevent).symm).trans (ENNReal.le_tsum (hashOutputFewTimeView output))
  · have hcache := simulateQ_romImpl_cache_le (signWithView key message) before result hresult
    have hnoNew (input : HashInput) (output : HashOutput) (hfresh : before input = none)
        (hmessage : MessageHashInput key.parameter input) (hafter : result.2 input = some output) :
        ¬ Admissible (truncateMessageDigest output) := by
      intro hadmissible
      obtain ⟨payload, rfl⟩ := hmessage
      exact hnew ⟨payload, output, hfresh, hafter, hadmissible, trivial⟩
    have hcounts (index : Index) : cachedIndexMultiplicity key.parameter result.2 index = cachedIndexMultiplicity key.parameter before index :=
      cacheMessageWeight_of_no_new key.parameter _ before result.2 hcache hnoNew
    simp only [rawIndexSigningGrowth, observedWeightedPowerMoments, weightedPowerMoment,
      hcounts, tsub_self, zero_mul, Finset.sum_const_zero, zero_le]

end SphincsSecurity.Concrete
