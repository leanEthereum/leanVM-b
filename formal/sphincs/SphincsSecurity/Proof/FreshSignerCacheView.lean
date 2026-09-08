import SphincsSecurity.Proof.SelectedDigestCache
import SphincsSecurity.Proof.FewTimeFreshMass
import SphincsSecurity.Proof.WeightedSigningMoments

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def NewAdmissibleSignerView (before : QueryCache HashSpec) (key : SecretKey) (P : FewTimeView → Prop)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : Prop :=
  ∃ payload output, before (tweakableHashInput key.parameter .message payload) = none ∧
    result.2 (tweakableHashInput key.parameter .message payload) = some output ∧
    Admissible (truncateMessageDigest output) ∧ P (hashOutputFewTimeView output)

theorem new_admissible_loop_freshSelected (attempts : Nat) (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (selected : Option (Randomness × Index × (DigestTree → FtsLeaf)))
    (hloop : (selected, after) ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run before))
    (P : FewTimeView → Prop) (payload : HashInput) (output : HashOutput)
    (hbefore : before (tweakableHashInput key.parameter .message payload) = none)
    (hafter : after (tweakableHashInput key.parameter .message payload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) (hP : P (hashOutputFewTimeView output)) :
    FreshSelectedView before key message P (selected, after) := by
  obtain ⟨randomness, index, leaves, rfl, hpayload⟩ := signDigestLoop_new_admissible_selected attempts key message
    before after selected hloop payload output hbefore hafter hadmissible
  obtain ⟨selectedOutput, houtput, _, hview⟩ := signDigestLoop_selected_cached_output attempts key message before after randomness index leaves hloop
  have hout : output = selectedOutput := Option.some.inj ((hpayload ▸ hafter).symm.trans houtput)
  refine ⟨randomness, index, leaves, rfl, hpayload ▸ hbefore, ?_⟩
  rwa [hout, hview] at hP

theorem probEvent_signWithView_newAdmissible_le_freshSelected (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (P : FewTimeView → Prop) :
    Pr[NewAdmissibleSignerView before key P | (simulateQ romImpl (signWithView key message)).run before] ≤
      Pr[FreshSelectedView before key message P |
        (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] := by
  rw [signWithView, simulateQ_bind, StateT.run_bind]
  refine probEvent_bind_le_probEvent (p := FreshSelectedView before key message P) ?_
  intro loopResult hloop hnotFresh
  obtain ⟨selected, loopCache⟩ := loopResult
  cases selected with
  | none =>
      apply probEvent_eq_zero
      intro result hresult hevent
      have heq : result = ((none, none), loopCache) := by
        simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using hresult
      rw [heq] at hevent
      obtain ⟨payload, output, hbefore, hafter, hadmissible, hP⟩ := hevent
      exact hnotFresh (new_admissible_loop_freshSelected digestAttemptLimit key message before loopCache none hloop P payload output
        hbefore hafter hadmissible hP)
  | some data =>
      obtain ⟨randomness, index, leaves⟩ := data
      apply probEvent_eq_zero
      intro result hresult hevent
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨⟨signature, after⟩, hsignature, hpure⟩ := hresult
      have heq : result = ((signature, some (selectedFewTimeView index leaves)), after) := by
        simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using hpure
      rw [heq] at hevent
      obtain ⟨payload, output, hbefore, hafter, hadmissible, hP⟩ := hevent
      have hfinish : (signature, after) ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (signAfterDigest key randomness index leaves)).run loopCache) := by
        simpa only [simulateQ_romImpl_liftM] using hsignature
      change after (tweakableHashInput key.parameter .message payload) = some output at hafter
      rw [signAfterDigest_message_cache_eq key randomness index leaves loopCache after signature hfinish payload] at hafter
      exact hnotFresh (new_admissible_loop_freshSelected digestAttemptLimit key message before loopCache
        (some (randomness, index, leaves)) hloop P payload output hbefore hafter hadmissible hP)

theorem probEvent_signWithView_newAdmissible_le_mass_mul_uniform
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec) (P : FewTimeView → Prop) :
    Pr[NewAdmissibleSignerView before key P | (simulateQ romImpl (signWithView key message)).run before] ≤
      freshDigestSelectionProbability key message before * Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] :=
  (probEvent_signWithView_newAdmissible_le_freshSelected key message before P).trans_eq
    (probEvent_signDigestLoop_freshSelected_eq_mass_mul_uniform digestAttemptLimit key message
      before before P (onlyRejectedNewMessageEntries_self before key message))

theorem expected_newAdmissibleSignerView_weight_le_mass_mul
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec) (weight : FewTimeView → ENNReal) :
    (∑' source, Pr[NewAdmissibleSignerView before key (· = source) |
      (simulateQ romImpl (signWithView key message)).run before] * weight source) ≤
      freshDigestSelectionProbability key message before *
        ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight source := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro source
  rw [← mul_assoc]
  apply mul_le_mul' _ le_rfl
  simpa only [probEvent_eq_eq_probOutput] using
    probEvent_signWithView_newAdmissible_le_mass_mul_uniform key message before (· = source)

theorem expected_signWithView_newAdmissible_cost_le_mass_mul
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (cost : ((Option Signature × Option FewTimeView) × QueryCache HashSpec) → ENNReal)
    (weight : FewTimeView → ENNReal)
    (hcost : ∀ result ∈ support ((simulateQ romImpl (signWithView key message)).run before),
      cost result ≤ ∑' source, if NewAdmissibleSignerView before key (· = source) result then weight source else 0) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] * cost result) ≤
      freshDigestSelectionProbability key message before *
        ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight source := by
  apply le_trans ?_ (expected_newAdmissibleSignerView_weight_le_mass_mul key message before weight)
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        ∑' source, if NewAdmissibleSignerView before key (· = source) result then weight source else 0 := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
      · exact mul_le_mul' le_rfl (hcost result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = _ := by
      simp only [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro source
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro result
      split_ifs <;> simp

theorem probEvent_signWithView_newAdmissible_le_uniform (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (P : FewTimeView → Prop) :
    Pr[NewAdmissibleSignerView before key P | (simulateQ romImpl (signWithView key message)).run before] ≤
      Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] :=
  (probEvent_signWithView_newAdmissible_le_mass_mul_uniform key message before P).trans
    (mul_le_of_le_one_left' (freshDigestSelectionProbability_le_one key message before))

theorem expected_newAdmissibleSignerView_weight_le (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (weight : FewTimeView → ENNReal) :
    (∑' source, Pr[NewAdmissibleSignerView before key (· = source) | (simulateQ romImpl (signWithView key message)).run before] * weight source) ≤
      ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight source :=
  (expected_newAdmissibleSignerView_weight_le_mass_mul key message before weight).trans
    (mul_le_of_le_one_left' (freshDigestSelectionProbability_le_one key message before))

end SphincsSecurity.Concrete
