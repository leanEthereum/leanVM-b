import SphincsSecurity.Proof.InterleavedCoverCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def ValidSigningStep (log : QueryLog SigningSpec) : (OracleWorld + SigningSpec).Domain → Prop
  | .inl _ => log.length ≤ signatureLimit
  | .inr _ => log.length < signatureLimit

theorem logTracedMappedAdversaryImpl_validSigningStep (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState)
    (result : (OracleWorld + SigningSpec).Range input × CoverLogState)
    (hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)) :
    SigningTranscript.Valid result.2.2 ↔ ValidSigningStep state.2 input := by
  rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
  obtain ⟨base, _, rfl⟩ := hresult
  cases input <;> simp [SigningTranscript.Valid, signingLogFragment, ValidSigningStep]

theorem ValidSigningStep.valid_before {log : QueryLog SigningSpec}
    {input : (OracleWorld + SigningSpec).Domain} (h : ValidSigningStep log input) : SigningTranscript.Valid log := by
  cases input with
  | inl _ => exact h
  | inr _ => exact Nat.le_of_lt h

noncomputable def validInterleavedCoverStepCharge (key : SecretKey) (q : Nat)
    (state : CoverLogState) (input : (OracleWorld + SigningSpec).Domain) : ENNReal :=
  if ValidSigningStep state.2 input then interleavedCoverStepCharge key q state input else 0

def ValidCappedSigningCacheCovered (key : SecretKey) (q : Nat) (state : CoverLogState) : Prop :=
  SigningTranscript.Valid state.2 ∧ CappedSigningCacheCovered key q state

theorem probEvent_interleaved_validCappedCover_step_le (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (input : (OracleWorld + SigningSpec).Domain) :
    Pr[fun result => ValidCappedSigningCacheCovered key q result.2 | (logTracedMappedAdversaryImpl key input).run state] ≤
      (if ValidCappedSigningCacheCovered key q state then 1 else 0) + validInterleavedCoverStepCharge key q state input := by
  by_cases hstep : ValidSigningStep state.2 input
  · have hbound := probEvent_interleaved_cappedCover_step_le key q hq state hsigned input
    simpa only [ValidCappedSigningCacheCovered, hstep.valid_before, true_and,
      validInterleavedCoverStepCharge, if_pos hstep] using
      (probEvent_mono (fun _ _ h => h.2)).trans hbound
  · have hzero : Pr[fun result => ValidCappedSigningCacheCovered key q result.2 |
        (logTracedMappedAdversaryImpl key input).run state] = 0 := by
      apply probEvent_eq_zero
      intro result hresult hcover
      exact hstep ((logTracedMappedAdversaryImpl_validSigningStep key input state result hresult).mp hcover.1)
    rw [hzero]
    exact bot_le

noncomputable def expectedValidInterleavedCoverCharge {α : Type} (key : SecretKey) (q : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : CoverLogState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => validInterleavedCoverStepCharge key q state input +
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * next result.1 result.2) computation

@[simp] theorem expectedValidInterleavedCoverCharge_pure {α : Type} (key : SecretKey) (q : Nat)
    (value : α) (state : CoverLogState) : expectedValidInterleavedCoverCharge key q (pure value) state = 0 := rfl

theorem expectedValidInterleavedCoverCharge_query_bind {α : Type} (key : SecretKey) (q : Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedValidInterleavedCoverCharge key q (OracleSpec.query input >>= next) state =
      validInterleavedCoverStepCharge key q state input + ∑' result,
        Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * expectedValidInterleavedCoverCharge key q (next result.1) result.2 := by
  cases input <;> rfl

theorem probEvent_interleaved_validCappedCover_le_charge {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    Pr[fun result => ValidCappedSigningCacheCovered key q result.2 | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] ≤
      (if ValidCappedSigningCacheCovered key q state then 1 else 0) + expectedValidInterleavedCoverCharge key q computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, probEvent_pure, expectedValidInterleavedCoverCharge_pure, add_zero]
      exact le_rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, probEvent_bind_eq_tsum, expectedValidInterleavedCoverCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
            ((if ValidCappedSigningCacheCovered key q result.2 then 1 else 0) + expectedValidInterleavedCoverCharge key q (next result.1) result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
          · exact mul_le_mul' le_rfl (ih result.1 result.2
              (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned result hresult))
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ = Pr[fun result => ValidCappedSigningCacheCovered key q result.2 | (logTracedMappedAdversaryImpl key input).run state] +
            ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
              expectedValidInterleavedCoverCharge key q (next result.1) result.2 := by
          simp only [mul_add, ENNReal.tsum_add, mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite]
        _ ≤ ((if ValidCappedSigningCacheCovered key q state then 1 else 0) + validInterleavedCoverStepCharge key q state input) +
            ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
              expectedValidInterleavedCoverCharge key q (next result.1) result.2 :=
          add_le_add (probEvent_interleaved_validCappedCover_step_le key q hq state hsigned input) le_rfl
        _ = _ := by rw [add_assoc]

theorem probEvent_interleaved_validObservedCover_from_emptyLog_le_charge {α : Type}
    (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (forgery : α → Forgery)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])), QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => SigningTranscript.Valid result.2.2 ∧
      ObservedFewTimeCover (messageAnswers key.parameter result.2.1) key.root result.2.2 (forgery result.1) |
        (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] ≤
      expectedValidInterleavedCoverCharge key q computation (cache, []) := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hbound := probEvent_interleaved_validCappedCover_le_charge key q hq computation (cache, []) hsigned
  rw [if_neg (fun h => not_signingCacheCovered_nil key.parameter key.root cache h.2.2), zero_add] at hbound
  apply (probEvent_mono (fun result hresult hcover => And.intro hcover.1 (And.intro (hbudget result hresult)
    (observedFewTimeCover_signingCacheCovered key.parameter key.root result.2.1 result.2.2 (forgery result.1) hcover.2)))).trans hbound

theorem expectedValidInterleavedCoverCharge_of_invalid {α : Type} (key : SecretKey) (q : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hinvalid : ¬ SigningTranscript.Valid state.2) : expectedValidInterleavedCoverCharge key q computation state = 0 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedValidInterleavedCoverCharge_query_bind, validInterleavedCoverStepCharge,
        if_neg (fun h => hinvalid h.valid_before), zero_add]
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
      · rw [ih result.1 result.2 (fun h => hinvalid
          ((logTracedMappedAdversaryImpl_validSigningStep key input state result hresult).mp h).valid_before), mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]

theorem expectedValidInterleavedCoverCharge_signing_at_limit {α : Type} (key : SecretKey) (q : Nat)
    (message : Message) (next : Option Signature → OracleComp (OracleWorld + SigningSpec) α)
    (state : CoverLogState) (hlimit : signatureLimit ≤ state.2.length) :
    expectedValidInterleavedCoverCharge key q (OracleSpec.query (spec := OracleWorld + SigningSpec) (.inr message) >>= next) state = 0 := by
  have hstep : ¬ ValidSigningStep state.2 (.inr message) := Nat.not_lt.mpr hlimit
  rw [expectedValidInterleavedCoverCharge_query_bind, validInterleavedCoverStepCharge, if_neg hstep, zero_add]
  apply ENNReal.tsum_eq_zero.mpr
  intro result
  by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
  · rw [expectedValidInterleavedCoverCharge_of_invalid key q _ result.2 (fun h => hstep
      ((logTracedMappedAdversaryImpl_validSigningStep key (.inr message) state result hresult).mp h)), mul_zero]
  · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]

theorem expectedValidInterleavedCoverCharge_le {α : Type} (key : SecretKey) (q : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedValidInterleavedCoverCharge key q computation state ≤ expectedInterleavedCoverCharge key q computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => exact le_rfl
  | query_bind input next ih =>
      rw [expectedValidInterleavedCoverCharge_query_bind, expectedInterleavedCoverCharge_query_bind]
      apply add_le_add
      · unfold validInterleavedCoverStepCharge
        split_ifs
        · exact le_rfl
        · exact bot_le
      · exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2)

end SphincsSecurity.Concrete
