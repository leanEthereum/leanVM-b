import SphincsSecurity.Proof.InterleavedCoverStep

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedInterleavedCoverCharge {α : Type} (key : SecretKey) (q : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : CoverLogState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => interleavedCoverStepCharge key q state input +
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * next result.1 result.2) computation

@[simp] theorem expectedInterleavedCoverCharge_pure {α : Type} (key : SecretKey) (q : Nat)
    (value : α) (state : CoverLogState) : expectedInterleavedCoverCharge key q (pure value) state = 0 := rfl

theorem expectedInterleavedCoverCharge_query_bind {α : Type} (key : SecretKey) (q : Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedInterleavedCoverCharge key q (OracleSpec.query input >>= next) state =
      interleavedCoverStepCharge key q state input + ∑' result,
        Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * expectedInterleavedCoverCharge key q (next result.1) result.2 := by
  cases input <;> rfl

theorem probEvent_interleaved_cappedCover_le_charge {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    Pr[fun result => CappedSigningCacheCovered key q result.2 | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] ≤
      (if CappedSigningCacheCovered key q state then 1 else 0) + expectedInterleavedCoverCharge key q computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, probEvent_pure, expectedInterleavedCoverCharge_pure, add_zero]
      exact le_rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, probEvent_bind_eq_tsum, expectedInterleavedCoverCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
            ((if CappedSigningCacheCovered key q result.2 then 1 else 0) + expectedInterleavedCoverCharge key q (next result.1) result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
          · exact mul_le_mul' le_rfl (ih result.1 result.2
              (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned result hresult))
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ = Pr[fun result => CappedSigningCacheCovered key q result.2 | (logTracedMappedAdversaryImpl key input).run state] +
            ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
              expectedInterleavedCoverCharge key q (next result.1) result.2 := by
          simp only [mul_add, ENNReal.tsum_add, mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite]
        _ ≤ ((if CappedSigningCacheCovered key q state then 1 else 0) + interleavedCoverStepCharge key q state input) +
            ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
              expectedInterleavedCoverCharge key q (next result.1) result.2 :=
          add_le_add (probEvent_interleaved_cappedCover_step_le key q hq state hsigned input) le_rfl
        _ = _ := by rw [add_assoc]

theorem observedFewTimeCover_signingCacheCovered (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (forgery : Forgery)
    (hcover : ObservedFewTimeCover (messageAnswers parameter cache) root log forgery) :
    SigningCacheCovered parameter root cache log := by
  obtain ⟨digest, ⟨answer, hanswer, hdigest⟩, hadmissible, hcover⟩ := hcover
  have hdigest' : digest = truncateMessageDigest answer := hdigest.symm
  rw [hdigest'] at hadmissible hcover
  refine ⟨tweakableHashInput parameter .message (messageDigestPayload root forgery.message forgery.signature.randomness),
    answer, ⟨_, rfl⟩, hanswer, hadmissible, ?_⟩
  rw [fixedSigningViews, payloadOf_tweakableHashInput, covered_eligibleSigningViews_iff]
  intro tree
  obtain ⟨entry, signature, signedDigest, hentry, hresponse, _, hsigned, hne, hindex, hleaf⟩ := hcover tree
  exact ⟨entry, hentry, fewTimeTargetView (digestIndex signedDigest) (digestLeaves signedDigest),
    eligibleSigningView?_eq_some hresponse hsigned hne, hindex, hleaf⟩

theorem probEvent_interleaved_observedCover_le_charge {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) (forgery : α → Forgery)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state), QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => ObservedFewTimeCover (messageAnswers key.parameter result.2.1) key.root result.2.2 (forgery result.1) |
      (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] ≤
      (if CappedSigningCacheCovered key q state then 1 else 0) + expectedInterleavedCoverCharge key q computation state := by
  apply (probEvent_mono (fun result hresult hcover => And.intro (hbudget result hresult)
    (observedFewTimeCover_signingCacheCovered key.parameter key.root result.2.1 result.2.2 (forgery result.1) hcover))).trans
  exact probEvent_interleaved_cappedCover_le_charge key q hq computation state hsigned

theorem not_signingCacheCovered_nil (parameter : PublicParameter) (root : Digest) (cache : QueryCache HashSpec) :
    ¬ SigningCacheCovered parameter root cache [] := by
  rintro ⟨input, output, _, _, _, hcover⟩
  obtain ⟨slot, _⟩ := hcover (⟨0, by decide⟩ : FtsTree)
  exact Fin.elim0 slot

theorem probEvent_interleaved_observedCover_from_emptyLog_le_charge {α : Type}
    (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (forgery : α → Forgery)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])), QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => ObservedFewTimeCover (messageAnswers key.parameter result.2.1) key.root result.2.2 (forgery result.1) |
      (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] ≤
      expectedInterleavedCoverCharge key q computation (cache, []) := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hbound := probEvent_interleaved_observedCover_le_charge key q hq computation (cache, []) forgery hsigned hbudget
  rw [if_neg (fun h => not_signingCacheCovered_nil key.parameter key.root cache h.2), zero_add] at hbound
  exact hbound

end SphincsSecurity.Concrete
