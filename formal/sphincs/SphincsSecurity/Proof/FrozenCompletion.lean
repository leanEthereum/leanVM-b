import SphincsSecurity.Proof.FrozenSigningLog

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def frozenLogCompletion (key : SecretKey) (q degree : Nat) (state : CoverLogState) : ENNReal :=
  if QueryCache.enncard state.1 ≤ q then
    binomialCompletion (fun degree => frozenLogBinomialOccupancy key degree state)
      (signatureLimit - state.2.length) degree else 0

theorem frozenLogCompletion_of_valid (key : SecretKey) (q degree : Nat) (state : CoverLogState)
    (hvalid : SigningTranscript.Valid state.2) :
    frozenLogCompletion key q degree state = cappedLogCompletion key q degree state := by
  simp only [frozenLogCompletion, cappedLogCompletion, hvalid, true_and,
    frozenLogBinomialOccupancy_of_valid key _ state hvalid]

theorem expected_logTraced_frozenCompletion_le (key : SecretKey) (q degree : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (input : (OracleWorld + SigningSpec).Domain) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      frozenLogCompletion key q degree result.2) ≤
        frozenLogCompletion key q degree state + completionReuseStepCharge key q degree state input := by
  by_cases hlimit : state.2.length < signatureLimit
  · have hvalid : SigningTranscript.Valid state.2 := Nat.le_of_lt hlimit
    have hstep : ValidSigningStep state.2 input := by
      cases input
      · exact hvalid
      · exact hlimit
    rw [frozenLogCompletion_of_valid key q degree state hvalid]
    apply le_trans (le_of_eq ?_) (expected_logTraced_cappedCompletion_le key q degree hq state hsigned input)
    apply tsum_congr
    intro result
    by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
    · rw [frozenLogCompletion_of_valid key q degree result.2
        ((logTracedMappedAdversaryImpl_validSigningStep key input state result hresult).mpr hstep)]
    · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
  · have hatlimit : signatureLimit ≤ state.2.length := Nat.le_of_not_gt hlimit
    have hcharge : completionReuseStepCharge key q degree state input = 0 := by
      cases input with
      | inl _ => rfl
      | inr message => simp only [completionReuseStepCharge, hlimit, false_and, if_false]
    rw [hcharge, add_zero]
    have hpoint (result : (OracleWorld + SigningSpec).Range input × CoverLogState)
        (hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)) :
        frozenLogCompletion key q degree result.2 ≤ frozenLogCompletion key q degree state := by
      have hcache := logTracedMappedAdversaryImpl_cache_le key input state result hresult
      by_cases hcap : QueryCache.enncard state.1 ≤ q
      · rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
        obtain ⟨base, hbase, rfl⟩ := hresult
        have hlength : signatureLimit ≤ (state.2 ++ signingLogFragment input base.1).length := by
          rw [List.length_append]
          exact hatlimit.trans (Nat.le_add_right _ _)
        have hstable := observedOptionalSigningViews_cache_stable key.parameter key.root state.1 base.2
          (state.2.take signatureLimit) hcache (hsigned.take signatureLimit)
        rw [frozenLogCompletion, frozenLogCompletion, if_pos hcap]
        split_ifs
        · simp only [Nat.sub_eq_zero_of_le hlength, Nat.sub_eq_zero_of_le hatlimit, binomialCompletion_zero,
            frozenLogBinomialOccupancy, observedLogBinomialOccupancy]
          rw [List.take_append_of_le_length hatlimit, hstable]
        · exact bot_le
      · have hafter : ¬ QueryCache.enncard result.2.1 ≤ q :=
          fun h => hcap ((QueryCache.enncard_mono hcache).trans h)
        rw [frozenLogCompletion, if_neg hafter, frozenLogCompletion, if_neg hcap]
    calc
      _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
          frozenLogCompletion key q degree state := by
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
        · exact mul_le_mul' le_rfl (hpoint result hresult)
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
      _ ≤ _ := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' tsum_probOutput_le_one

end SphincsSecurity.Concrete
