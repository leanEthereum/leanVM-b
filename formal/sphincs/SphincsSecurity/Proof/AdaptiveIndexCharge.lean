import SphincsSecurity.Proof.SigningMacroBudget
import SphincsSecurity.Proof.TargetIndexEnvelope127

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedMacroIndexCharge {α : Type} (key : SecretKey) (cap : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : CoverLogState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => (signingMacroHashCost input : ENNReal) * cappedRawIndexCacheEnvelope key cap state groups remaining +
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * next result.1 result.2) computation

@[simp] theorem expectedMacroIndexCharge_pure {α : Type} (key : SecretKey) (cap : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (value : α) (state : CoverLogState) :
    expectedMacroIndexCharge key cap groups remaining (pure value) state = 0 := rfl

theorem expectedMacroIndexCharge_query_bind {α : Type} (key : SecretKey) (cap : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedMacroIndexCharge key cap groups remaining (OracleSpec.query input >>= next) state =
      (signingMacroHashCost input : ENNReal) * cappedRawIndexCacheEnvelope key cap state groups remaining +
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
        expectedMacroIndexCharge key cap groups remaining (next result.1) result.2 := by
  cases input <;> rfl

theorem expectedMacroIndexCharge_le_queryBudget {α : Type} (key : SecretKey) (cap : Nat) (hcap : cap ≤ 2 ^ 127)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state),
      QueryCache.enncard result.2.1 ≤ cap) :
    expectedMacroIndexCharge key cap groups remaining computation state ≤
      (q : ENNReal) * cappedRawIndexCacheEnvelope key cap state groups remaining := by
  induction computation using OracleComp.inductionOn generalizing q state with
  | pure value => exact bot_le
  | query_bind input next ih =>
      let cost := signingMacroHashCost input
      have htail := simulateQ_logTraced_tail_cache_bound key cap input next state hbudget
      have hbefore := simulateQ_logTraced_initial_cache_bound key cap (OracleSpec.query input >>= next) state hbudget
      have hstep := expected_logTraced_cappedRawIndexCacheEnvelope_le key cap hcap state hsigned hbefore input
        (fun result hresult => simulateQ_logTraced_initial_cache_bound key cap (next result.1) result.2 (htail result hresult)) groups remaining hvalid
      have hcost : cost ≤ q := by
        obtain ⟨result, hresult⟩ := simulateQ_logTraced_support_nonempty key (OracleSpec.query input) state
        rw [simulateQ_spec_query] at hresult
        exact (expanded_query_bound_signing_macro key input next q hbound state result hresult).1
      have hrest : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
          expectedMacroIndexCharge key cap groups remaining (next result.1) result.2) ≤
          ((q - cost : Nat) : ENNReal) * cappedRawIndexCacheEnvelope key cap state groups remaining := by
        calc
          _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
              (((q - cost : Nat) : ENNReal) * cappedRawIndexCacheEnvelope key cap result.2 groups remaining) := by
            apply ENNReal.tsum_le_tsum
            intro result
            by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
            · exact mul_le_mul' le_rfl (ih result.1 (q - cost)
                (expanded_query_bound_signing_macro key input next q hbound state result hresult).2 result.2
                (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned result hresult) (htail result hresult))
            · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
          _ = ((q - cost : Nat) : ENNReal) * ∑' result,
              Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * cappedRawIndexCacheEnvelope key cap result.2 groups remaining := by
            simp_rw [mul_left_comm (Pr[= _ | _])]
            rw [ENNReal.tsum_mul_left]
          _ ≤ _ := mul_le_mul' le_rfl hstep
      rw [expectedMacroIndexCharge_query_bind]
      apply (add_le_add le_rfl hrest).trans_eq
      rw [← add_mul, ← Nat.cast_add, Nat.add_sub_of_le hcost]

end SphincsSecurity.Concrete
