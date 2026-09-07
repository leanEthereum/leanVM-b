import SphincsSecurity.Proof.SigningExecutionBudget
import SphincsSecurity.Proof.TargetArrivalCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev expectedSigningExecutionIndexCharge {α : Type} (key : SecretKey) (cap : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) : ENNReal :=
  expectedWeightedIndexCharge key cap (fun _ => signingExecutionHashCost) groups remaining computation state

noncomputable abbrev expectedUnusedSigningExecutionIndexCharge {α : Type} (key : SecretKey) (cap : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) : ENNReal :=
  expectedWeightedIndexCharge key cap (fun _ => unusedSigningExecutionCost) groups remaining computation state

theorem expectedMacroIndexCharge_add_signingExecutionReserve {α : Type} (key : SecretKey) (cap : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedMacroIndexCharge key cap groups remaining computation state +
      expectedUnusedSigningExecutionIndexCharge key cap groups remaining computation state =
      expectedSigningExecutionIndexCharge key cap groups remaining computation state := by
  rw [← expectedWeightedIndexCharge_macro_eq]
  simp only [expectedUnusedSigningExecutionIndexCharge, expectedSigningExecutionIndexCharge]
  rw [← expectedWeightedIndexCharge_add]
  simp_rw [signingMacroHashCost_add_unused_execution]

theorem expectedSigningExecutionIndexCharge_le_queryBudget {α : Type} (key : SecretKey) (cap : Nat) (hcap : cap ≤ 2 ^ 127)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state),
      QueryCache.enncard result.2.1 ≤ cap) :
    expectedSigningExecutionIndexCharge key cap groups remaining computation state ≤
      (q : ENNReal) * cappedRawIndexCacheEnvelope key cap state groups remaining := by
  induction computation using OracleComp.inductionOn generalizing q state with
  | pure value => exact bot_le
  | query_bind input next ih =>
      let cost := signingExecutionHashCost input
      have htail := simulateQ_logTraced_tail_cache_bound key cap input next state hbudget
      have hbefore := simulateQ_logTraced_initial_cache_bound key cap (OracleSpec.query input >>= next) state hbudget
      have hstep := expected_logTraced_cappedRawIndexCacheEnvelope_le key cap hcap state hsigned hbefore input
        (fun result hresult => simulateQ_logTraced_initial_cache_bound key cap (next result.1) result.2 (htail result hresult)) groups remaining hvalid
      have hcost : cost ≤ q := by
        obtain ⟨result, hresult⟩ := simulateQ_logTraced_support_nonempty key (OracleSpec.query input) state
        rw [simulateQ_spec_query] at hresult
        exact (expanded_query_bound_signing_execution key input next q hbound state result hresult).1
      have hrest : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
          expectedSigningExecutionIndexCharge key cap groups remaining (next result.1) result.2) ≤
          ((q - cost : Nat) : ENNReal) * cappedRawIndexCacheEnvelope key cap state groups remaining := by
        calc
          _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
              (((q - cost : Nat) : ENNReal) * cappedRawIndexCacheEnvelope key cap result.2 groups remaining) := by
            apply ENNReal.tsum_le_tsum
            intro result
            by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
            · exact mul_le_mul' le_rfl (ih result.1 (q - cost)
                (expanded_query_bound_signing_execution key input next q hbound state result hresult).2 result.2
                (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned result hresult) (htail result hresult))
            · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
          _ = ((q - cost : Nat) : ENNReal) * ∑' result,
              Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * cappedRawIndexCacheEnvelope key cap result.2 groups remaining := by
            simp_rw [mul_left_comm (Pr[= _ | _])]
            rw [ENNReal.tsum_mul_left]
          _ ≤ _ := mul_le_mul' le_rfl hstep
      simp only [expectedSigningExecutionIndexCharge]
      rw [expectedWeightedIndexCharge_query_bind]
      apply (add_le_add le_rfl hrest).trans_eq
      rw [← add_mul, ← Nat.cast_add, Nat.add_sub_of_le hcost]

theorem expectedSigningExecutionIndexCharge_full_scaled_le_127 {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    expectedSigningExecutionIndexCharge key q ∅ Finset.univ computation (cache, []) * ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≤
      (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hvalid : TargetShapeValid ∅ Finset.univ := by constructor <;> simp
  have hcharge := expectedSigningExecutionIndexCharge_le_queryBudget key q hq ∅ Finset.univ hvalid computation q hbound (cache, []) hsigned hbudget
  have hcache := simulateQ_logTraced_initial_cache_bound key q computation (cache, []) hbudget
  have hpure : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) (pure () : OracleComp (OracleWorld + SigningSpec) Unit)).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q := by
    intro result hresult
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hresult
    subst result
    exact hcache
  have hinitial := expected_adaptive_cappedRawIndex_full_scaled_le_127 key q hq (pure ()) cache hnone hpure
  simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul] at hinitial
  apply (mul_le_mul' hcharge le_rfl).trans
  rw [mul_assoc]
  exact mul_le_mul' le_rfl hinitial

end SphincsSecurity.Concrete
