import SphincsSecurity.Proof.TargetArrivalCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expected_adaptive_cappedCachedTargetEnvelope_le_arrival {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state),
      QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
      cappedCachedTargetEnvelope key q result.2 groups remaining) ≤
      cappedCachedTargetEnvelope key q state groups remaining +
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
          expectedTargetArrivalIndexCharge key q groups remaining computation state := by
  let arrival : ENNReal := ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, expectedWeightedIndexCharge_pure, mul_zero, add_zero, le_refl]
  | query_bind input next ih =>
      have htail := simulateQ_logTraced_tail_cache_bound key q input next state hbudget
      have hbefore := simulateQ_logTraced_initial_cache_bound key q (OracleSpec.query input >>= next) state hbudget
      have hstep := expected_logTraced_cappedCachedTargetEnvelope_le_arrival key q hq state hsigned hbefore input
        (fun result hresult => simulateQ_logTraced_initial_cache_bound key q (next result.1) result.2 (htail result hresult)) groups remaining hvalid
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
      calc
        _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
            (cappedCachedTargetEnvelope key q result.2 groups remaining + arrival * expectedTargetArrivalIndexCharge key q groups remaining (next result.1) result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
          · exact mul_le_mul' le_rfl (ih result.1 result.2
              (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned result hresult) (htail result hresult))
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
            cappedCachedTargetEnvelope key q result.2 groups remaining) +
            arrival * ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
              expectedTargetArrivalIndexCharge key q groups remaining (next result.1) result.2 := by
          simp_rw [mul_add, mul_left_comm (Pr[= _ | _])]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
        _ ≤ (cappedCachedTargetEnvelope key q state groups remaining +
            (targetArrivalHashCost key.parameter state.1 input : ENNReal) * (arrival * cappedRawIndexCacheEnvelope key q state groups remaining)) +
            arrival * ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
              expectedTargetArrivalIndexCharge key q groups remaining (next result.1) result.2 := add_le_add hstep le_rfl
        _ = _ := by
          simp only [expectedTargetArrivalIndexCharge]
          rw [expectedWeightedIndexCharge_query_bind]
          dsimp only [arrival]
          ring

theorem expected_adaptive_cappedCachedTargetEnvelope_add_unused_le {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state),
      QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
      cappedCachedTargetEnvelope key q result.2 groups remaining) +
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
        expectedUnusedTargetIndexCharge key q groups remaining computation state ≤
      cappedCachedTargetEnvelope key q state groups remaining +
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
          expectedMacroIndexCharge key q groups remaining computation state := by
  apply (add_le_add (expected_adaptive_cappedCachedTargetEnvelope_le_arrival key q hq computation state hsigned hbudget groups remaining hvalid) le_rfl).trans_eq
  rw [add_assoc, ← mul_add, expectedTargetArrivalIndexCharge_add_unused]

end SphincsSecurity.Concrete
