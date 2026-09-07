import SphincsSecurity.Proof.CacheCapacityStep

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem simulateQ_logTraced_support_nonempty {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    (support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state)).Nonempty := by
  by_contra hnone
  have hzero : (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state]) = 0 :=
    ENNReal.tsum_eq_zero.mpr (fun result => probOutput_eq_zero_of_not_mem_support (fun h => hnone ⟨result, h⟩))
  rw [simulateQ_logTraced_mass] at hzero
  exact one_ne_zero hzero

theorem simulateQ_logTraced_initial_cache_bound {α : Type} (key : SecretKey) (q : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state),
      QueryCache.enncard result.2.1 ≤ q) : QueryCache.enncard state.1 ≤ q := by
  obtain ⟨result, hresult⟩ := simulateQ_logTraced_support_nonempty key computation state
  exact (QueryCache.enncard_mono (simulateQ_logTraced_extends key computation state result hresult).1).trans (hbudget result hresult)

theorem simulateQ_logTraced_tail_cache_bound {α : Type} (key : SecretKey) (q : Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) (OracleSpec.query input >>= next)).run state),
      QueryCache.enncard result.2.1 ≤ q)
    (middle : (OracleWorld + SigningSpec).Range input × CoverLogState)
    (hmiddle : middle ∈ support ((logTracedMappedAdversaryImpl key input).run state)) :
    ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) (next middle.1)).run middle.2),
      QueryCache.enncard result.2.1 ≤ q := by
  intro result hresult
  apply hbudget result
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
  exact ⟨middle, hmiddle, hresult⟩

noncomputable def expectedCapacityReuseCharge {α : Type} (key : SecretKey) (q : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : CoverLogState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => capacityReuseStepCharge key q state input +
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * next result.1 result.2) computation

@[simp] theorem expectedCapacityReuseCharge_pure {α : Type} (key : SecretKey) (q : Nat)
    (value : α) (state : CoverLogState) : expectedCapacityReuseCharge key q (pure value) state = 0 := rfl

theorem expectedCapacityReuseCharge_query_bind {α : Type} (key : SecretKey) (q : Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedCapacityReuseCharge key q (OracleSpec.query input >>= next) state =
      capacityReuseStepCharge key q state input + ∑' result,
        Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
          expectedCapacityReuseCharge key q (next result.1) result.2 := by
  cases input <;> rfl

theorem expected_adaptive_cappedCacheCapacityPotential_le {α : Type} (key : SecretKey)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
      cappedCacheCapacityPotential key q result.2) ≤
      cappedCacheCapacityPotential key q state + expectedCapacityReuseCharge key q computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul,
        expectedCapacityReuseCharge_pure, add_zero, le_refl]
  | query_bind input next ih =>
      have htail := simulateQ_logTraced_tail_cache_bound key q input next state hbudget
      have hbefore := simulateQ_logTraced_initial_cache_bound key q (OracleSpec.query input >>= next) state hbudget
      have hstep := expected_logTraced_cappedCacheCapacityPotential_le key q hq state hsigned hbefore input
        (fun result hresult => simulateQ_logTraced_initial_cache_bound key q (next result.1) result.2 (htail result hresult))
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedCapacityReuseCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
            (cappedCacheCapacityPotential key q result.2 + expectedCapacityReuseCharge key q (next result.1) result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
          · exact mul_le_mul' le_rfl (ih result.1 result.2
              (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned result hresult) (htail result hresult))
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * cappedCacheCapacityPotential key q result.2) +
            ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * expectedCapacityReuseCharge key q (next result.1) result.2 := by
          simp only [mul_add, ENNReal.tsum_add]
        _ ≤ (cappedCacheCapacityPotential key q state + capacityReuseStepCharge key q state input) +
            ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * expectedCapacityReuseCharge key q (next result.1) result.2 :=
          add_le_add hstep le_rfl
        _ = _ := by rw [add_assoc]

theorem cappedCacheCapacityPotential_empty_le (key : SecretKey) (q : Nat) (cache : QueryCache HashSpec)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none) :
    cappedCacheCapacityPotential key q (cache, []) ≤ (q : ENNReal) * (7 * (2 : ENNReal) ^ 40 * ((2 ^ 176 : Nat) : ENNReal)⁻¹) := by
  rw [cappedCacheCapacityPotential, if_pos (show SigningTranscript.Valid [] from Nat.zero_le _),
    List.length_nil, Nat.sub_zero, cacheCapacityPotential, cachedFutureCoverage_of_no_message _ _ _ _ _ hnone, zero_add]
  change cacheCapacity q cache * (coverageOccupancyCompletion _ signatureLimit * _) ≤ _
  rw [coverageOccupancyCompletion_empty]
  exact mul_le_mul' tsub_le_self (mul_le_mul' uniformCoverageCompletion_signatureLimit_le le_rfl)

theorem probEvent_adaptive_validObservedCover_le_capacity {α : Type} (key : SecretKey)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (forgery : α → Forgery)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => SigningTranscript.Valid result.2.2 ∧
      ObservedFewTimeCover (messageAnswers key.parameter result.2.1) key.root result.2.2 (forgery result.1) |
      (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] ≤
      (q : ENNReal) * (7 * (2 : ENNReal) ^ 40 * ((2 ^ 176 : Nat) : ENNReal)⁻¹) + expectedCapacityReuseCharge key q computation (cache, []) := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  apply le_trans ?_ ((expected_adaptive_cappedCacheCapacityPotential_le key q hq computation (cache, []) hsigned hbudget).trans
    (add_le_add (cappedCacheCapacityPotential_empty_le key q cache hnone) le_rfl))
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  split_ifs with hcover
  · rw [cappedCacheCapacityPotential, if_pos hcover.1]
    apply le_mul_of_one_le_right'
    exact (one_le_cachedFutureCoverage_of_covered _ _ _ _ _
      (observedFewTimeCover_signingCacheCovered _ _ _ _ _ hcover.2)).trans le_self_add
  · exact bot_le

end SphincsSecurity.Concrete
