import SphincsSecurity.Proof.FutureCoverageBound
import SphincsSecurity.Proof.FrozenSigningLog

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem binomialOccupancyMoment_mono {n : Nat} (first second : Fin n → Option FewTimeView)
    (hviews : ∀ slot view, first slot = some view → second slot = some view) (degree : Nat) :
    binomialOccupancyMoment first degree ≤ binomialOccupancyMoment second degree := by
  apply Finset.sum_le_sum
  intro index _
  apply Nat.choose_le_choose
  apply Finset.card_le_card
  intro slot hslot
  obtain ⟨view, hview, hindex⟩ := (Finset.mem_filter.mp hslot).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, view, hviews slot view hview, hindex⟩

theorem coverageOccupancyCompletion_mono_moments {m n : Nat}
    (first : Fin m → Option FewTimeView) (second : Fin n → Option FewTimeView)
    (h : ∀ degree, binomialOccupancyMoment first degree ≤ binomialOccupancyMoment second degree) (remaining : Nat) :
    coverageOccupancyCompletion first remaining ≤ coverageOccupancyCompletion second remaining := by
  apply Finset.sum_le_sum
  intro degree _
  exact mul_le_mul' le_rfl (binomialCompletion_mono (fun d => Nat.cast_le.mpr (h d)) remaining (degree + 1))

theorem eligibleSigningViews_completion_le (answers : HashInput → Option HashOutput) (root : Digest)
    (payload : HashInput) (log : QueryLog SigningSpec) (remaining : Nat) :
    coverageOccupancyCompletion (eligibleSigningViews answers root payload log) remaining ≤
      coverageOccupancyCompletion (observedOptionalSigningViews answers root log) remaining :=
  coverageOccupancyCompletion_mono_moments _ _
    (binomialOccupancyMoment_mono _ _ (fun _ _ hview => eligibleSigningView?_some_observed hview)) remaining

theorem binomialCompletion_ne_top (moments : Nat → ENNReal) (hfinite : ∀ degree, moments degree ≠ ∞)
    (remaining degree : Nat) : binomialCompletion moments remaining degree ≠ ∞ := by
  induction remaining generalizing degree with
  | zero => exact hfinite degree
  | succ remaining ih =>
      cases degree with
      | zero => exact ih 0
      | succ degree =>
          rw [binomialCompletion_succ]
          exact ENNReal.add_ne_top.mpr ⟨ih _, ENNReal.div_ne_top (ih _) (by norm_num [Index, totalHeight])⟩

theorem coverageOccupancyCompletion_ne_top {n : Nat} (views : Fin n → Option FewTimeView) (remaining : Nat) :
    coverageOccupancyCompletion views remaining ≠ ∞ := by
  apply ENNReal.sum_ne_top.mpr
  intro degree _
  exact ENNReal.mul_ne_top (by finiteness) (binomialCompletion_ne_top _ (fun _ => by finiteness) remaining (degree + 1))

noncomputable def observedLogOccupancyCompletion (remaining : Nat) (key : SecretKey) (state : CoverLogState) : ENNReal :=
  coverageOccupancyCompletion (observedOptionalSigningViews (messageAnswers key.parameter state.1) key.root state.2) remaining

theorem observedLogOccupancyCompletion_mono (remaining : Nat) (key : SecretKey) (before after : CoverLogState)
    (hcache : before.1 ≤ after.1) (hprefix : before.2.IsPrefix after.2)
    (hsigned : SigningDigestsCached key.parameter before.1 key.root before.2) :
    observedLogOccupancyCompletion remaining key before ≤ observedLogOccupancyCompletion remaining key after := by
  have hstable := observedOptionalSigningViews_cache_stable key.parameter key.root before.1 after.1 before.2 hcache hsigned
  unfold observedLogOccupancyCompletion
  rw [← hstable]
  exact coverageOccupancyCompletion_mono_moments _ _
    (observed_binomialOccupancy_prefix_mono _ _ _ _ hprefix) remaining

noncomputable def occupancyCompletionReuseCharge (remaining : Nat) (key : SecretKey) (q : Nat)
    (state : CoverLogState) (message : Message) : ENNReal :=
  ∑ degree ∈ Finset.range 14, (coverageFactorialCoefficient (degree + 1) * (degree + 1).factorial : Nat) *
    binomialCompletion (binomialReuseMoments key q state message) remaining (degree + 1)

theorem expected_logTraced_sign_occupancyCompletion_le (remaining : Nat) (key : SecretKey) (q : Nat)
    (hq : q ≤ 2 ^ 127) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      observedLogOccupancyCompletion remaining key result.2) ≤
      observedLogOccupancyCompletion (remaining + 1) key state + occupancyCompletionReuseCharge remaining key q state message := by
  simp only [observedLogOccupancyCompletion, coverageOccupancyCompletion, occupancyCompletionReuseCharge, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro degree _
  simp_rw [mul_left_comm (Pr[= _ | _])]
  rw [ENNReal.tsum_mul_left, ← mul_add]
  exact mul_le_mul' le_rfl (expected_logTraced_sign_completion_le key q remaining (degree + 1) hq state hsigned hcache message)

end SphincsSecurity.Concrete
