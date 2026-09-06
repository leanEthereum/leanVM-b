import SphincsSecurity.Proof.AmortizedExceptionCharge

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

theorem expected_runExceptionMonitor_potential_le_queryCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : QueryCache HashSpec → Bool → ℝ≥0∞) (charge : QueryCache HashSpec → HashInput → ℝ≥0∞)
    (hstep : ∀ query cache, Finite cache → ∀ hit,
      (∑' result, Pr[= result | (romImpl query).run cache] *
        potential result.2 (hit || queryException exception cache query result.1)) ≤
      potential cache hit + hashQueryCharge charge cache query)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool) :
    (∑' result, Pr[= result | runExceptionMonitor exception computation cache hit] * potential result.1.2 result.2) ≤
      potential cache hit + expectedQueryCharge charge computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp [runExceptionMonitor]
  | query_bind query next ih =>
      rw [runExceptionMonitor, OracleComp.construct_query_bind, tsum_probOutput_bind_mul, expectedQueryCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (romImpl query).run cache] *
            (potential result.2 (hit || queryException exception cache query result.1) +
              expectedQueryCharge charge (next result.1) result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : result ∈ support ((romImpl query).run cache)
          · exact mul_le_mul' le_rfl (ih result.1 result.2 (finite_of_mem_support_romImpl hfinite hr) _)
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | (romImpl query).run cache] *
            potential result.2 (hit || queryException exception cache query result.1)) +
            ∑' result, Pr[= result | (romImpl query).run cache] *
              expectedQueryCharge charge (next result.1) result.2 := by
          simp_rw [mul_add, ENNReal.tsum_add]
        _ ≤ (potential cache hit + hashQueryCharge charge cache query) +
            ∑' result, Pr[= result | (romImpl query).run cache] *
              expectedQueryCharge charge (next result.1) result.2 :=
          add_le_add (hstep query cache hfinite hit) le_rfl
        _ = _ := by rw [add_assoc]

noncomputable def stoppedBadPotential (Bad : QueryCache HashSpec → Prop)
    (potential : QueryCache HashSpec → Nat) (ε : ℝ≥0∞) (cache : QueryCache HashSpec) (hit : Bool) : ℝ≥0∞ :=
  open Classical in
  if hit then 0 else if Bad cache then 1 else min 1 ((potential cache : ℝ≥0∞) * ε)

theorem stoppedBadPotential_le_one (Bad : QueryCache HashSpec → Prop)
    (potential : QueryCache HashSpec → Nat) (ε : ℝ≥0∞) (cache : QueryCache HashSpec) (hit : Bool) :
    stoppedBadPotential Bad potential ε cache hit ≤ 1 := by
  unfold stoppedBadPotential
  split_ifs <;> simp

variable (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
  (Bad : QueryCache HashSpec → Prop) (potential : QueryCache HashSpec → Nat)
  (charge : QueryCache HashSpec → HashInput → Nat) (ε : ℝ≥0∞)
  (hstep : ∀ target : Digest,
    Pr[fun answer => truncateHash answer = target | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ ε)
  (hamortized : ∀ cache : QueryCache HashSpec, Finite cache → ¬ Bad cache → ∀ input : HashInput,
    cache input = none → ∃ targets : Finset Digest, targets.card ≤ potential cache + charge cache input ∧
      ∀ answer : HashOutput, ¬ exception cache input answer → truncateHash answer ∉ targets →
        ¬ Bad (cache.cacheQuery input answer) ∧
          potential (cache.cacheQuery input answer) + targets.card ≤ potential cache + charge cache input)

include hstep hamortized

theorem expected_stoppedBadPotential_query_le (query : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool) :
    (∑' result, Pr[= result | (romImpl query).run cache] *
      stoppedBadPotential Bad potential ε result.2 (hit || queryException exception cache query result.1)) ≤
      stoppedBadPotential Bad potential ε cache hit +
        hashQueryCharge (fun cache input => (charge cache input : ℝ≥0∞) * ε) cache query := by
  classical
  have hmass : (∑' result, Pr[= result | (romImpl query).run cache] *
      stoppedBadPotential Bad potential ε result.2 (hit || queryException exception cache query result.1)) ≤ 1 := by
    calc
      _ ≤ ∑' result, Pr[= result | (romImpl query).run cache] * 1 :=
        ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (stoppedBadPotential_le_one _ _ _ _ _)
      _ = _ := by simp only [mul_one, romImpl_query_mass]
  cases hit with
  | true => simp [stoppedBadPotential]
  | false =>
      by_cases hbad : Bad cache
      · simp only [stoppedBadPotential, Bool.false_eq_true, if_false, if_pos hbad] at ⊢
        exact hmass.trans le_self_add
      · by_cases hlarge : 1 ≤ (potential cache : ℝ≥0∞) * ε
        · have heq : stoppedBadPotential Bad potential ε cache false = 1 := by
            simp [stoppedBadPotential, hbad, min_eq_left hlarge]
          rw [heq]
          exact hmass.trans le_self_add
        · have hsmall : min 1 ((potential cache : ℝ≥0∞) * ε) = (potential cache : ℝ≥0∞) * ε :=
            min_eq_right (le_of_not_ge hlarge)
          cases query with
          | inl sample =>
              have hrun : (romImpl (.inl sample)).run cache =
                  (fun answer => (answer, cache)) <$> (liftM (unifSpec.query sample) : ProbComp _) := rfl
              rw [hrun, tsum_probOutput_map_mul]
              simp only [queryException, Bool.false_or, hashQueryCharge, Sum.elim_inl, add_zero]
              rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
          | inr input =>
              change (∑' result, Pr[= result | (randomOracle input).run cache] *
                stoppedBadPotential Bad potential ε result.2 (false || queryException exception cache (.inr input) result.1)) ≤ _
              by_cases hfresh : cache input = none
              · obtain ⟨targets, hcard, htargets⟩ := hamortized cache hfinite hbad input hfresh
                let remainder := potential cache + charge cache input - targets.card
                have hremain : targets.card + remainder = potential cache + charge cache input :=
                  Nat.add_sub_of_le hcard
                have hpoint (answer : HashOutput) :
                    stoppedBadPotential Bad potential ε (cache.cacheQuery input answer)
                        (false || queryException exception cache (.inr input) answer) ≤
                      (if truncateHash answer ∈ targets then 1 else 0) + (remainder : ℝ≥0∞) * ε := by
                  by_cases ht : truncateHash answer ∈ targets
                  · rw [if_pos ht]
                    exact (stoppedBadPotential_le_one _ _ _ _ _).trans le_self_add
                  · rw [if_neg ht, zero_add]
                    by_cases hx : exception cache input answer
                    · simp [stoppedBadPotential, queryException, hfresh, hx]
                    · obtain ⟨hclean, hp⟩ := htargets answer hx ht
                      simp only [stoppedBadPotential, queryException, hfresh, hx, and_false, decide_false,
                        Bool.false_or, Bool.false_eq_true, if_false, if_neg hclean]
                      exact (min_le_right _ _).trans (mul_le_mul' (by exact_mod_cast Nat.le_sub_of_add_le hp) le_rfl)
                rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
                calc
                  _ ≤ ∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                      ((if truncateHash answer ∈ targets then 1 else 0) + (remainder : ℝ≥0∞) * ε) :=
                    ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (hpoint answer)
                  _ = Pr[fun answer => truncateHash answer ∈ targets | ($ᵗ HashOutput : ProbComp HashOutput)] +
                      (remainder : ℝ≥0∞) * ε := by
                    simp_rw [mul_add, ENNReal.tsum_add]
                    simp only [mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite]
                    rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
                  _ ≤ (targets.card : ℝ≥0∞) * ε + (remainder : ℝ≥0∞) * ε :=
                    add_le_add (probEvent_mem_targets_le hstep targets) le_rfl
                  _ = _ := by
                    rw [← add_mul, ← Nat.cast_add, hremain, Nat.cast_add, add_mul]
                    simp only [stoppedBadPotential, Bool.false_eq_true, if_false, if_neg hbad, hsmall,
                      hashQueryCharge, Sum.elim_inr]
              · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hfresh
                rw [randomOracle, QueryImpl.withCaching_run_some _ hanswer, tsum_probOutput_pure_mul]
                simp only [queryException, hfresh, false_and, decide_false, Bool.false_or]
                exact le_self_add

theorem probEvent_bad_without_exception_le_expectedCharge (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hclean : ¬ Bad cache) :
    Pr[fun result => Bad result.1.2 ∧ result.2 = false | runExceptionMonitor exception computation cache false] ≤
      (potential cache : ℝ≥0∞) * ε + expectedQueryCharge (fun cache input => (charge cache input : ℝ≥0∞)) computation cache * ε := by
  classical
  have hbound := expected_runExceptionMonitor_potential_le_queryCharge exception (stoppedBadPotential Bad potential ε)
    (fun cache input => (charge cache input : ℝ≥0∞) * ε)
    (expected_stoppedBadPotential_query_le exception Bad potential charge ε hstep hamortized)
    computation cache hfinite false
  rw [expectedQueryCharge_mul] at hbound
  apply le_trans _ (hbound.trans (add_le_add (by simp [stoppedBadPotential, hclean]) le_rfl))
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases h : Bad result.1.2 ∧ result.2 = false
  · simp [h.1, h.2, stoppedBadPotential]
  · simp [h]

end SphincsSecurity
