import SphincsSecurity.Proof.AmortizedExceptions
import SphincsSecurity.Proof.RomQueryCharge

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable def exceptionReservePotential (potential : QueryCache HashSpec → Nat) (ε : ℝ≥0∞)
    (cache : QueryCache HashSpec) (hit : Bool) : ℝ≥0∞ :=
  (if hit then 1 else 0) + (potential cache : ℝ≥0∞) * ε

variable (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
  (potential : QueryCache HashSpec → Nat) (charge : QueryCache HashSpec → HashInput → Nat) (ε : ℝ≥0∞)
  (hstep : ∀ target : Digest,
    Pr[fun answer => truncateHash answer = target | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ ε)
  (hamortized : ∀ cache : QueryCache HashSpec, Finite cache → ∀ input : HashInput,
    cache input = none → ∃ targets : Finset Digest, ∀ answer : HashOutput,
      (exception cache input answer → truncateHash answer ∈ targets) ∧
      potential (cache.cacheQuery input answer) + targets.card ≤ potential cache + charge cache input)

include hstep hamortized

theorem expected_exceptionReserve_query_le (query : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool) :
    (∑' result, Pr[= result | (romImpl query).run cache] *
      exceptionReservePotential potential ε result.2 (hit || queryException exception cache query result.1)) ≤
      exceptionReservePotential potential ε cache hit +
        hashQueryCharge (fun cache input => (charge cache input : ℝ≥0∞) * ε) cache query := by
  classical
  cases query with
  | inl sample =>
      have hrun : (romImpl (.inl sample)).run cache =
          (fun answer => (answer, cache)) <$> (liftM (unifSpec.query sample) : ProbComp _) := by
        simp [romImpl, unifFwdImpl, QueryImpl.liftTarget, HasQuery.toQueryImpl, StateT.run_monadLift]
      rw [hrun, tsum_probOutput_map_mul]
      simp only [queryException, Bool.or_false, hashQueryCharge, Sum.elim_inl, add_zero]
      rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
  | inr input =>
      change (∑' result, Pr[= result | (randomOracle input).run cache] *
        exceptionReservePotential potential ε result.2 (hit || queryException exception cache (.inr input) result.1)) ≤ _
      by_cases hfresh : cache input = none
      · obtain ⟨targets, htargets⟩ := hamortized cache hfinite input hfresh
        let remainder := potential cache + charge cache input - targets.card
        have hcard : targets.card ≤ potential cache + charge cache input :=
          (Nat.le_add_left _ _).trans (htargets default).2
        have hremain : remainder + targets.card = potential cache + charge cache input :=
          Nat.sub_add_cancel hcard
        have hpotential (answer : HashOutput) : potential (cache.cacheQuery input answer) ≤ remainder :=
          Nat.le_sub_of_add_le (htargets answer).2
        have hpoint (answer : HashOutput) :
            exceptionReservePotential potential ε (cache.cacheQuery input answer)
                (hit || queryException exception cache (.inr input) answer) ≤
              (if hit then 1 else 0) + (if truncateHash answer ∈ targets then 1 else 0) +
                (remainder : ℝ≥0∞) * ε := by
          apply add_le_add _ (mul_le_mul' (by exact_mod_cast hpotential answer) le_rfl)
          by_cases hh : hit = true
          · simp [hh]
          · by_cases hx : exception cache input answer
            · simp [queryException, hfresh, hh, hx, (htargets answer).1 hx]
            · simp [queryException, hfresh, hh, hx]
        rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
        calc
          _ ≤ ∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
              ((if hit then 1 else 0) + (if truncateHash answer ∈ targets then 1 else 0) +
                (remainder : ℝ≥0∞) * ε) :=
            ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (hpoint answer)
          _ = (if hit then 1 else 0) +
              Pr[fun answer => truncateHash answer ∈ targets | ($ᵗ HashOutput : ProbComp HashOutput)] +
                (remainder : ℝ≥0∞) * ε := by
            simp_rw [mul_add, ENNReal.tsum_add]
            simp only [mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite]
            rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul, probEvent_const,
              probFailure_of_liftM_PMF, tsub_zero]
          _ ≤ (if hit then 1 else 0) + (targets.card : ℝ≥0∞) * ε + (remainder : ℝ≥0∞) * ε :=
            add_le_add (add_le_add le_rfl (probEvent_mem_targets_le hstep targets)) le_rfl
          _ = _ := by
            simp only [exceptionReservePotential, hashQueryCharge, Sum.elim_inr]
            rw [add_assoc, ← add_mul, add_comm (targets.card : ℝ≥0∞), ← Nat.cast_add,
              hremain, Nat.cast_add, add_mul, add_assoc]
      · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hfresh
        rw [randomOracle, QueryImpl.withCaching_run_some _ hanswer, tsum_probOutput_pure_mul]
        simp only [queryException, hfresh, false_and, decide_false, Bool.or_false]
        exact le_self_add

theorem expected_runExceptionMonitor_reserve_le (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool) :
    (∑' result, Pr[= result | runExceptionMonitor exception computation cache hit] *
      exceptionReservePotential potential ε result.1.2 result.2) ≤
      exceptionReservePotential potential ε cache hit +
        expectedQueryCharge (fun cache input => (charge cache input : ℝ≥0∞)) computation cache * ε := by
  rw [← expectedQueryCharge_mul]
  let cost := fun cache input => (charge cache input : ℝ≥0∞) * ε
  change _ ≤ _ + expectedQueryCharge cost computation cache
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp [runExceptionMonitor]
  | query_bind query next ih =>
      rw [runExceptionMonitor, OracleComp.construct_query_bind, tsum_probOutput_bind_mul,
        expectedQueryCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (romImpl query).run cache] *
            (exceptionReservePotential potential ε result.2 (hit || queryException exception cache query result.1) +
              expectedQueryCharge cost (next result.1) result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : result ∈ support ((romImpl query).run cache)
          · exact mul_le_mul' le_rfl (ih result.1 result.2 (finite_of_mem_support_romImpl hfinite hr) _)
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | (romImpl query).run cache] *
            exceptionReservePotential potential ε result.2 (hit || queryException exception cache query result.1)) +
            ∑' result, Pr[= result | (romImpl query).run cache] *
              expectedQueryCharge cost (next result.1) result.2 := by
          simp_rw [mul_add, ENNReal.tsum_add]
        _ ≤ (exceptionReservePotential potential ε cache hit + hashQueryCharge cost cache query) +
            ∑' result, Pr[= result | (romImpl query).run cache] *
              expectedQueryCharge cost (next result.1) result.2 :=
          add_le_add (expected_exceptionReserve_query_le exception potential charge ε hstep hamortized query cache hfinite hit) le_rfl
        _ = _ := by rw [add_assoc]

theorem probEvent_runExceptionMonitor_le_amortized_queryCharge (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    Pr[fun result => result.2 = true | runExceptionMonitor exception computation cache false] ≤
      (potential cache : ℝ≥0∞) * ε +
        expectedQueryCharge (fun cache input => (charge cache input : ℝ≥0∞)) computation cache * ε := by
  have hbound := expected_runExceptionMonitor_reserve_le exception potential charge ε hstep hamortized
    computation cache hfinite false
  simp only [exceptionReservePotential, Bool.false_eq_true, ↓reduceIte, zero_add] at hbound
  apply le_trans _ hbound
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hh : result.2 = true
  · simp only [hh, if_true]
    exact le_mul_of_one_le_right' (le_self_add)
  · simp [hh]

end SphincsSecurity
