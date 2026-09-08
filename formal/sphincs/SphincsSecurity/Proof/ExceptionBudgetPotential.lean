import SphincsSecurity.Proof.AmortizedExceptions
import SphincsSecurity.Proof.RomQueryCharge

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem probEvent_runExceptionMonitor_hit_le_budgetPotential
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : Nat → QueryCache HashSpec → Bool → ENNReal)
    (hterminal : ∀ q cache, Finite cache → 1 ≤ potential q cache true)
    (hstep : ∀ q cache, Finite cache → ∀ input hit,
      (∑' result, Pr[= result | (romImpl (.inr input)).run cache] *
        potential q result.2 (hit || queryException exception cache (.inr input) result.1)) ≤
      potential (q + 1) cache hit)
    (computation : OracleComp OracleWorld α) :
    ∀ q, computation.IsQueryBoundP (· matches Sum.inr _) q →
      ∀ cache, Finite cache → ∀ hit,
        Pr[fun result => result.2 = true | runExceptionMonitor exception computation cache hit] ≤
          potential q cache hit := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro q _ cache hfinite hit
      cases hit
      · simp [runExceptionMonitor]
      · simpa [runExceptionMonitor] using hterminal q cache hfinite
  | query_bind query next ih =>
      intro q hq cache hfinite hit
      rw [isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hcont⟩ := hq
      rw [runExceptionMonitor, OracleComp.construct_query_bind]
      change Pr[fun result => result.2 = true |
        (romImpl query).run cache >>= fun result =>
          runExceptionMonitor exception (next result.1) result.2
            (hit || queryException exception cache query result.1)] ≤ _
      cases query with
      | inl sample =>
          simp only [Bool.false_eq_true, if_false] at hcont
          have hrun : ((romImpl (.inl sample)).run cache >>= fun result =>
              runExceptionMonitor exception (next result.1) result.2
                (hit || queryException exception cache (.inl sample) result.1)) =
              (liftM (unifSpec.query sample) : ProbComp _) >>= fun answer =>
                runExceptionMonitor exception (next answer) cache hit := by
            simp [romImpl, unifFwdImpl, QueryImpl.liftTarget, HasQuery.toQueryImpl,
              StateT.run_monadLift, map_eq_bind_pure_comp, bind_assoc, queryException]
          rw [hrun]
          exact probEvent_bind_le_of_forall_le fun answer _ =>
            ih answer q (hcont answer) cache hfinite hit
      | inr input =>
          simp only [if_true] at hcont
          have hpositive : 0 < q := by simpa using hcan
          obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
          simp only [Nat.add_sub_cancel] at hcont
          rw [probEvent_bind_eq_tsum]
          apply le_trans _ (hstep q' cache hfinite input hit)
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : result ∈ support ((romImpl (.inr input)).run cache)
          · exact mul_le_mul' le_rfl (ih result.1 q' (hcont result.1) result.2
              (finite_of_mem_support_romImpl hfinite hr) _)
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

noncomputable def cacheEntryException (Bad : QueryCache HashSpec → Prop)
    (cache : QueryCache HashSpec) (input : HashInput) (answer : HashOutput) : Prop :=
  Bad (cache.cacheQuery input answer)

theorem probEvent_cacheEntryException_le_budgetPotential
    (Bad : QueryCache HashSpec → Prop) (potential : Nat → QueryCache HashSpec → ENNReal)
    (hbad : ∀ q cache, Finite cache → Bad cache → 1 ≤ potential q cache)
    (hmono : ∀ q cache, Finite cache → potential q cache ≤ potential (q + 1) cache)
    (hfresh : ∀ q cache, Finite cache → ∀ input, cache input = none →
      (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        potential q (cache.cacheQuery input answer)) ≤ potential (q + 1) cache)
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hq : computation.IsQueryBoundP (· matches Sum.inr _) q)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    Pr[fun result => result.2 = true |
      runExceptionMonitor (cacheEntryException Bad) computation cache false] ≤ potential q cache := by
  classical
  apply probEvent_runExceptionMonitor_hit_le_budgetPotential (cacheEntryException Bad)
    (fun q cache hit => if hit then 1 else potential q cache) (by simp) ?_ computation q hq cache hfinite false
  intro remaining current hcurrent input hit
  cases hit with
  | true => simp only [Bool.true_or, if_true, mul_one, romImpl_query_mass, le_refl]
  | false =>
      simp only [Bool.false_or, Bool.false_eq_true, if_false]
      change (∑' result, Pr[= result | (randomOracle input).run current] *
        (if queryException (cacheEntryException Bad) current (.inr input) result.1 then 1
          else potential remaining result.2)) ≤ _
      by_cases hnew : current input = none
      · rw [randomOracle, QueryImpl.withCaching_run_none _ hnew, tsum_probOutput_map_mul]
        apply le_trans _ (hfresh remaining current hcurrent input hnew)
        apply ENNReal.tsum_le_tsum
        intro answer
        apply mul_le_mul' le_rfl
        simp only [queryException, hnew, true_and, cacheEntryException, decide_eq_true_eq]
        split_ifs with hbadCache
        · exact hbad remaining _ (finite_cacheQuery hcurrent input answer) hbadCache
        · exact le_rfl
      · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hnew
        rw [randomOracle, QueryImpl.withCaching_run_some _ hanswer, tsum_probOutput_pure_mul]
        simpa [queryException, hnew] using hmono remaining current hcurrent

end SphincsSecurity
