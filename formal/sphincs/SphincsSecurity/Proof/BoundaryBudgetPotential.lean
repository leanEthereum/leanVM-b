import SphincsSecurity.Proof.BoundaryHashCost
import SphincsSecurity.Proof.ExceptionBudgetPotential

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expected_romHash_budgetPotential_le (potential : Nat → QueryCache HashSpec → ENNReal)
    (hmono : ∀ q cache, Finite cache → potential q cache ≤ potential (q + 1) cache)
    (hfresh : ∀ q cache, Finite cache → ∀ input, cache input = none →
      (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        potential q (cache.cacheQuery input answer)) ≤ potential (q + 1) cache)
    (q : Nat) (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) :
    (∑' result, Pr[= result | (romImpl (.inr input)).run cache] * potential q result.2) ≤
      potential (q + 1) cache := by
  change (∑' result, Pr[= result | (randomOracle input).run cache] * potential q result.2) ≤ _
  by_cases hnew : cache input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hnew, tsum_probOutput_map_mul]
    exact hfresh q cache hfinite input hnew
  · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hnew
    rw [randomOracle, QueryImpl.withCaching_run_some _ hanswer, tsum_probOutput_pure_mul]
    exact hmono q cache hfinite

theorem expected_boundaryRun_budgetPotential_le {α : Type}
    (potential : Nat → QueryCache HashSpec → ENNReal)
    (hmono : ∀ q cache, Finite cache → potential q cache ≤ potential (q + 1) cache)
    (hfresh : ∀ q cache, Finite cache → ∀ input, cache input = none →
      (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        potential q (cache.cacheQuery input answer)) ≤ potential (q + 1) cache)
    (parameter : PublicParameter) (computation : OracleComp OracleWorld α)
    (q : Nat) (hbound : computation.IsQueryBoundP (· matches .inr _) q)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑' result, Pr[= result | boundaryRun parameter computation cache] *
      potential (q - result.1.2.hashCalls) result.2) ≤ potential q cache := by
  induction computation using OracleComp.inductionOn generalizing q cache with
  | pure value =>
      simp only [boundaryRun, simulateQ_pure, WriterT.run_pure, StateT.run_pure,
        tsum_probOutput_pure_mul, SigningBoundaryTrace.hashCalls, FreeMonoid.toList_one,
        List.length_nil, Nat.sub_zero, le_refl]
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [boundaryRun_bind, boundaryRun_query, tsum_probOutput_bind_mul, tsum_probOutput_map_mul]
      simp only [tsum_probOutput_map_mul, SigningBoundaryTrace.hashCalls_mul,
        signingBoundaryTrace_hashCalls_eq, ← Nat.sub_sub]
      calc
        _ ≤ ∑' result, Pr[= result | (romImpl input).run cache] *
            potential (q - if input matches .inr _ then 1 else 0) result.2 := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : result ∈ support ((romImpl input).run cache)
          · apply mul_le_mul' le_rfl
            have htail := ih result.1 _ (hbound.2 result.1) result.2
              (finite_of_mem_support_romImpl hfinite hr)
            cases input <;>
              simpa only [Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] using htail
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        _ ≤ _ := by
          cases input with
          | inl sample =>
              simp only [Bool.false_eq_true, if_false, Nat.sub_zero]
              have hrun : (romImpl (.inl sample)).run cache =
                  (fun answer => (answer, cache)) <$> (liftM (unifSpec.query sample) : ProbComp _) := by
                simp [romImpl, unifFwdImpl, QueryImpl.liftTarget, HasQuery.toQueryImpl,
                  StateT.run_monadLift]
              rw [hrun, tsum_probOutput_map_mul]
              change (∑' answer, Pr[= answer | (liftM (unifSpec.query sample) : ProbComp _)] *
                potential q cache) ≤ potential q cache
              rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
          | inr input =>
              have hpositive : 0 < q := hbound.1.resolve_left (by simp)
              obtain ⟨remaining, rfl⟩ : ∃ remaining, q = remaining + 1 := ⟨q - 1, by omega⟩
              simpa only [if_true, Nat.add_sub_cancel] using
                expected_romHash_budgetPotential_le potential hmono hfresh remaining cache hfinite input

end SphincsSecurity.Concrete
