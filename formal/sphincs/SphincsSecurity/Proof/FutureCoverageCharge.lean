import SphincsSecurity.Proof.CacheMessageWeight

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def newMessageFutureCoverage {n : Nat} (remaining : Nat) (parameter : PublicParameter)
    (views : HashInput → Fin n → Option FewTimeView) (before after : QueryCache HashSpec) : ENNReal :=
  cacheMessageWeight parameter (fun input target => if before input = none then
    futureFewTimeCoverage remaining (uncoveredFewTimeTrees (views input) target) target else 0) after

noncomputable def freshFutureCoverageCharge {n : Nat} (remaining : Nat) (parameter : PublicParameter)
    (views : HashInput → Fin n → Option FewTimeView) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if cache input = none ∧ MessageHashInput parameter input then
    coverageOccupancyCompletion (views input) remaining * ((2 ^ 176 : Nat) : ENNReal)⁻¹ else 0

theorem newMessageFutureCoverage_self {n : Nat} (remaining : Nat) (parameter : PublicParameter)
    (views : HashInput → Fin n → Option FewTimeView) (cache : QueryCache HashSpec) :
    newMessageFutureCoverage remaining parameter views cache cache = 0 :=
  cacheMessageWeight_fresh_restriction _ _ _

theorem expected_newMessageFutureCoverage_cacheQuery_le {n : Nat} (remaining : Nat) (parameter : PublicParameter)
    (views : HashInput → Fin n → Option FewTimeView) (before cache : QueryCache HashSpec)
    (input : HashInput) (hfresh : cache input = none) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      newMessageFutureCoverage remaining parameter views before (cache.cacheQuery input output)) ≤
      newMessageFutureCoverage remaining parameter views before cache + freshFutureCoverageCharge remaining parameter views cache input := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 :=
    tsum_probOutput_eq_one' (by simp)
  simp_rw [newMessageFutureCoverage, cacheMessageWeight_cacheQuery parameter _ cache input _ hfresh, mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
  apply add_le_add le_rfl
  by_cases hmessage : MessageHashInput parameter input
  · simp only [hmessage, true_and, freshFutureCoverageCharge, hfresh, and_self, if_true]
    by_cases hbefore : before input = none
    · simp only [hbefore, if_true]
      exact expected_uniformHashOutput_futureCoverage_le (views input) remaining
    · simp only [hbefore, if_false, ite_self, mul_zero, tsum_zero, zero_le]
  · simp only [hmessage, false_and, if_false, mul_zero, tsum_zero, freshFutureCoverageCharge,
      and_false, le_refl]

theorem expected_newMessageFutureCoverage_le {α : Type} {n : Nat} (remaining : Nat) (parameter : PublicParameter)
    (views : HashInput → Fin n → Option FewTimeView) (computation : OracleComp OracleWorld α)
    (before : QueryCache HashSpec) (hfinite : Finite before) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run before] *
      newMessageFutureCoverage remaining parameter views before result.2) ≤
      expectedQueryCharge (freshFutureCoverageCharge remaining parameter views) computation before := by
  have hstep (query : OracleWorld.Domain) (cache : QueryCache HashSpec) (hcache : Finite cache) :=
    expected_potential_romImpl_le_charge (newMessageFutureCoverage remaining parameter views before)
      (freshFutureCoverageCharge remaining parameter views)
      (fun cache _ input hfresh => expected_newMessageFutureCoverage_cacheQuery_le remaining parameter views before cache input hfresh)
      query cache hcache
  have hbound := expected_potential_simulateQ_le_queryCharge (newMessageFutureCoverage remaining parameter views before)
    (freshFutureCoverageCharge remaining parameter views) hstep computation before hfinite
  simpa only [newMessageFutureCoverage_self, zero_add] using hbound

end SphincsSecurity.Concrete
