import SphincsSecurity.Proof.HashQueryCut
import SphincsSecurity.Proof.PreExceptionQueryCharge

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expectedQueryCharge_lift_eq_zero_of_supported_cuts
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp HashSpec α) (cache : QueryCache HashSpec)
    (hzero : ∀ (ordinal : Nat) (middleCache : QueryCache HashSpec) (input : HashInput)
      (next : HashOutput → OracleComp HashSpec α),
      (.query input next, middleCache) ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _) (hashQueryCutAt computation ordinal)).run cache) →
      charge middleCache input = 0) :
    expectedQueryCharge charge (liftM computation : OracleComp OracleWorld α) cache = 0 := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input next ih =>
      have hhead : charge cache input = 0 := hzero 0 cache input next (by
        simp only [hashQueryCutAt, construct_query_bind, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff])
      rw [liftM_bind]
      change expectedQueryCharge charge ((liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld HashOutput) >>=
        fun output => liftM (next output)) cache = 0
      rw [expectedQueryCharge_query_bind]
      simp only [hashQueryCharge, Sum.elim_inr, hhead, zero_add]
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hr : result ∈ support ((romImpl (.inr input)).run cache)
      · rw [ih result.1 result.2 ?_, mul_zero]
        intro ordinal middleCache queried continuation hcut
        apply hzero (ordinal + 1) middleCache queried continuation
        simp only [hashQueryCutAt, construct_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          mem_support_bind_iff]
        exact ⟨result, hr, hcut⟩
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

theorem expectedPreExceptionCharge_lift_eq_zero_of_supported_cuts
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp HashSpec α) (cache : QueryCache HashSpec) (hit : Bool)
    (hzero : ∀ (ordinal : Nat) (middleCache : QueryCache HashSpec) (input : HashInput)
      (next : HashOutput → OracleComp HashSpec α),
      (.query input next, middleCache) ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _) (hashQueryCutAt computation ordinal)).run cache) →
      charge middleCache input = 0) :
    expectedPreExceptionCharge exception charge (liftM computation : OracleComp OracleWorld α) cache hit = 0 := by
  apply le_antisymm _ bot_le
  exact (expectedPreExceptionCharge_le_queryCharge exception charge _ cache hit).trans_eq
    (expectedQueryCharge_lift_eq_zero_of_supported_cuts charge computation cache hzero)

end SphincsSecurity
