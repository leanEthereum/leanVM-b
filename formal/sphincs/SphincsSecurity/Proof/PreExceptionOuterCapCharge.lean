import SphincsSecurity.Proof.PreExceptionOuterCharge
import SphincsSecurity.Proof.OuterHashQueryCapBudget

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expectedPreExceptionOuterCharge_map
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (secretKey : SecretKey) (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (f : α → β) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionOuterCharge exception secretKey charge (f <$> computation) cache hit =
      expectedPreExceptionOuterCharge exception secretKey charge computation cache hit := by
  rw [← bind_pure_comp, expectedPreExceptionOuterCharge_bind]
  simp only [expectedPreExceptionOuterCharge_pure, mul_zero, tsum_zero, add_zero]

theorem expectedPreExceptionOuterCharge_capOuterHashQueries
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (secretKey : SecretKey) (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl secretKey) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionOuterCharge exception secretKey charge (OtsProbeSimulation.capOuterHashQueries computation q) cache hit =
      expectedPreExceptionOuterCharge exception secretKey charge computation cache hit := by
  induction computation using OracleComp.inductionOn generalizing q cache hit with
  | pure value => rfl
  | query_bind input next ih =>
      have hbudget := OtsProbeSimulation.expandedQuery_hashBudget secretKey input next q hbound
      rw [OtsProbeSimulation.capOuterHashQueries_query_bind_of_budget input next q hbudget.1,
        expectedPreExceptionOuterCharge_query_bind, expectedPreExceptionOuterCharge_query_bind]
      congr 1
      apply tsum_congr
      intro result
      by_cases hr : result ∈ support (runExceptionMonitor exception (expandedAdversaryImpl secretKey input) cache hit)
      · have hm : result.1 ∈ support ((unloggedMappedAdversaryImpl secretKey input).run cache) := by
          rw [unloggedMappedAdversaryImpl_eq_simulateQ_expanded, ← runExceptionMonitor_project exception _ cache hit, support_map]
          exact ⟨result, hr, rfl⟩
        have hreply := unloggedMappedAdversaryImpl_output_mem_support_expanded secretKey input cache result.1.2 result.1.1 hm
        rw [ih result.1.1 (q - OtsProbeSimulation.outerHashQueryCount input) (hbudget.2 result.1.1 hreply) result.1.2 result.2]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

end SphincsSecurity.Concrete
