import SphincsSecurity.Proof.BoundaryBudgetPotential
import SphincsSecurity.Proof.OriginalProposalBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem boundaryRun_cache_finite {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (result : (α × SigningBoundaryTrace) × QueryCache HashSpec)
    (hr : result ∈ support (boundaryRun parameter computation cache)) : Finite result.2 := by
  apply finite_cache_of_mem_support computation cache result.1.1 result.2 _ hfinite
  rw [← boundaryRun_forget parameter computation cache, support_map]
  exact ⟨result, hr, rfl⟩

theorem originalProposalRecord_cache_finite (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (record : ProposalExecutionRecord input)
    (hr : record ∈ (originalProposalRecord key input cache).support) : Finite record.cache :=
  boundaryRun_cache_finite key.parameter (expandedAdversaryImpl key input) cache hfinite _
    (originalProposalRecord_boundary_support key input cache record hr)

theorem expected_originalProposalRecord_budgetPotential_le
    (potential : Nat → QueryCache HashSpec → ENNReal)
    (hmono : ∀ q cache, Finite cache → potential q cache ≤ potential (q + 1) cache)
    (hfresh : ∀ q cache, Finite cache → ∀ input, cache input = none →
      (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        potential q (cache.cacheQuery input answer)) ≤ potential (q + 1) cache)
    (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (q : Nat) (hbound : (expandedAdversaryImpl key input).IsQueryBoundP (· matches .inr _) q)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑' record, Pr[= record | originalProposalRecord key input cache] *
      potential (q - record.trace.hashCalls) record.cache) ≤ potential q cache := by
  have hmap := congrArg (fun law : PMF (((OracleWorld + SigningSpec).Range input × SigningBoundaryTrace) ×
      QueryCache HashSpec) => ∑' result, Pr[= result | law] * potential (q - result.1.2.hashCalls) result.2)
    (originalProposalRecord_boundary key input cache)
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at hmap
  exact hmap.trans_le (expected_boundaryRun_budgetPotential_le potential hmono hfresh key.parameter
    (expandedAdversaryImpl key input) q hbound cache hfinite)

end SphincsSecurity.Concrete
