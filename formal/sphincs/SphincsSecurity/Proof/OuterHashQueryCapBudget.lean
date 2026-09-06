import SphincsSecurity.Proof.OuterHashQueryCap
import SphincsSecurity.Proof.OtsProbeNativeLiveBudget

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem capOuterHashQueries_query_bind_of_budget
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbudget : outerHashQueryCount input ≤ q) :
    capOuterHashQueries ((liftM (OracleSpec.query input) : OracleComp (OracleWorld + SigningSpec) _) >>= next) q =
      ((liftM (OracleSpec.query input) : OracleComp (OracleWorld + SigningSpec) _) >>= fun reply =>
        capOuterHashQueries (next reply) (q - outerHashQueryCount input)) := by
  rw [capOuterHashQueries_query_bind]
  cases input with
  | inl input =>
      cases input with
      | inl n => simp [IsOuterHash, outerHashQueryCount]
      | inr input =>
          cases q with
          | zero => simp [outerHashQueryCount] at hbudget
          | succ remaining => simp [IsOuterHash, outerHashQueryCount]
  | inr message => simp [IsOuterHash, outerHashQueryCount]

theorem simulateQ_expanded_capOuterHashQueries
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl secretKey) computation).IsQueryBoundP (· matches Sum.inr _) q) :
    simulateQ (expandedAdversaryImpl secretKey) (capOuterHashQueries computation q) =
      some <$> simulateQ (expandedAdversaryImpl secretKey) computation := by
  induction computation using OracleComp.inductionOn generalizing q with
  | pure value => simp [capOuterHashQueries, outerHashQueryCutAt, OuterQueryCut.value?]
  | query_bind input next ih =>
      have hbudget := expandedQuery_hashBudget secretKey input next q hbound
      rw [capOuterHashQueries_query_bind_of_budget input next q hbudget.1,
        simulateQ_bind, simulateQ_spec_query, simulateQ_bind, simulateQ_spec_query, map_bind]
      apply bind_congr_of_forall_mem_support
      intro reply hreply
      exact ih reply (q - outerHashQueryCount input) (hbudget.2 reply hreply)

theorem simulateQ_expandedRetained_capOuterHashQueries
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (root : Digest) :
    simulateQ (expandedAdversaryImpl
      (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
      (capOuterHashQueries (retainedGameRestComputation adversary ⟨root, parameter⟩) q) =
      some <$> simulateQ (expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩) :=
  simulateQ_expanded_capOuterHashQueries _ _ q
    (isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hparameter table ftsSecret hfts root)

end SphincsSecurity.Concrete.OtsProbeSimulation
