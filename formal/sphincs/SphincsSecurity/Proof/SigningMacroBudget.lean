import SphincsSecurity.Proof.SigningQueryCost
import SphincsSecurity.Proof.WorldCoverBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec

def signingMacroHashCost : (OracleWorld + SigningSpec).Domain → Nat
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 1024

theorem expanded_query_bound_signing_macro {α : Type} (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl key) (OracleSpec.query input >>= next)).IsQueryBoundP (· matches Sum.inr _) q)
    (state : CoverLogState)
    (result : (OracleWorld + SigningSpec).Range input × CoverLogState)
    (hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)) :
    signingMacroHashCost input ≤ q ∧
      (simulateQ (expandedAdversaryImpl key) (next result.1)).IsQueryBoundP (· matches Sum.inr _)
        (q - signingMacroHashCost input) := by
  cases input with
  | inl world =>
      obtain ⟨hcost, htail⟩ := expanded_query_bound_log_step key (.inl world) next q hbound state
      cases world with
      | inl uniform => exact ⟨hcost, htail result hresult⟩
      | inr input => exact ⟨hcost, htail result hresult⟩
  | inr message =>
      rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
      obtain ⟨base, hbase, rfl⟩ := hresult
      have houtput := unloggedMappedAdversaryImpl_output_mem_support_expanded key (.inr message) state.1 base.2 base.1 hbase
      rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
      exact consumesHashQueries_sign key message _ q hbound base.1 houtput

end SphincsSecurity.Concrete
