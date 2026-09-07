import SphincsSecurity.Proof.SigningMacroBudget
import SphincsSecurity.Proof.SigningRetryBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ConsumesHashQueries

theorem consumesHashQueries_sign_28504 (key : SecretKey) (message : Message) :
    ConsumesHashQueries (sign key message) 28504 := by
  rw [sign_eq]
  apply ConsumesHashQueries.mono (a := min digestAttemptLimit 28504) ?_ (by decide)
  apply consumesHashQueries_signDigestLoop_bind
  rintro ⟨randomness, index, leaves⟩
  apply consumesHashQueries_bind _ _ 28504 0
  · exact ConsumesHashQueries.mono (consumesHashQueries_ftsOpen _ _ _ _) (by decide)
  · intro path
    exact consumesHashQueries_zero _

/-- Debit from the syntactic continuation bound, including repeatable digest rejection. -/
def signingExecutionHashCost : (OracleWorld + SigningSpec).Domain → Nat
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => digestAttemptLimit

def unusedSigningExecutionCost : (OracleWorld + SigningSpec).Domain → Nat
  | .inl _ => 0
  | .inr _ => digestAttemptLimit - 1024

theorem signingMacroHashCost_add_unused_execution (input : (OracleWorld + SigningSpec).Domain) :
    signingMacroHashCost input + unusedSigningExecutionCost input = signingExecutionHashCost input := by
  cases input with
  | inl world => cases world <;> rfl
  | inr message =>
      norm_num [signingMacroHashCost, unusedSigningExecutionCost, signingExecutionHashCost, digestAttemptLimit]

theorem expanded_query_bound_signing_execution {α : Type} (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl key) (OracleSpec.query input >>= next)).IsQueryBoundP (· matches Sum.inr _) q)
    (state : CoverLogState)
    (result : (OracleWorld + SigningSpec).Range input × CoverLogState)
    (hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)) :
    signingExecutionHashCost input ≤ q ∧
      (simulateQ (expandedAdversaryImpl key) (next result.1)).IsQueryBoundP (· matches Sum.inr _)
        (q - signingExecutionHashCost input) := by
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
      have hcost := consumesHashQueries_sign_retryLimit key message
      unfold ConsumesHashQueries at hcost
      exact hcost _ q hbound base.1 houtput

end SphincsSecurity.Concrete
