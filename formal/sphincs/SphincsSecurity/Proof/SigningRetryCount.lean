import SphincsSecurity.Proof.SigningExecutionBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem signingLog_length_mul_retryLimit_le_queryBudget {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (state : CoverLogState) (result : α × CoverLogState)
    (hresult : result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state)) :
    result.2.2.length * digestAttemptLimit ≤ state.2.length * digestAttemptLimit + q := by
  induction computation using OracleComp.inductionOn generalizing q state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hresult
      subst result
      exact Nat.le_add_right _ _
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨step, hstep, hrest⟩ := hresult
      rw [simulateQ_spec_query] at hstep
      obtain ⟨hcost, htail⟩ := expanded_query_bound_signing_execution key input next q hbound state step hstep
      have hrec := ih step.1 (q - signingExecutionHashCost input) htail step.2 hrest
      rw [logTracedMappedAdversaryImpl_run_map, support_map] at hstep
      obtain ⟨base, hbase, rfl⟩ := hstep
      cases input with
      | inl world =>
          simpa only [signingLogFragment, List.append_nil] using hrec.trans
            (Nat.add_le_add_left (Nat.sub_le _ _) _)
      | inr message =>
          simp only [signingLogFragment, List.length_append, List.length_singleton,
            Nat.add_mul, Nat.one_mul, signingExecutionHashCost] at hrec hcost
          omega

theorem signingLog_length_le_queryBudget_div_retryLimit {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (cache : QueryCache HashSpec) (result : α × CoverLogState)
    (hresult : result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, []))) :
    result.2.2.length ≤ q / digestAttemptLimit := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < digestAttemptLimit)).mpr
  simpa only [List.length_nil, Nat.zero_mul, Nat.zero_add] using
    signingLog_length_mul_retryLimit_le_queryBudget key computation q hbound (cache, []) result hresult

end SphincsSecurity.Concrete
