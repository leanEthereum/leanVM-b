import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeHistoryPrefix

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

theorem expected_completeHistoryResolvedPrefix_view_cost
    (entry : HistoryResolvedPrefix α) (cost : DeferredContext → α → ℝ≥0∞) :
    (∑' result, Pr[= result | completeHistoryResolvedPrefix (some entry)] *
      match result with
      | none => 0
      | some result => cost result.context result.value) =
    cost entry.context entry.value *
      Pr[fun base => ¬ChainStartHistoryHit entry.context entry.history base | sampleOtsHashTable] := by
  rw [completeHistoryResolvedPrefix, completeResolvedHistory, tsum_probOutput_bind_mul]
  conv_rhs => rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro base
  by_cases hhit : ChainStartHistoryHit entry.context entry.history base <;>
    simp [hhit, mul_comm]

theorem expected_completeHistoryResolvedPrefix_function
    (entry : HistoryResolvedPrefix α) (cost : (OtsSecretIndex → HashOutput) → DeferredContext → α → ℝ≥0∞) :
    (∑' result, Pr[= result | completeHistoryResolvedPrefix (some entry)] *
      match result with
      | none => 0
      | some result => cost result.table result.context result.value) =
    ∑' base, Pr[= base | sampleOtsHashTable] *
      if ChainStartHistoryHit entry.context entry.history base then 0
      else cost (completedStartTable entry.context.state base) entry.context entry.value := by
  rw [completeHistoryResolvedPrefix, completeResolvedHistory, tsum_probOutput_bind_mul]
  apply tsum_congr
  intro base
  by_cases hhit : ChainStartHistoryHit entry.context entry.history base <;> simp [hhit]

noncomputable def unresolvedStartCandidateAllowance
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) : Option Probe → ℝ≥0∞
  | some candidate@⟨.chainStart _ _ _ _, _⟩ =>
      if context.state.values candidate.coordinate = none then candidateFailureAllowance table context (some candidate) else 0
  | _ => 0

noncomputable def unresolvedStartCandidateCharge (context : DeferredContext) : Option Probe → ℝ≥0∞
  | some candidate@⟨.chainStart _ _ _ _, _⟩ =>
      if context.state.values candidate.coordinate = none then
        (unmaterializedCandidateCharge (materializedDeferredState context) (some candidate) : ℝ≥0∞)
      else 0
  | _ => 0

noncomputable def historyUnresolvedStartAllowance (candidate : DeferredContext → α → Option Probe) :
    Option (ResolvedRunResult α) → ℝ≥0∞
  | none => 0
  | some result => unresolvedStartCandidateAllowance result.table result.context (candidate result.context result.value)

noncomputable def historyUnresolvedStartCharge (candidate : DeferredContext → α → Option Probe) :
    Option (ResolvedRunResult α) → ℝ≥0∞
  | none => 0
  | some result => unresolvedStartCandidateCharge result.context (candidate result.context result.value)

theorem expected_completeHistoryResolvedPrefix_unresolvedStart_le
    (entry : HistoryResolvedPrefix α) (candidate : DeferredContext → α → Option Probe)
    (hlength : entry.history.length ≤ 2 ^ 126) :
    (∑' result, Pr[= result | completeHistoryResolvedPrefix (some entry)] * historyUnresolvedStartAllowance candidate result) ≤
      (∑' result, Pr[= result | completeHistoryResolvedPrefix (some entry)] * historyUnresolvedStartCharge candidate result) *
        ((4 / 3 : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by
  unfold historyUnresolvedStartAllowance historyUnresolvedStartCharge
  rw [expected_completeHistoryResolvedPrefix_function entry (fun table context value =>
        unresolvedStartCandidateAllowance table context (candidate context value)),
      expected_completeHistoryResolvedPrefix_view_cost entry (fun context value =>
        unresolvedStartCandidateCharge context (candidate context value))]
  cases hcandidate : candidate entry.context entry.value with
  | none => simp [unresolvedStartCandidateAllowance, unresolvedStartCandidateCharge]
  | some probe =>
      rcases probe with ⟨coordinate, digest⟩
      cases coordinate with
      | position position => simp [unresolvedStartCandidateAllowance, unresolvedStartCandidateCharge]
      | chainStart lay tree leafIdx chainIdx =>
          by_cases hmissing : entry.context.state.values (.chainStart lay tree leafIdx chainIdx) = none
          · simp only [unresolvedStartCandidateAllowance, unresolvedStartCandidateCharge, if_pos hmissing]
            have hlocal := expected_history_guarded_chainStart_allowance_le_four_thirds entry.context entry.history hlength
              ⟨lay, tree, leafIdx, chainIdx⟩ digest hmissing
            simpa only [OtsSecretIndex.coordinate, ite_not, mul_assoc, mul_comm, mul_left_comm] using hlocal
          · simp [unresolvedStartCandidateAllowance, unresolvedStartCandidateCharge, hmissing]

theorem evalDist_history_filtered_runResolved_eq_prefix_observe
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe)
    (observe : Option (ResolvedRunResult α) → ProbComp β)
    (hobserve : ∀ result, result.context.ValuesConsistent → StartTableAgrees result.context.state result.table →
      ¬DeferredCompletable result.table result.context → evalDist (observe (some result)) = evalDist (observe none))
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hbudget : history.length + bound ≤ 2 ^ 126) :
    evalDist ((do
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit context history base then pure none
      else runResolvedFromTable context fuel (completedStartTable context.state base) computation) >>= observe) =
    evalDist ((runResolvedHistoryPrefix computation context fuel history >>= completeHistoryResolvedPrefix) >>= observe) := by
  rw [← runResolvedHistoryAdaptive_eq_prefix_complete]
  have hspace : 2 ^ 126 < Fintype.card Digest := by norm_num [digestBits]
  exact evalDist_history_filtered_runResolved_eq_adaptive_observe computation context fuel bound history observe
    hobserve hconsistent hcovered (((Nat.add_le_add_right hcovered.card_le bound).trans hbudget).trans_lt hspace) hbound

end SphincsSecurity.Concrete.OtsProbeSimulation
