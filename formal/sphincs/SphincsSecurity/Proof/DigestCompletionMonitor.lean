import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.CertificateMonitor
import SphincsSecurity.Proof.DigestCompletionBank

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop
attribute [local irreducible] bankedProposalRecordValue bankedTargetEnvelope completedTargetBank targetCreationPrice targetCreationMultiplier

theorem expected_digestCompletion_bankedProposalRecord_le {α : Type}
    (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat) (required : Finset FtsTree)
    (state : CoverLogState) (bank : HashInput → Bool) (message : Message)
    (finish : DigestLoopRecord → ProbComp α) (record : α → ProposalExecutionRecord (.inr message))
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run state.1),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop
        (((record result).output, (record result).selectedView), (record result).cache))
    (stopped : α → Bool) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run state.1 >>= finish] *
      bankedProposalRecordValue key reuse budget signatures required state bank (.inr message) (record result) (stopped result)) ≤
      bankedTargetEnvelope key reuse budget (signatures + 1) required state bank false +
        targetCreationMultiplier key state.1 (.inr message) * targetCreationPrice key reuse budget (signatures + 1) required state := by
  have hstep := expected_digestCompletion_bankedTarget_le key reuse budget signatures required state bank message finish
    (fun result => (((record result).output, (record result).selectedView), (record result).cache)) hcompletion stopped hsigned hreuse
  dsimp only at hstep
  conv at hstep =>
    rhs
    arg 2
    rw [← targetCreationMultiplier_sign_mul_price key reuse budget signatures required state message]
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run state.1 >>= finish] *
        bankedTargetEnvelope key reuse budget signatures required
          ((record result).cache, state.2 ++ [⟨message, (record result).output⟩])
          (completedTargetBank key required ((record result).cache, state.2 ++ [⟨message, (record result).output⟩]) bank) (stopped result) := by
      apply ENNReal.tsum_le_tsum
      intro result
      apply mul_le_mul' le_rfl
      unfold bankedProposalRecordValue proposalRecordLogState signingLogFragment
      exact bankedTargetEnvelope_budget_mono key reuse signatures required
        ((record result).cache, state.2 ++ [⟨message, (record result).output⟩])
        (completedTargetBank key required ((record result).cache, state.2 ++ [⟨message, (record result).output⟩]) bank)
        (stopped result) (Nat.sub_le budget (record result).trace.hashCalls)
    _ ≤ bankedTargetEnvelope key reuse budget (signatures + 1) required state bank false +
        targetCreationMultiplier key state.1 (.inr message) * targetCreationPrice key reuse budget signatures required state := hstep
    _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl
      (targetCreationPrice_signatures_mono key reuse budget required state (Nat.le_succ _)))

theorem expected_certificateMonitor_sign_le_digestCompletion {α : Type}
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (message : Message) (state : CertificateMonitorState)
    (finish : DigestLoopRecord → ProbComp α) (length : α → Nat) (record : α → ProposalExecutionRecord (.inr message))
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run state.1),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop
        (((record result).output, (record result).selectedView), (record result).cache)) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run state.1 >>= finish] *
      certificateMonitorPotential key budget required
        (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter)
          (.inr message) state (length result) (record result))) ≤
      certificateMonitorPotential key budget required state + certificateMonitorCharge key budget required (.inr message) state := by
  by_cases hactive : CertificateMonitorActive key budget (.inr message) state
  · have hdata := hactive
    obtain ⟨hlive, ⟨hsigned, hcache, _⟩, hvalid, _⟩ := hdata
    rw [certificateMonitorCharge, if_pos hactive]
    simp only [certificateMonitorPotential_advance_active key budget required stopAfter (.inr message) state _ _ hactive,
      signingLogFragment, List.length_append, List.length_singleton]
    have hremaining : signatureLimit - (state.2.log.length + 1) + 1 = signatureLimit - state.2.log.length := by
      change state.2.log.length < signatureLimit at hvalid
      omega
    have hreuse := exactDigestReuseWeight_le_near_uniform_of_clean_cache key state.1 state.2.spent
      hcache.spent_le hcache.cache_le hcache.no_deficit message
    have h := expected_digestCompletion_bankedProposalRecord_le key nearUniformDigestReuseWeight
      (budget - state.2.spent) (signatureLimit - (state.2.log.length + 1)) required (certificateMonitorCoverState state)
      state.2.bank message finish record hcompletion
      (fun result => (certificateMonitorUpdate key budget required stopAfter (.inr message) state (length result) (record result)).stopped)
      hsigned hreuse
    rw [hremaining] at h
    simpa only [certificateMonitorPotential, certificateMonitorCoverState, hlive] using h
  · rw [certificateMonitorCharge, if_neg hactive, add_zero]
    simp only [certificateMonitorPotential_advance_inactive key budget required stopAfter (.inr message) state _ _ hactive]
    rw [ENNReal.tsum_mul_right]
    apply (mul_le_of_le_one_left' tsum_probOutput_le_one).trans
    unfold certificateMonitorPotential bankedTargetEnvelope
    exact certificateBankCount_le_bankedCacheWeight _ _ _ _ _

end SphincsSecurity.Concrete
