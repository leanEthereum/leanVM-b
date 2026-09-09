import SphincsSecurity.Proof.ProposalPrefixConstants
import SphincsSecurity.Proof.CertificateGame

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def proposalPrefixPotential (proposals completed : Nat) : ENNReal :=
  proposalLengthTilt ^ proposals * proposalLengthMoment ^ (signatureLimit - completed)

theorem expected_certificateLengthImpl_prefixPotential (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
      proposalPrefixPotential result.2.2.proposals result.2.2.log.length) =
        proposalPrefixPotential state.2.proposals state.2.log.length := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · cases input with
    | inl world =>
        rw [certificateLengthImpl_world_run, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
        simp only [originalProposalAdvance, certificateMonitorUpdate, if_pos hactive,
          proposalRecordLogState, signingLogFragment, List.append_nil, Nat.add_zero]
        simp only [ENNReal.tsum_mul_right, PMF.probOutput_eq_apply, PMF.tsum_coe, one_mul]
    | inr message =>
        have hvalid : state.2.log.length < signatureLimit := hactive.2.2.1
        have hremaining : signatureLimit - (state.2.log.length + 1) + 1 =
            signatureLimit - state.2.log.length := by omega
        rw [certificateLengthImpl_sign_run, if_pos hactive, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
        simp only [originalProposalAdvance, certificateMonitorUpdate, if_pos hactive,
          proposalRecordLogState, signingLogFragment, List.length_append, List.length_singleton,
          proposalPrefixPotential, pow_add]
        calc
          _ = (proposalLengthTilt ^ state.2.proposals *
              proposalLengthMoment ^ (signatureLimit - (state.2.log.length + 1))) *
              ∑' result, Pr[= result | recordLengthBridge (originalProposalRecord key (.inr message) state.1)
                targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le] *
                  proposalLengthTilt ^ result.1 := by
            rw [← ENNReal.tsum_mul_left]
            apply tsum_congr
            intro result
            ring
          _ = _ := by
            rw [expected_recordLengthBridge_pow, mul_assoc, ← pow_succ, hremaining]
  · apply expected_certificateLengthImpl_of_advance_constant key budget required stopAfter input state
      (fun current => proposalPrefixPotential current.2.proposals current.2.log.length)
    intro length record
    simp only [originalProposalAdvance, certificateMonitorUpdate_inactive key budget required stopAfter input state length record hactive]

theorem expected_certificateLength_prefixPotential {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] *
      proposalPrefixPotential result.2.2.proposals result.2.2.log.length) =
        proposalPrefixPotential state.2.proposals state.2.log.length := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
      simp_rw [ih]
      exact expected_certificateLengthImpl_prefixPotential key budget required stopAfter input state

theorem expected_certificateProposal_prefixPotential {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : List Index × CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateProposalImpl key budget required stopAfter) computation).run state] *
      proposalPrefixPotential result.2.2.2.proposals result.2.2.2.log.length) =
        proposalPrefixPotential state.2.2.proposals state.2.2.log.length := by
  have h := congrArg (fun law : PMF (α × CertificateMonitorState) =>
    ∑' result, Pr[= result | law] * proposalPrefixPotential result.2.2.proposals result.2.2.log.length)
      (simulateQ_certificateProposalImpl_length key budget required stopAfter computation state)
  rw [tsum_probOutput_map_mul] at h
  exact h.trans (expected_certificateLength_prefixPotential key budget required stopAfter computation state.2)

theorem expected_certificateGame_prefixPotential (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    (∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] *
      proposalPrefixPotential result.2.2.2.proposals result.2.2.2.log.length) =
        proposalLengthMoment ^ signatureLimit := by
  rw [certificateGame, tsum_probOutput_bind_mul]
  simp_rw [expected_certificateProposal_prefixPotential]
  simp only [initialCertificateMonitor, proposalPrefixPotential, pow_zero, List.length_nil,
    Nat.sub_zero, one_mul, ENNReal.tsum_mul_right, PMF.probOutput_eq_apply, PMF.tsum_coe]

end SphincsSecurity.Concrete
