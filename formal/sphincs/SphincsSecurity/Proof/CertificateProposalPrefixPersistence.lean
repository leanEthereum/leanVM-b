import SphincsSecurity.Proof.CertificateProposalPrefixException
import SphincsSecurity.Proof.CertificateStoppedState

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable

theorem certificateMonitorUpdate_prefixStop (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : CertificateMonitorActive key budget input state)
    (hstop : proposalPrefixStop input state length record = true) :
    let after := certificateMonitorUpdate key budget required
      (fun input state length record => proposalPrefixStop input state length record || stopAfter input state length record)
      input state length record
    after.stopped = true ∧ ProposalPrefixExceptional after.proposals after.log.length := by
  dsimp only
  constructor
  · simp only [certificateMonitorUpdate, if_pos hactive, hstop, Bool.true_or]
  · rw [proposalPrefixStop_eq_after_exception key budget required
        (fun input state length record => proposalPrefixStop input state length record || stopAfter input state length record)
        input state length record hactive, decide_eq_true_eq] at hstop
    exact hstop

theorem certificateLength_run_prefixOverflow {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState)
    (hstop : state.2.stopped = true)
    (hbad : ProposalPrefixExceptional state.2.proposals state.2.log.length)
    (result : α × CertificateMonitorState)
    (hr : result ∈ ((simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state).support) :
    result.2.2.stopped = true ∧ ProposalPrefixExceptional result.2.2.proposals result.2.2.log.length := by
  rw [certificateLength_run_stopped key budget required stopAfter computation state hstop result hr]
  exact ⟨hstop, hbad⟩

theorem certificateProposal_run_prefixOverflow {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : List Index × CertificateMonitorState)
    (hstop : state.2.2.stopped = true)
    (hbad : ProposalPrefixExceptional state.2.2.proposals state.2.2.log.length)
    (result : α × (List Index × CertificateMonitorState))
    (hr : result ∈ ((simulateQ (certificateProposalImpl key budget required stopAfter) computation).run state).support) :
    result.2.2.2.stopped = true ∧ ProposalPrefixExceptional result.2.2.2.proposals result.2.2.2.log.length := by
  rw [certificateProposal_run_stopped key budget required stopAfter computation state hstop result hr]
  exact ⟨hstop, hbad⟩

theorem certificateLength_run_after_prefixStop {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : CertificateMonitorActive key budget input state)
    (hstop : proposalPrefixStop input state length record = true)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (result : α × CertificateMonitorState)
    (hr : result ∈ ((simulateQ (certificateLengthImpl key budget required
      (fun input state length record => proposalPrefixStop input state length record || stopAfter input state length record))
      computation).run (originalProposalAdvance (certificateMonitorUpdate key budget required
        (fun input state length record => proposalPrefixStop input state length record || stopAfter input state length record))
        input state length record)).support) :
    ProposalPrefixExceptional result.2.2.proposals result.2.2.log.length := by
  have hafter := certificateMonitorUpdate_prefixStop key budget required stopAfter input state length record hactive hstop
  exact (certificateLength_run_prefixOverflow key budget required
    (fun input state length record => proposalPrefixStop input state length record || stopAfter input state length record)
    computation (originalProposalAdvance (certificateMonitorUpdate key budget required
      (fun input state length record => proposalPrefixStop input state length record || stopAfter input state length record))
      input state length record) hafter.1 hafter.2 result hr).2

end SphincsSecurity.Concrete
