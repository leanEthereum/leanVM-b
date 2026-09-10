import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.CertificateProposalPrefixException
import SphincsSecurity.Proof.CertificateStoppedState

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable

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

end SphincsSecurity.Concrete
