import SphincsSecurity.Proof.CertificateCacheExceptionGame
import SphincsSecurity.Proof.CertificateCachePersistence
import SphincsSecurity.Proof.CertificateProposalPrefixPersistence

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
set_option backward.isDefEq.respectTransparency false

def CertificateGameExceptional (result : CertificateCacheGameResult) : Prop :=
  result.2.2.2.2 = true ∨
    ProposalPrefixExceptional result.2.2.2.1.proposals result.2.2.2.1.log.length

theorem certificateCacheProposal_run_prefixOverflow {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : List Index × CertificateCacheMonitorState)
    (hstop : state.2.2.1.stopped = true)
    (hbad : ProposalPrefixExceptional state.2.2.1.proposals state.2.2.1.log.length)
    (result : α × (List Index × CertificateCacheMonitorState))
    (hr : result ∈ ((simulateQ (certificateCacheProposalImpl key budget required stopAfter) computation).run state).support) :
    ProposalPrefixExceptional result.2.2.2.1.proposals result.2.2.2.1.log.length := by
  have hm := (PMF.mem_support_map_iff (Prod.map id (Prod.map id certificateCacheMonitorProject)) _ _).mpr
    ⟨result, hr, rfl⟩
  rw [← PMF.monad_map_eq_map, simulateQ_certificateCacheProposalImpl_project] at hm
  exact (certificateProposal_run_prefixOverflow key budget required stopAfter computation
    (state.1, certificateCacheMonitorProject state.2) hstop hbad _ hm).2

theorem probEvent_certificateCacheGame_proposalPrefix_le (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    Pr[fun result => ProposalPrefixExceptional result.2.2.2.1.proposals result.2.2.2.1.log.length |
      certificateCacheGame adversary budget required stopAfter stopped] ≤ (2 ^ 704 : ENNReal)⁻¹ := by
  have h := congrArg (fun law : PMF CertificateGameResult =>
    Pr[fun result => ProposalPrefixExceptional result.2.2.2.proposals result.2.2.2.log.length | law])
    (certificateCacheGame_project adversary budget required stopAfter stopped)
  rw [probEvent_map] at h
  exact h.trans_le (probEvent_certificateGame_proposalPrefix_le adversary budget required stopAfter stopped)

theorem probEvent_certificateGameExceptional_le (adversary : Adversary) (q : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool)
    (hbound : HasHashQueryBound scheme adversary q) (hq : q ≤ 2 ^ 127) :
    Pr[CertificateGameExceptional | certificateCacheGame adversary q required stopAfter stopped] ≤
      (q : ENNReal) / 2 ^ 223 + (q : ENNReal) / 2 ^ 170 + (2 ^ 704 : ENNReal)⁻¹ :=
  (probEvent_or_le _ _ _).trans (add_le_add
    (probEvent_certificateCacheGame_hit_le adversary q required stopAfter stopped hbound hq)
    (probEvent_certificateCacheGame_proposalPrefix_le adversary q required stopAfter stopped))

theorem forgeAdvantage_le_certificateCacheGame_clean_add (adversary : Adversary) (q : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool)
    (hbound : HasHashQueryBound scheme adversary q) (hq : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      Pr[fun result => certificateGameVerdict result.1 = true ∧ ¬ CertificateGameExceptional result |
        certificateCacheGame adversary q required stopAfter stopped] +
        ((q : ENNReal) / 2 ^ 223 + (q : ENNReal) / 2 ^ 170 + (2 ^ 704 : ENNReal)⁻¹) := by
  classical
  rw [forgeAdvantage_eq_certificateGame adversary q required stopAfter stopped,
    ← certificateCacheGame_project, probEvent_map]
  apply le_trans _ (add_le_add le_rfl
    (probEvent_certificateGameExceptional_le adversary q required stopAfter stopped hbound hq))
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases he : CertificateGameExceptional result <;>
    by_cases hw : certificateGameVerdict result.1 = true <;>
      simp [he, hw, certificateCacheGameProject]

theorem expected_certificateCacheGame_project (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool)
    (weight : CertificateGameResult → ENNReal) :
    (∑' result, Pr[= result | certificateCacheGame adversary budget required stopAfter stopped] *
      weight (certificateCacheGameProject result)) =
        ∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] * weight result := by
  have h := congrArg (fun law : PMF CertificateGameResult => ∑' result, Pr[= result | law] * weight result)
    (certificateCacheGame_project adversary budget required stopAfter stopped)
  rw [tsum_probOutput_map_mul] at h
  exact h

theorem expected_certificateCacheGame_full_count_le (adversary : Adversary) (q : Nat)
    (stopAfter : SecretKey → CertificateStopRule) (hq : q ≤ 2 ^ 127)
    (hbound : HasHashQueryBound scheme adversary q) :
    let law := certificateCacheGame adversary q Finset.univ
      (fun key input state length record => proposalPrefixStop input state length record ||
        stopAfter key input state length record) false
    (∑' result, Pr[= result | law] * certificateBankCount result.2.2.2.1.bank) ≤
      ((3 / 2 : ENNReal) * (2 ^ 128 : ENNReal)⁻¹) *
        (∑' result, Pr[= result | law] * result.2.2.2.1.messageCalls) +
          (q : ENNReal) * (2 ^ 141 : ENNReal)⁻¹ := by
  dsimp only
  have h := expected_fixedCertificateGame_full_count_le adversary q stopAfter hq hbound
  unfold fixedCertificateGame at h
  rw [expected_certificateTerminalGame_project adversary q Finset.univ _ false fixedProposalLength
      (fun result => certificateBankCount result.2.2.2.bank),
    expected_certificateTerminalGame_project adversary q Finset.univ _ false fixedProposalLength
      (fun result => (result.2.2.2.messageCalls : ENNReal))] at h
  have hbank := expected_certificateCacheGame_project adversary q Finset.univ
    (fun key input state length record => proposalPrefixStop input state length record ||
      stopAfter key input state length record) false (fun result => certificateBankCount result.2.2.2.bank)
  have hmessage := expected_certificateCacheGame_project adversary q Finset.univ
    (fun key input state length record => proposalPrefixStop input state length record ||
      stopAfter key input state length record) false (fun result => (result.2.2.2.messageCalls : ENNReal))
  change (∑' result : CertificateCacheGameResult, Pr[= result | _] * certificateBankCount result.2.2.2.1.bank) = _ at hbank
  change (∑' result : CertificateCacheGameResult, Pr[= result | _] * (result.2.2.2.1.messageCalls : ENNReal)) = _ at hmessage
  rw [hbank, hmessage]
  exact h

end SphincsSecurity.Concrete
