import SphincsSecurity.Proof.CertificateFamilyGame
import SphincsSecurity.Proof.UnitCertificateCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expected_certificateFamilyGame_full_count_le (adversary : Adversary) (q : Nat)
    (stopAfter : SecretKey → CertificateCoreStopRule) (hq : q ≤ 2 ^ 127)
    (hbound : HasHashQueryBound scheme adversary q) :
    let law := certificateFamilyGame adversary q (fun key => certificateCoreGuard (stopAfter key)) false
    (∑' result, Pr[= result | law] * certificateBankCount (result.2.2.2.ledger none).bank) ≤
      (2 ^ 128 : ENNReal)⁻¹ * (∑' result, Pr[= result | law] * result.2.2.2.core.messageCalls) +
        (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) := by
  dsimp only
  have hbank := expected_certificateFamilyGame_project adversary q
    (fun key => certificateCoreGuard (stopAfter key)) false none
    (fun result => certificateBankCount result.2.2.2.1.bank)
  have hmessage := expected_certificateFamilyGame_project adversary q
    (fun key => certificateCoreGuard (stopAfter key)) false none
    (fun result => (result.2.2.2.1.messageCalls : ENNReal))
  change (∑' result : CertificateFamilyGameResult, Pr[= result | _] *
    certificateBankCount (result.2.2.2.ledger none).bank) = _ at hbank
  change (∑' result : CertificateFamilyGameResult, Pr[= result | _] *
    (result.2.2.2.core.messageCalls : ENNReal)) = _ at hmessage
  rw [hbank, hmessage]
  simp only [certificateCoreStop_guard, certificateRequiredTrees]
  exact expected_certificateCacheGame_full_unit_count_le adversary q
    (fun key => certificateCoreStop (stopAfter key)) hq hbound

private theorem expected_certificateCacheGame_near_subset_count_le (adversary : Adversary) (q : Nat)
    (required : Finset FtsTree) (hdegree : required.card = 13) (stopAfter : SecretKey → CertificateStopRule)
    (hq : q ≤ 2 ^ 127) (hbound : HasHashQueryBound scheme adversary q) :
    let law := certificateCacheGame adversary q required
      (fun key input state length record => proposalPrefixStop input state length record ||
        stopAfter key input state length record) false
    (∑' result, Pr[= result | law] * certificateBankCount result.2.2.2.1.bank) ≤
      (q : ENNReal) * (((2 ^ 128 : ENNReal)⁻¹ * (14 : ENNReal)⁻¹) * 557) := by
  dsimp only
  have h := expected_fixedCertificateGame_near_subset_count_le adversary q required hdegree stopAfter hq hbound
  unfold fixedCertificateGame at h
  rw [expected_certificateTerminalGame_project adversary q required _ false fixedProposalLength
    (fun result => certificateBankCount result.2.2.2.bank)] at h
  have hbank := expected_certificateCacheGame_project adversary q required
    (fun key input state length record => proposalPrefixStop input state length record ||
      stopAfter key input state length record) false (fun result => certificateBankCount result.2.2.2.bank)
  change (∑' result : CertificateCacheGameResult, Pr[= result | _] * certificateBankCount result.2.2.2.1.bank) = _ at hbank
  rw [hbank]
  exact h

theorem expected_certificateFamilyGame_near_subset_count_le (adversary : Adversary) (q : Nat)
    (stopAfter : SecretKey → CertificateCoreStopRule) (hq : q ≤ 2 ^ 127)
    (hbound : HasHashQueryBound scheme adversary q) (omitted : FtsTree) :
    let law := certificateFamilyGame adversary q (fun key => certificateCoreGuard (stopAfter key)) false
    (∑' result, Pr[= result | law] * certificateBankCount (result.2.2.2.ledger (some omitted)).bank) ≤
      (q : ENNReal) * (((2 ^ 128 : ENNReal)⁻¹ * (14 : ENNReal)⁻¹) * 557) := by
  dsimp only
  have hbank := expected_certificateFamilyGame_project adversary q
    (fun key => certificateCoreGuard (stopAfter key)) false (some omitted)
    (fun result => certificateBankCount result.2.2.2.1.bank)
  change (∑' result : CertificateFamilyGameResult, Pr[= result | _] *
    certificateBankCount (result.2.2.2.ledger (some omitted)).bank) = _ at hbank
  rw [hbank]
  simp only [certificateCoreStop_guard, certificateRequiredTrees]
  apply expected_certificateCacheGame_near_subset_count_le adversary q _ _ _ hq hbound
  rw [Finset.card_erase_of_mem (Finset.mem_univ omitted), Finset.card_univ,
    show Fintype.card FtsTree = 14 from Fintype.card_fin _]

noncomputable def certificateFamilyNearCount (monitor : CertificateFamilyMonitor) : ENNReal :=
  ∑ omitted : FtsTree, certificateBankCount (monitor.ledger (some omitted)).bank

theorem expected_certificateFamilyGame_near_count_le (adversary : Adversary) (q : Nat)
    (stopAfter : SecretKey → CertificateCoreStopRule) (hq : q ≤ 2 ^ 127)
    (hbound : HasHashQueryBound scheme adversary q) :
    let law := certificateFamilyGame adversary q (fun key => certificateCoreGuard (stopAfter key)) false
    (∑' result, Pr[= result | law] * certificateFamilyNearCount result.2.2.2) ≤
      (557 : ENNReal) * q / (2 ^ 128 : ENNReal) := by
  dsimp only
  simp only [certificateFamilyNearCount, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  calc
    _ ≤ ∑ _omitted : FtsTree,
        (q : ENNReal) * (((2 ^ 128 : ENNReal)⁻¹ * (14 : ENNReal)⁻¹) * 557) := by
      apply Finset.sum_le_sum
      intro omitted _
      exact expected_certificateFamilyGame_near_subset_count_le adversary q stopAfter hq hbound omitted
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, show Fintype.card FtsTree = 14 from Fintype.card_fin _, nsmul_eq_mul]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow]
      ring

end SphincsSecurity.Concrete
