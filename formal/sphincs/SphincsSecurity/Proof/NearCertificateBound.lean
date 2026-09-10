import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.PoissonProposalMoments
import SphincsSecurity.Proof.TerminalCertificateCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal

set_option maxHeartbeats 2000000 in
theorem poissonPowerMoment_thirteen :
    poissonPowerMoment (19 / 50) 13 =
      (1986585224814431503899382459 : ENNReal) / 12207031250000000000000 := by
  unfold poissonPowerMoment
  apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.sum_ne_top.mpr (fun _ _ => by finiteness)) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_sum, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

theorem terminalProposalAverage_nearPrice (required : Finset FtsTree) (hdegree : required.card = 13) :
    terminalProposalAverage (terminalCertificatePrice required) ≤
      ((557 : ENNReal) / 14) / (2 ^ 128 : Nat) := by
  rw [terminalProposalAverage_certificatePrice, hdegree, poissonPowerMoment_thirteen]
  unfold targetCertificateScale
  rw [hdegree]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ftsTreeHeight, FtsLeaf, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_div, ENNReal.toReal_pow]

theorem expected_poissonCertificateGame_near_subset_count_le (adversary : Adversary)
    (q : Nat) (required : Finset FtsTree) (stopAfter : Nat → SecretKey → CertificateStopRule)
    (hbudget : q ≤ 2 ^ 127) (hbound : HasHashQueryBound scheme adversary q) (hdegree : required.card = 13) :
    (∑' result, Pr[= result | poissonCertificateGame adversary q required stopAfter] *
      certificateBankCount result.2.1.2.2.2.bank) ≤
        (q : ENNReal) * (((557 : ENNReal) / 14) / (2 ^ 128 : Nat)) := by
  have h := expected_poissonCertificateGame_count_le_message_excess adversary q required stopAfter hbudget hbound 0
  simp only [zero_mul, zero_add, tsub_zero] at h
  exact h.trans (mul_le_mul' le_rfl (terminalProposalAverage_nearPrice required hdegree))

theorem expected_poissonCertificateGame_near_count_le (adversary : Adversary)
    (q : Nat) (stopAfter : Nat → SecretKey → CertificateStopRule)
    (hbudget : q ≤ 2 ^ 127) (hbound : HasHashQueryBound scheme adversary q) :
    (∑ omitted : FtsTree, ∑' result,
      Pr[= result | poissonCertificateGame adversary q (Finset.univ.erase omitted) stopAfter] *
        certificateBankCount result.2.1.2.2.2.bank) ≤
          (557 : ENNReal) * (q : ENNReal) / (2 ^ 128 : Nat) := by
  classical
  calc
    _ ≤ ∑ _ : FtsTree, (q : ENNReal) * (((557 : ENNReal) / 14) / (2 ^ 128 : Nat)) := by
      apply Finset.sum_le_sum
      intro omitted _
      exact expected_poissonCertificateGame_near_subset_count_le adversary q (Finset.univ.erase omitted)
        stopAfter hbudget hbound (by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
          have hcard : Fintype.card FtsTree = 14 := by decide
          rw [hcard])
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : Fintype.card FtsTree = 14 := by decide
      rw [hcard]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
      ring

end SphincsSecurity.Concrete
