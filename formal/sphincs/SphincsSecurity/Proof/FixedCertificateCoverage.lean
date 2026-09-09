import SphincsSecurity.Proof.FixedProposalMoments
import SphincsSecurity.Proof.TerminalCertificateCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal

noncomputable def fixedCertificateGame (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) :
    PMF (CertificateGameResult × List Index) :=
  certificateTerminalGame adversary budget required
    (fun key input state length record =>
      proposalPrefixStop input state length record || stopAfter key input state length record)
    false fixedProposalLength

theorem fixedCertificateGame_original (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) :
    (fixedCertificateGame adversary budget required stopAfter).map
      (fun result => (certificateGameVerdict result.1.1, result.1.2.2.1)) =
        (liftM ((simulateQ romImpl (gameCore scheme adversary)).run ∅) : PMF _) :=
  certificateTerminalGame_original adversary budget required _ false fixedProposalLength

theorem uniformWordAverage_eq_independent {α : Type} [SampleableType α] [Fintype α] [Nonempty α]
    (steps : Nat) (payoff : List α → ENNReal) :
    uniformWordAverage steps payoff =
      ∑' word, Pr[= word | independentProposalWord (PMF.uniformOfFintype α) steps] * payoff word := by
  simp only [uniformWordAverage, probOutput_def, evalDist_sampleUniformProposalWord, PMF.evalDist_eq]

theorem expected_fixedCertificateGame_count_le_message_excess (adversary : Adversary)
    (q : Nat) (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule)
    (hbudget : q ≤ 2 ^ 127) (hbound : HasHashQueryBound scheme adversary q) (baseline : ENNReal) :
    (∑' result, Pr[= result | fixedCertificateGame adversary q required stopAfter] *
      certificateBankCount result.1.2.2.2.bank) ≤
        baseline * (∑' result, Pr[= result | fixedCertificateGame adversary q required stopAfter] *
          result.1.2.2.2.messageCalls) +
          (q : ENNReal) * uniformWordAverage fixedProposalLength
            (fun word => terminalCertificatePrice required word - baseline) := by
  let law := fixedCertificateGame adversary q required stopAfter
  have hmass :
      (∑' result, Pr[= result | law] * result.1.2.2.2.creationMass) ≤
        ∑' result, Pr[= result | law] * result.1.2.2.2.messageCalls := by
    change (∑' result, Pr[= result | certificateTerminalGame adversary q required _ false fixedProposalLength] *
      result.1.2.2.2.creationMass) ≤ _
    rw [expected_certificateTerminalGame_project adversary q required _ false fixedProposalLength
      (fun result => result.2.2.2.creationMass)]
    change _ ≤ ∑' result, Pr[= result | certificateTerminalGame adversary q required _ false fixedProposalLength] *
      (result.1.2.2.2.messageCalls : ENNReal)
    rw [expected_certificateTerminalGame_project adversary q required _ false fixedProposalLength
      (fun result => (result.2.2.2.messageCalls : ENNReal))]
    exact expected_certificateGame_creationMass_le_messageCalls adversary q required _ false
  calc
    _ ≤ ∑' result, Pr[= result | law] *
        (result.1.2.2.2.creationMass * terminalCertificatePrice required result.2) := by
      simpa [fixedCertificateGame, law, fixedProposalLength] using
        expected_certificateTerminalGame_count_le_mass_price adversary q fixedProposalLength required stopAfter hbudget
    _ ≤ ∑' result, Pr[= result | law] *
        (result.1.2.2.2.creationMass * (baseline + (terminalCertificatePrice required result.2 - baseline))) := by
      apply ENNReal.tsum_le_tsum
      intro result
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl le_add_tsub)
    _ = baseline * (∑' result, Pr[= result | law] * result.1.2.2.2.creationMass) +
        ∑' result, Pr[= result | law] *
          (result.1.2.2.2.creationMass * (terminalCertificatePrice required result.2 - baseline)) := by
      simp_rw [mul_add, ENNReal.tsum_add]
      congr 1
      calc
        _ = ∑' result, baseline * (Pr[= result | law] * result.1.2.2.2.creationMass) := by
          apply tsum_congr
          intro result
          ring
        _ = _ := ENNReal.tsum_mul_left
    _ ≤ _ := by
      apply add_le_add (mul_le_mul' le_rfl hmass)
      rw [uniformWordAverage_eq_independent]
      exact expected_certificateTerminalGame_mass_payoff_le adversary q required _ false fixedProposalLength hbound _

private theorem terminalCertificatePrice_factor (required : Finset FtsTree) (word : List Index) :
    terminalCertificatePrice required word =
      ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
        targetCertificateScale required) * proposalPowerSum required.card word := by
  unfold terminalCertificatePrice proposalPowerSum
  ring

theorem terminalCertificatePrice_full (word : List Index) :
    terminalCertificatePrice Finset.univ word = (2 ^ 128 : ENNReal)⁻¹ * fixedFullProposalPrice word := by
  have htrees : Fintype.card FtsTree = 14 := Fintype.card_fin _
  have hindex : Fintype.card Index = 2 ^ 26 := Fintype.card_fin _
  have hleaf : Fintype.card FtsLeaf = 2 ^ 10 := Fintype.card_fin _
  rw [terminalCertificatePrice_factor, Finset.card_univ, htrees]
  have hcoefficient :
      ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
        targetCertificateScale Finset.univ) = (2 ^ 128 : ENNReal)⁻¹ * (2 ^ 48 : ENNReal)⁻¹ := by
    unfold targetCertificateScale
    rw [Finset.card_univ, htrees, hindex, hleaf]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ftsTreeHeight, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow]
  rw [hcoefficient, fixedFullProposalPrice, mul_assoc]

theorem expected_fixedCertificateGame_full_count_le (adversary : Adversary) (q : Nat)
    (stopAfter : SecretKey → CertificateStopRule) (hbudget : q ≤ 2 ^ 127)
    (hbound : HasHashQueryBound scheme adversary q) :
    (∑' result, Pr[= result | fixedCertificateGame adversary q Finset.univ stopAfter] *
      certificateBankCount result.1.2.2.2.bank) ≤
        ((3 / 2 : ENNReal) * (2 ^ 128 : ENNReal)⁻¹) *
          (∑' result, Pr[= result | fixedCertificateGame adversary q Finset.univ stopAfter] *
            result.1.2.2.2.messageCalls) + (q : ENNReal) * (2 ^ 141 : ENNReal)⁻¹ := by
  have h := expected_fixedCertificateGame_count_le_message_excess adversary q Finset.univ stopAfter
    hbudget hbound ((3 / 2 : ENNReal) * (2 ^ 128 : ENNReal)⁻¹)
  apply h.trans
  apply add_le_add le_rfl
  apply mul_le_mul' le_rfl
  have hscale (word : List Index) :
      terminalCertificatePrice Finset.univ word - (3 / 2 : ENNReal) * (2 ^ 128 : ENNReal)⁻¹ =
        (2 ^ 128 : ENNReal)⁻¹ * (fixedFullProposalPrice word - 3 / 2) := by
    rw [terminalCertificatePrice_full, mul_comm (3 / 2 : ENNReal), ENNReal.mul_sub (fun _ _ => by finiteness)]
  simp_rw [hscale]
  rw [uniformWordAverage_mul_left]
  calc
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * (2 ^ 13 : ENNReal)⁻¹ :=
      mul_le_mul' le_rfl uniformWordAverage_fixedFull_excess_le
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow]

theorem terminalCertificatePrice_near (required : Finset FtsTree) (hdegree : required.card = 13)
    (word : List Index) :
    terminalCertificatePrice required word =
      ((2 ^ 128 : ENNReal)⁻¹ * (14 : ENNReal)⁻¹) * fixedNearProposalPrice word := by
  have hindex : Fintype.card Index = 2 ^ 26 := Fintype.card_fin _
  have hleaf : Fintype.card FtsLeaf = 2 ^ 10 := Fintype.card_fin _
  rw [terminalCertificatePrice_factor, hdegree]
  have hcoefficient :
      ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
        targetCertificateScale required) =
      ((2 ^ 128 : ENNReal)⁻¹ * (14 : ENNReal)⁻¹) * (14 * (2 ^ 38 : ENNReal)⁻¹) := by
    unfold targetCertificateScale
    rw [hdegree, hindex, hleaf]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ftsTreeHeight, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow]
  rw [hcoefficient, fixedNearProposalPrice, mul_assoc]

theorem expected_fixedCertificateGame_near_subset_count_le (adversary : Adversary) (q : Nat)
    (required : Finset FtsTree) (hdegree : required.card = 13) (stopAfter : SecretKey → CertificateStopRule)
    (hbudget : q ≤ 2 ^ 127) (hbound : HasHashQueryBound scheme adversary q) :
    (∑' result, Pr[= result | fixedCertificateGame adversary q required stopAfter] *
      certificateBankCount result.1.2.2.2.bank) ≤
        (q : ENNReal) * (((2 ^ 128 : ENNReal)⁻¹ * (14 : ENNReal)⁻¹) * 557) := by
  have h := expected_fixedCertificateGame_count_le_message_excess adversary q required stopAfter hbudget hbound 0
  simp only [zero_mul, zero_add, tsub_zero] at h
  apply h.trans
  apply mul_le_mul' le_rfl
  simp_rw [terminalCertificatePrice_near required hdegree]
  rw [uniformWordAverage_mul_left]
  exact mul_le_mul' le_rfl uniformWordAverage_fixedNear_mean_le

theorem expected_fixedCertificateGame_near_count_le (adversary : Adversary) (q : Nat)
    (stopAfter : SecretKey → CertificateStopRule) (hbudget : q ≤ 2 ^ 127)
    (hbound : HasHashQueryBound scheme adversary q) :
    (∑ omitted : FtsTree,
      ∑' result, Pr[= result | fixedCertificateGame adversary q (Finset.univ.erase omitted) stopAfter] *
        certificateBankCount result.1.2.2.2.bank) ≤ (557 : ENNReal) * q / (2 ^ 128 : ENNReal) := by
  have htrees : Fintype.card FtsTree = 14 := Fintype.card_fin _
  calc
    _ ≤ ∑ _omitted : FtsTree,
        (q : ENNReal) * (((2 ^ 128 : ENNReal)⁻¹ * (14 : ENNReal)⁻¹) * 557) := by
      apply Finset.sum_le_sum
      intro omitted _
      apply expected_fixedCertificateGame_near_subset_count_le adversary q _ _ stopAfter hbudget hbound
      rw [Finset.card_erase_of_mem (Finset.mem_univ omitted), Finset.card_univ, htrees]
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, htrees, nsmul_eq_mul]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow]
      ring

end SphincsSecurity.Concrete
