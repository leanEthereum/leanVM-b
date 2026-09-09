import SphincsSecurity.Proof.CertificateProposalPrefixPotential
import SphincsSecurity.Proof.FixedCertificateCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable

def ProposalPrefixExceptional (proposals completed : Nat) : Prop :=
  targetProposalOverhead * completed + 131072 < (proposals : ENNReal)

theorem proposalPrefixExceptional_twice (proposals completed : Nat)
    (h : ProposalPrefixExceptional proposals completed) :
    3 * completed + 262144 ≤ 2 * proposals := by
  have hreal := (ENNReal.toReal_lt_toReal
    (by unfold targetProposalOverhead; finiteness) (by finiteness)).mpr h
  change (targetProposalOverhead * (completed : ENNReal) + 131072).toReal <
    (proposals : ENNReal).toReal at hreal
  rw [ENNReal.toReal_add (by unfold targetProposalOverhead; finiteness) (by finiteness),
    ENNReal.toReal_mul] at hreal
  norm_num [targetProposalOverhead, ENNReal.toReal_div] at hreal
  have hc : (0 : ℝ) ≤ completed := Nat.cast_nonneg _
  have hh : (3 : ℝ) * completed + 262144 ≤ 2 * proposals := by nlinarith
  exact_mod_cast hh

private theorem prefixPotential_barrier (tilt moment : ENNReal) (cap barrier proposals completed slack : Nat)
    (htilt : 1 ≤ tilt) (hmoment : tilt ^ 3 ≤ moment ^ 2)
    (hbarrier : 2 * barrier = 3 * cap + slack) (htwice : 3 * completed + slack ≤ 2 * proposals) :
    tilt ^ barrier ≤ tilt ^ proposals * moment ^ (cap - completed) := by
  by_cases hcount : completed ≤ cap
  · apply (ENNReal.pow_le_pow_left_iff (n := 2) (by decide)).mp
    have hdegree : 2 * barrier ≤ 2 * proposals + 3 * (cap - completed) := by omega
    calc
      _ = tilt ^ (2 * barrier) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ tilt ^ (2 * proposals + 3 * (cap - completed)) := pow_le_pow_right' htilt hdegree
      _ = (tilt ^ proposals) ^ 2 * (tilt ^ 3) ^ (cap - completed) := by
        rw [pow_add]
        simp only [← pow_mul, Nat.mul_comm proposals 2]
      _ ≤ (tilt ^ proposals) ^ 2 * (moment ^ 2) ^ (cap - completed) :=
        mul_le_mul' le_rfl (pow_le_pow_left' hmoment _)
      _ = _ := by
        rw [mul_pow]
        congr 1
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  · have hdegree : barrier ≤ proposals := by omega
    rw [Nat.sub_eq_zero_of_le (by omega), pow_zero, mul_one]
    exact pow_le_pow_right' htilt hdegree

theorem proposalPrefixExceptional_potential_ge (proposals completed : Nat)
    (h : ProposalPrefixExceptional proposals completed) :
    proposalLengthTilt ^ proposalPrefixBarrierExponent ≤ proposalPrefixPotential proposals completed :=
  prefixPotential_barrier proposalLengthTilt proposalLengthMoment signatureLimit proposalPrefixBarrierExponent
    proposals completed 262144 one_le_proposalLengthTilt proposalLengthTilt_cube_le_moment_square
    proposalPrefixBarrierExponent_twice (proposalPrefixExceptional_twice proposals completed h)

theorem probEvent_certificateGame_proposalPrefix_le (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    Pr[fun result => ProposalPrefixExceptional result.2.2.2.proposals result.2.2.2.log.length |
      certificateGame adversary budget required stopAfter stopped] ≤ (2 ^ 704 : ENNReal)⁻¹ := by
  have ht0 := proposalLengthTilt_ne_zero
  have ht := proposalLengthTilt_ne_top
  calc
    _ ≤ ∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] *
        (proposalPrefixPotential result.2.2.2.proposals result.2.2.2.log.length *
          (proposalLengthTilt ^ proposalPrefixBarrierExponent)⁻¹) := by
      apply probEvent_le_tsum_probOutput_mul_cost
      intro result hbad
      calc
        _ = proposalLengthTilt ^ proposalPrefixBarrierExponent *
            (proposalLengthTilt ^ proposalPrefixBarrierExponent)⁻¹ :=
          (ENNReal.mul_inv_cancel (pow_ne_zero _ ht0) (ENNReal.pow_ne_top ht)).symm
        _ ≤ _ := mul_le_mul' (proposalPrefixExceptional_potential_ge _ _ hbad) le_rfl
    _ = proposalLengthMoment ^ signatureLimit * (proposalLengthTilt ^ proposalPrefixBarrierExponent)⁻¹ := by
      simp_rw [← mul_assoc]
      rw [ENNReal.tsum_mul_right, expected_certificateGame_prefixPotential]
    _ ≤ _ := proposalPrefixFactor_le

theorem probEvent_fixedCertificateGame_proposalPrefix_le (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) :
    Pr[fun result => ProposalPrefixExceptional result.1.2.2.2.proposals result.1.2.2.2.log.length |
      fixedCertificateGame adversary budget required stopAfter] ≤ (2 ^ 704 : ENNReal)⁻¹ := by
  have h := congrArg (fun law : PMF CertificateGameResult =>
    Pr[fun result => ProposalPrefixExceptional result.2.2.2.proposals result.2.2.2.log.length | law])
      (certificateTerminalGame_game adversary budget required
        (fun key input state length record => proposalPrefixStop input state length record ||
          stopAfter key input state length record) false fixedProposalLength)
  rw [← PMF.monad_map_eq_map, probEvent_map] at h
  exact h.trans_le (probEvent_certificateGame_proposalPrefix_le adversary budget required _ false)

theorem proposalPrefixStop_eq_after_exception (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : CertificateMonitorActive key budget input state) :
    proposalPrefixStop input state length record =
      decide (ProposalPrefixExceptional
        (certificateMonitorUpdate key budget required stopAfter input state length record).proposals
        (certificateMonitorUpdate key budget required stopAfter input state length record).log.length) := by
  simp only [proposalPrefixStop, ProposalPrefixExceptional, certificateMonitorUpdate, if_pos hactive,
    proposalRecordLogState]

end SphincsSecurity.Concrete
