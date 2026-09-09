import SphincsSecurity.Proof.ProposalLengthProjection

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal

theorem expected_proposalBlockLength_pow (accept : ENNReal) (hpos : accept ≠ 0)
    (hle : accept ≤ 1) (tilt : ENNReal) :
    (∑' length, Pr[= length | proposalBlockLength accept hpos hle] * tilt ^ length) =
      (accept * tilt) * (1 - (1 - accept) * tilt)⁻¹ := by
  rw [proposalBlockLength, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
  simp only [PMF.probOutput_eq_apply, proposalFailureCount_apply, pow_succ]
  calc
    _ = (accept * tilt) * ∑' failures : Nat, ((1 - accept) * tilt) ^ failures := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro failures
      rw [mul_pow]
      ring
    _ = _ := by rw [ENNReal.tsum_geometric]

noncomputable def proposalLengthTilt : ENNReal := 129 / 128

noncomputable def proposalLengthMoment : ENNReal := 132096 / 130559

theorem proposalLengthTilt_ne_zero : proposalLengthTilt ≠ 0 := by
  unfold proposalLengthTilt
  exact ENNReal.div_ne_zero.mpr ⟨by norm_num, by finiteness⟩

theorem proposalLengthTilt_ne_top : proposalLengthTilt ≠ ⊤ := by
  unfold proposalLengthTilt
  finiteness

theorem proposalLengthMoment_ne_top : proposalLengthMoment ≠ ⊤ := by
  unfold proposalLengthMoment
  finiteness

theorem one_le_proposalLengthTilt : 1 ≤ proposalLengthTilt := by
  apply (ENNReal.toReal_le_toReal (by finiteness) proposalLengthTilt_ne_top).mp
  norm_num [proposalLengthTilt, ENNReal.toReal_div]

theorem proposalLengthTilt_cube_le_moment_square :
    proposalLengthTilt ^ 3 ≤ proposalLengthMoment ^ 2 := by
  have ht := proposalLengthTilt_ne_top
  have hm := proposalLengthMoment_ne_top
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [proposalLengthTilt, proposalLengthMoment, ENNReal.toReal_pow, ENNReal.toReal_div]

theorem expected_targetProposalBlockLength_pow :
    (∑' length, Pr[= length | proposalBlockLength targetProposalAcceptance targetProposalAcceptance_ne_zero
      targetProposalAcceptance_lt_one.le] * proposalLengthTilt ^ length) = proposalLengthMoment := by
  rw [expected_proposalBlockLength_pow]
  have ha : targetProposalAcceptance ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) targetProposalAcceptance_lt_one.le
  have ht := proposalLengthTilt_ne_top
  have hratio : (1 - targetProposalAcceptance) * proposalLengthTilt < 1 := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_sub_of_le targetProposalAcceptance_lt_one.le (by finiteness)]
    norm_num [proposalLengthTilt, targetProposalAcceptance, targetProposalOverhead,
      ENNReal.toReal_inv, ENNReal.toReal_div]
  have hden : 1 - (1 - targetProposalAcceptance) * proposalLengthTilt ≠ 0 :=
    (tsub_pos_iff_lt.mpr hratio).ne'
  have hi : (1 - (1 - targetProposalAcceptance) * proposalLengthTilt)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr hden
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) proposalLengthMoment_ne_top).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_sub_of_le hratio.le (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le targetProposalAcceptance_lt_one.le (by finiteness)]
  norm_num [proposalLengthTilt, proposalLengthMoment, targetProposalAcceptance, targetProposalOverhead,
    ENNReal.toReal_inv, ENNReal.toReal_div]

theorem expected_recordLengthBridge_pow {Ω : Type} (record : PMF Ω) :
    (∑' result, Pr[= result | recordLengthBridge record targetProposalAcceptance
      targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le] * proposalLengthTilt ^ result.1) =
        proposalLengthMoment := by
  have h := congrArg (fun law : PMF Nat => ∑' length, Pr[= length | law] * proposalLengthTilt ^ length)
    (recordLengthBridge_length record targetProposalAcceptance targetProposalAcceptance_ne_zero
      targetProposalAcceptance_lt_one.le)
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul, expected_targetProposalBlockLength_pow] at h
  exact h

end SphincsSecurity.Concrete
