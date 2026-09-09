import SphincsSecurity.Proof.CachedIndexExcessConcentration
import SphincsSecurity.Proof.MessageDeficitConcentration

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

def CertificateCacheExceptional (key : SecretKey) (cache : QueryCache HashSpec) : Prop :=
  MessageDeficitExceptional key cache ∨ CachedIndexExcessExceptional key.parameter cache

noncomputable def certificateCacheExceptionPotential (key : SecretKey) (remaining : Nat)
    (cache : QueryCache HashSpec) : ENNReal :=
  fourthMomentBudget remaining (messageDeficitMoment key.parameter key.root cache 2)
      (messageDeficitMoment key.parameter key.root cache 4) / 2 ^ 372 +
    (cachedIndexExcessMoment key.parameter cache + (remaining : ENNReal) * (2 ^ 10 : ENNReal)⁻¹) / 2 ^ 160

theorem certificateCacheExceptionPotential_bad (key : SecretKey) (remaining : Nat)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hbad : CertificateCacheExceptional key cache) :
    1 ≤ certificateCacheExceptionPotential key remaining cache := by
  rcases hbad with hdeficit | hindex
  · apply le_trans (b := fourthMomentBudget remaining (messageDeficitMoment key.parameter key.root cache 2)
      (messageDeficitMoment key.parameter key.root cache 4) / 2 ^ 372) _ le_self_add
    calc
      1 = (2 ^ 372 : ENNReal) / 2 ^ 372 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right
        ((messageDeficitExceptional_fourthMoment_le key cache hfinite hdeficit).trans
          (fourth_le_fourthMomentBudget remaining _ _)) _
  · apply le_trans (b := (cachedIndexExcessMoment key.parameter cache +
      (remaining : ENNReal) * (2 ^ 10 : ENNReal)⁻¹) / 2 ^ 160) _ le_add_self
    calc
      1 = (2 ^ 160 : ENNReal) / 2 ^ 160 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right
        ((cachedIndexExcessExceptional_moment_ge key.parameter cache hindex).trans le_self_add) _

theorem certificateCacheExceptionPotential_mono (key : SecretKey) (remaining : Nat)
    (cache : QueryCache HashSpec) :
    certificateCacheExceptionPotential key remaining cache ≤
      certificateCacheExceptionPotential key (remaining + 1) cache := by
  apply add_le_add (ENNReal.div_le_div_right (fourthMomentBudget_mono remaining _ _) _)
  apply ENNReal.div_le_div_right
  simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← add_assoc]
  exact le_self_add

theorem expected_certificateCacheExceptionPotential_fresh_le (key : SecretKey) (remaining : Nat)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none) :
    (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      certificateCacheExceptionPotential key remaining (cache.cacheQuery input answer)) ≤
        certificateCacheExceptionPotential key (remaining + 1) cache := by
  simp only [certificateCacheExceptionPotential, mul_add, ENNReal.tsum_add]
  apply add_le_add
  · simp_rw [div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right]
    exact mul_le_mul' (expected_fourthMomentBudget_fresh_le
      (fun current => messageDeficitMoment key.parameter key.root current 2)
      (fun current => messageDeficitMoment key.parameter key.root current 4) remaining cache input
      (expected_messageDeficit_second_le key.parameter key.root cache hfinite input hfresh)
      (expected_messageDeficit_fourth_le key.parameter key.root cache hfinite input hfresh)) le_rfl
  · simp only [div_eq_mul_inv, mul_add, ← mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_right,
      tsum_probOutput_of_liftM_PMF, one_mul]
    have hstep := expected_cachedIndexExcessMoment_le key.parameter cache hfinite input hfresh
    calc
      _ ≤ (cachedIndexExcessMoment key.parameter cache + (2 ^ 10 : ENNReal)⁻¹ +
          (remaining : ENNReal) * (2 ^ 10 : ENNReal)⁻¹) * (2 ^ 160 : ENNReal)⁻¹ :=
        mul_le_mul' (add_le_add hstep le_rfl) le_rfl
      _ = _ := by push_cast; ring

theorem certificateCacheExceptionPotential_initial_le (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    certificateCacheExceptionPotential key q cache ≤ (q : ENNReal) / 2 ^ 223 + (q : ENNReal) / 2 ^ 170 := by
  have hcells : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none :=
    fun payload => hnone _ ⟨payload, rfl⟩
  have hcounts := cachedMessageEntryCount_zero_of_no_inputs key.parameter key.root cache hcells
  rw [certificateCacheExceptionPotential,
    messageDeficitMoment_zero_of_no_inputs key.parameter key.root cache hcounts 2 (by decide),
    messageDeficitMoment_zero_of_no_inputs key.parameter key.root cache hcounts 4 (by decide),
    cachedIndexExcessMoment_zero_of_no_message key.parameter cache hnone, zero_add]
  apply add_le_add (fourthMomentBudget_zero_le q hq)
  apply le_of_eq
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

end SphincsSecurity.Concrete
