import SphincsSecurity.Proof.OtsProbeStartHistoryRisk
import SphincsSecurity.Proof.OtsProbePrivateHistoryRate

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

theorem privateHistoryGuessRate_mul_survival (budget : Nat) (hbudget : budget < Fintype.card Digest) :
    privateHistoryGuessRate budget * (1 - (budget : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) =
      (Fintype.card Digest : ENNReal)⁻¹ := by
  have hnonzero : ((Fintype.card Digest - budget : Nat) : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.sub_ne_zero_of_lt hbudget
  have hspace : (Fintype.card Digest : ENNReal) ≠ 0 := by
    exact_mod_cast (show Fintype.card Digest ≠ 0 from Fintype.card_ne_zero)
  have hsurvival : 1 - (budget : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ =
      ((Fintype.card Digest - budget : Nat) : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
    rw [ENNReal.natCast_sub, ENNReal.sub_mul (fun _ _ => ENNReal.inv_ne_top.mpr hspace),
      ENNReal.mul_inv_cancel hspace (by simp)]
  rw [hsurvival, privateHistoryGuessRate, ← mul_assoc, ENNReal.inv_mul_cancel hnonzero (by simp), one_mul]

theorem probEvent_no_chainStartHistoryHit_ge_survival
    (context : DeferredContext) (history : List Probe) (budget : Nat) (hlength : history.length ≤ budget) :
    1 - (budget : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ ≤
      Pr[fun base => ¬ChainStartHistoryHit context history base | sampleOtsHashTable] := by
  have hbad : Pr[fun base => ¬¬ChainStartHistoryHit context history base | sampleOtsHashTable] ≤
      (budget : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
    simp only [not_not]
    apply (probEvent_chainStartHistoryHit_le context history).trans
    simpa only [show Fintype.card Digest = 2 ^ digestBits by simp] using
      mul_le_mul' (Nat.cast_le.mpr hlength) (le_refl (Fintype.card Digest : ENNReal)⁻¹)
  exact probEvent_one_sub_le_of_compl_le (by simp : Pr[⊥ | sampleOtsHashTable] = 0) hbad

theorem expected_history_guarded_chainStart_allowance_le_rate
    (context : DeferredContext) (history : List Probe) (budget : Nat)
    (hlength : history.length ≤ budget) (hbudget : budget < Fintype.card Digest)
    (index : OtsSecretIndex) (digest : Digest) (hmissing : context.state.values index.coordinate = none) :
    (∑' base, Pr[= base | sampleOtsHashTable] *
      if ¬ChainStartHistoryHit context history base then
        candidateFailureAllowance (completedStartTable context.state base) context (some ⟨index.coordinate, digest⟩)
      else 0) ≤
      (unmaterializedCandidateCharge (materializedDeferredState context) (some ⟨index.coordinate, digest⟩) : ENNReal) *
        privateHistoryGuessRate budget *
        Pr[fun base => ¬ChainStartHistoryHit context history base | sampleOtsHashTable] := by
  let charge : ENNReal := unmaterializedCandidateCharge (materializedDeferredState context) (some ⟨index.coordinate, digest⟩)
  calc
    _ ≤ ∑' base, Pr[= base | sampleOtsHashTable] *
        candidateFailureAllowance (completedStartTable context.state base) context (some ⟨index.coordinate, digest⟩) := by
      apply ENNReal.tsum_le_tsum
      intro base
      apply mul_le_mul' le_rfl
      split_ifs <;> first | exact le_rfl | exact bot_le
    _ ≤ charge * (Fintype.card Digest : ENNReal)⁻¹ := by
      simpa only [show Fintype.card Digest = 2 ^ digestBits by simp] using
        expected_candidateFailureAllowance_chainStart_of_missing context index digest hmissing
    _ = charge * privateHistoryGuessRate budget *
        (1 - (budget : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) := by
      rw [mul_assoc, privateHistoryGuessRate_mul_survival budget hbudget]
    _ ≤ _ := mul_le_mul' le_rfl (probEvent_no_chainStartHistoryHit_ge_survival context history budget hlength)

end SphincsSecurity.Concrete.OtsProbeSimulation
