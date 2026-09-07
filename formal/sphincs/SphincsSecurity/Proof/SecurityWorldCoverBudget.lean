import SphincsSecurity.Proof.RetainedWorldCoverBudget
import SphincsSecurity.Proof.SecurityInterleavedCover

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def worldCoverageBudget (q : Nat) : ENNReal :=
  ((7 * q : Nat) : ENNReal) * ((2 ^ 136 : Nat) : ENNReal)⁻¹

theorem worldCoverageBudget_eq (q : Nat) :
    worldCoverageBudget q = (q : ENNReal) * (7 * (2 : ENNReal) ^ 40) * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  have hconstant : (7 : ENNReal) * (2 : ENNReal) ^ 40 * ((2 ^ 176 : Nat) : ENNReal)⁻¹ =
      7 * ((2 ^ 136 : Nat) : ENNReal)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
  rw [worldCoverageBudget, Nat.cast_mul]
  calc
    _ = (q : ENNReal) * (7 * ((2 ^ 136 : Nat) : ENNReal)⁻¹) := by ring
    _ = _ := by rw [← hconstant]; ring

noncomputable def retainedSigningAndReuseCharge (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (table : Coordinate → Digest) (q : Nat) : ENNReal :=
  (q : ENNReal) * expectedRetainedCompletionReuseCharge adversary parameter otsSecret table q * ((2 ^ 176 : Nat) : ENNReal)⁻¹ +
    expectedRetainedSigningCoverCharge adversary parameter otsSecret table q

noncomputable def sampledRetainedSigningAndReuseCharge (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        retainedSigningAndReuseCharge adversary parameter
          (tableSecrets parameter table (curryFtsTableEquiv ftsSecret)).otsSecret (curryFtsTableEquiv ftsSecret) q

private theorem expected_le_const_add {α : Type} (computation : ProbComp α) (left right : α → ENNReal) (cost : ENNReal)
    (h : ∀ result ∈ support computation, left result ≤ cost + right result) :
    (∑' result, Pr[= result | computation] * left result) ≤ cost + ∑' result, Pr[= result | computation] * right result := by
  calc
    _ ≤ ∑' result, Pr[= result | computation] * (cost + right result) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support computation
      · exact mul_le_mul' le_rfl (h result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ ≤ _ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl

theorem sampledRetainedCoverCharge_le_worldBudget_add_signingAndReuse
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    sampledRetainedCoverCharge adversary q ≤ worldCoverageBudget q + sampledRetainedSigningAndReuseCharge adversary q := by
  unfold sampledRetainedCoverCharge sampledRetainedSigningAndReuseCharge
  apply expected_le_const_add
  intro parameter hp
  apply expected_le_const_add
  intro ftsSecret hfts
  apply expected_le_const_add
  intro table _
  have hbound := isQueryBoundP_gameAfterSecrets adversary q hq hp
    (OtsProbeSimulation.mem_support_sampleOtsSecrets_all
      (tableSecrets parameter table (curryFtsTableEquiv ftsSecret)).otsSecret) hfts
  apply (expectedRetainedCoverCharge_le_worldBudget_add_signing adversary parameter
    (tableSecrets parameter table (curryFtsTableEquiv ftsSecret)).otsSecret (curryFtsTableEquiv ftsSecret) q hqMax hbound).trans_eq
  rw [worldCoverageBudget_eq, retainedSigningAndReuseCharge]
  ring

theorem forgeAdvantage_add_messageReserves_le_worldBudget_add_signingAndReuse
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1)) *
        (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + worldCoverageBudget q + sampledRetainedSigningAndReuseCharge adversary q :=
  (forgeAdvantage_add_messageReserves_le_interleavedCharge adversary q hq hqMax).trans
    ((add_le_add le_rfl (sampledRetainedCoverCharge_le_worldBudget_add_signingAndReuse adversary q hq hqMax)).trans_eq
      (add_assoc _ _ _).symm)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
