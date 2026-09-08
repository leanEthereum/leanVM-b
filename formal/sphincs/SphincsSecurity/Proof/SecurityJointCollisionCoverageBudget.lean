import SphincsSecurity.Proof.InitializedJointCollisionCoverage

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledJointCollisionCoverageCharge (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedJointCollisionCoverageCharge adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

noncomputable def sampledJointCollisionCoverageCredit (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedJointCollisionCoverageCredit adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

private theorem expected_add_le_const_add (computation : ProbComp α) (left credit risk : α → ENNReal) (initial : ENNReal)
    (h : ∀ result ∈ support computation, left result + credit result ≤ initial + risk result) :
    (∑' result, Pr[= result | computation] * left result) + (∑' result, Pr[= result | computation] * credit result) ≤
      initial + ∑' result, Pr[= result | computation] * risk result := by
  rw [← ENNReal.tsum_add]
  calc
    _ ≤ ∑' result, Pr[= result | computation] * (initial + risk result) := by
      apply ENNReal.tsum_le_tsum
      intro result
      rw [← mul_add]
      by_cases hr : result ∈ support computation
      · exact mul_le_mul' le_rfl (h result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl

theorem sampledJointCollisionCoverageRisk_add_credit_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledJointCollisionCoverageRisk adversary q fuel + sampledJointCollisionCoverageCredit adversary q fuel ≤
      min 1 ((q : ENNReal) * initialRawIndexRate q) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
        sampledJointCollisionCoverageCharge adversary q fuel := by
  unfold sampledJointCollisionCoverageRisk sampledJointCollisionCoverageCredit sampledJointCollisionCoverageCharge
  apply expected_add_le_const_add
  intro parameter hp
  apply expected_add_le_const_add
  intro ftsSecret hfts
  apply expected_add_le_const_add
  intro table _
  exact expected_retained_jointCollisionCoverage_add_credit_le adversary q hq hqMax parameter hp table
    (curryFtsTableEquiv ftsSecret) hfts fuel

theorem forgeAdvantage_add_jointCollisionCoverageCredit_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    forgeAdvantage scheme adversary + sampledJointCollisionCoverageCredit adversary q fuel ≤
      min 1 ((q : ENNReal) * initialRawIndexRate q) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
        sampledJointCollisionCoverageCharge adversary q fuel :=
  (add_le_add (forgeAdvantage_le_jointCollisionCoverage adversary q hq fuel) le_rfl).trans
    (sampledJointCollisionCoverageRisk_add_credit_le adversary q hq hqMax fuel)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
