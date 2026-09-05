import SphincsSecurity.Proof.OtsProbeCanonicalChargeRoot

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

noncomputable def sampledCanonicalJointCharge (adversary : Adversary) (fuel : Nat) : ℝ≥0∞ :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' table, Pr[= table | sampleOtsHashTable] *
      ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
        canonicalJointChargeAfterTable adversary parameter table ftsSecret fuel

set_option maxRecDepth 100000 in
theorem sampledCanonicalJointCharge_le_refinedReserve (adversary : Adversary) (fuel : Nat) :
    sampledCanonicalJointCharge adversary fuel ≤ sampledQueryCharge otsOpeningRefinedQueryReserve adversary := by
  unfold sampledCanonicalJointCharge sampledQueryCharge
  simp only [sampleSecrets, tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  have hcoupled := expected_cost_le_of_relTriple relTriple_uniformOtsHashTable_sampleOtsSecrets
    (fun table => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      canonicalJointChargeAfterTable adversary parameter table ftsSecret fuel)
    (fun otsSecret => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      expectedQueryCharge (otsOpeningRefinedQueryReserve (primitiveAccountingKey parameter otsSecret ftsSecret))
        (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅)
    (fun _ => 0) (by
      intro table otsSecret hsecrets
      simp only [add_zero]
      rw [← hsecrets]
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      exact mul_le_mul' le_rfl (canonicalJointChargeAfterTable_le_gameReserve adversary parameter table ftsSecret fuel))
  simpa only [sampleOtsHashTable, mul_zero, tsum_zero, add_zero] using hcoupled

end SphincsSecurity.Concrete.OtsProbeSimulation
