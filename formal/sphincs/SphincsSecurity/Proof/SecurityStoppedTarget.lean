import SphincsSecurity.Proof.InitializedStoppedTarget

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledStoppedTargetCharge (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedStoppedTargetCharge adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

theorem sampledLiveNonSecretResidual_le_stopped_arrival
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledLiveNonSecretResidual adversary q fuel ≤ sampledStoppedTargetCharge adversary q fuel := by
  unfold sampledLiveNonSecretResidual sampledStoppedTargetCharge
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hp : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    by_cases hfts : ftsSecret ∈ support sampleFtsSecrets
    · apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro table
      exact mul_le_mul' le_rfl (probEvent_liveNonSecretResidual_le_initialized_stopped_arrival adversary q hq hqMax parameter hp table
        (curryFtsTableEquiv ftsSecret) hfts fuel)
    · rw [probOutput_eq_zero_of_not_mem_support hfts, zero_mul, zero_mul]
  · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]

theorem forgeAdvantage_add_message_and_signingReserves_le_stoppedTargetCharge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledSigningNonEncodingReserve adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + sampledStoppedTargetCharge adversary q (q + 1) :=
  (forgeAdvantage_add_message_and_signingReserves_le_live adversary q hq hqMax).trans
    (add_le_add le_rfl (sampledLiveNonSecretResidual_le_stopped_arrival adversary q hq hqMax (q + 1)))

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
