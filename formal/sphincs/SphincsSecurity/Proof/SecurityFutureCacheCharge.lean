import SphincsSecurity.Proof.RetainedFutureCacheCharge
import SphincsSecurity.Proof.SecurityInterleavedCover

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_liveNonSecretResidual_le_futureCacheCharge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[LiveNonSecretResidual parameter otsTable ftsTable |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] ≤
        expectedRetainedFutureCacheCharge adversary parameter (tableSecrets parameter otsTable ftsTable).otsSecret ftsTable q := by
  apply (probEvent_liveNonSecretResidual_le_original adversary q hq parameter hp otsTable ftsTable hfts fuel).trans
  apply (probEvent_original_residual_le_actual_validObservedCover adversary parameter otsTable ftsTable).trans
  exact probEvent_actualRetained_validObservedCover_le_futureCharge_of_hashQueryBound adversary parameter hp _
    (OtsProbeSimulation.mem_support_sampleOtsSecrets_all _) ftsTable hfts q hqMax hq

noncomputable def sampledRetainedFutureCacheCharge (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        expectedRetainedFutureCacheCharge adversary parameter
          (tableSecrets parameter table (curryFtsTableEquiv ftsSecret)).otsSecret (curryFtsTableEquiv ftsSecret) q

theorem sampledLiveNonSecretResidual_le_futureCacheCharge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledLiveNonSecretResidual adversary q fuel ≤ sampledRetainedFutureCacheCharge adversary q := by
  unfold sampledLiveNonSecretResidual sampledRetainedFutureCacheCharge
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
      apply mul_le_mul' le_rfl
      exact probEvent_liveNonSecretResidual_le_futureCacheCharge adversary q hq hqMax parameter hp table
        (curryFtsTableEquiv ftsSecret) hfts fuel
    · rw [probOutput_eq_zero_of_not_mem_support hfts, zero_mul, zero_mul]
  · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]

theorem forgeAdvantage_add_messageReserves_le_futureCacheCharge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1)) *
        (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + sampledRetainedFutureCacheCharge adversary q :=
  (forgeAdvantage_add_messageReserves_le_joint_beforeFailureBudget_live adversary q hq hqMax).trans
    (add_le_add le_rfl (sampledLiveNonSecretResidual_le_futureCacheCharge adversary q hq hqMax (q + 1)))

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
