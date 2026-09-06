import SphincsSecurity.Proof.JointProbeCompletionSplit
import SphincsSecurity.Proof.JointProbeRetainedCost

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation
attribute [local instance] Classical.propDecidable

noncomputable def sampledNativeFtsOtsFailureRisk (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' otsTable, Pr[= otsTable | sampleOtsHashTable] *
        Pr[fun result => result = none | FtsProbeSimulation.nativeFtsRetainedResolved adversary parameter otsTable
          (fun coordinate => ftsSecret coordinate.1 coordinate.2.1 coordinate.2.2) q fuel >>= finishResolvedRun]

theorem sampledNativeFtsCompletionRisk_le_ots_add_fts_hit
    (adversary : Adversary) (q fuel : Nat) :
    sampledNativeFtsCompletionRisk adversary q fuel ≤
      sampledNativeFtsOtsFailureRisk adversary q fuel + sampledJointRetainedFtsHitRisk adversary q := by
  unfold sampledNativeFtsCompletionRisk sampledNativeFtsOtsFailureRisk sampledJointRetainedFtsHitRisk
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro parameter
  rw [← mul_add, ← ENNReal.tsum_add]
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  rw [← mul_add]
  exact mul_le_mul' le_rfl (FtsProbeSimulation.probEvent_sampled_nativeFts_completion_le_ots_add_fts_hit
    adversary parameter (fun coordinate => ftsSecret coordinate.1 coordinate.2.1 coordinate.2.2) q fuel)

theorem forgeAdvantage_le_nativeFts_ots_add_fts_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      (sampledNativeFtsOtsFailureRisk adversary q fuel + sampledJointRetainedFtsHitRisk adversary q) +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) :=
  (forgeAdvantage_le_jointResolved_completion_remaining127 adversary q hqPos hq hqMax fuel).trans
    (add_le_add (add_le_add le_rfl (sampledNativeFtsCompletionRisk_le_ots_add_fts_hit adversary q fuel)) le_rfl)

end SphincsSecurity.Concrete
