import SphincsSecurity.Proof.AdaptiveStoppedTarget
import SphincsSecurity.Proof.CachedTargetCoverage

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_runWithFailure_liveCover_le_stopped_arrival
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => result.1.2.2 = false ∧ result.2 = false ∧ SigningTranscript.Valid result.1.2.1.1.2 ∧
      SigningCacheCovered parameter root result.1.2.1.2 result.1.2.1.1.2 |
      runWithFailure exception parameter root otsTable ftsTable (withSigningLog computation []) frame cache hit failed] ≤
      expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (targetArrivalHashCost parameter)
        ∅ Finset.univ computation frame (cache, []) hit failed * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  let key := secretKey parameter root otsTable ftsTable
  have hsigned : SigningDigestsCached parameter cache root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hvalid : TargetShapeValid ∅ Finset.univ := by constructor <;> simp
  have hinitial : cappedCachedTargetEnvelope key q (cache, []) ∅ Finset.univ = 0 := by
    rw [cappedCachedTargetEnvelope, if_pos (show SigningTranscript.Valid [] from Nat.zero_le _), cachedTargetEnvelope]
    exact cacheMessageWeight_of_no_message parameter _ cache hnone
  have h := expected_runWithFailure_target_le_stopped_arrival exception parameter root otsTable ftsTable q hq computation frame
    (cache, []) hit failed hsigned hbudget ∅ Finset.univ hvalid
  have hzero : survivingLogPotential (fun current => cappedCachedTargetEnvelope key q current ∅ Finset.univ) (cache, []) hit failed = 0 := by
    simp [survivingLogPotential, hinitial]
  rw [hzero, zero_add] at h
  have hrate : (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
      ((2 ^ 140 : Nat) : ENNReal)⁻¹ = ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
    norm_num [Index, totalHeight, ftsTreeHeight, ← ENNReal.mul_inv]
  have hscaled := mul_le_mul' h (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹))
  rw [mul_right_comm _ (expectedStoppedIndexCharge _ _ _ _ _ _ _ _ _ _ _ _ _ _), hrate, mul_comm (((2 ^ 176 : Nat) : ENNReal)⁻¹)] at hscaled
  apply le_trans ?_ hscaled
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro result
  split_ifs with hcover
  · rw [mul_assoc, survivingLogPotential, hcover.1, hcover.2.1]
    simp only [Bool.false_or, Bool.false_eq_true, if_false]
    exact le_mul_of_one_le_right' (one_le_cappedCachedTargetEnvelope_scaled_of_covered key q
      (result.1.2.1.2, result.1.2.1.1.2) hcover.2.2.1 hcover.2.2.2)
  · exact bot_le

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
