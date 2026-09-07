import SphincsSecurity.Proof.AdaptiveStoppedTarget
import SphincsSecurity.Proof.CachedTargetCoverage

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_runWithFailure_target_full_add_unused_scaled_le_127
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | runWithFailure exception parameter root otsTable ftsTable
        (withSigningLog computation []) frame cache hit failed] *
      survivingLogPotential (fun current => cappedCachedTargetEnvelope (secretKey parameter root otsTable ftsTable) q current ∅ Finset.univ)
        (result.1.2.1.2, result.1.2.1.1.2) result.1.2.2 result.2) * ((2 ^ 140 : Nat) : ENNReal)⁻¹ +
      expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (unusedTargetHashCost parameter)
        ∅ Finset.univ computation frame (cache, []) hit failed * ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≤
      (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  let key := secretKey parameter root otsTable ftsTable
  have hsigned : SigningDigestsCached parameter cache root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hvalid : TargetShapeValid ∅ Finset.univ := by constructor <;> simp
  have hinitial : cappedCachedTargetEnvelope key q (cache, []) ∅ Finset.univ = 0 := by
    rw [cappedCachedTargetEnvelope, if_pos (show SigningTranscript.Valid [] from Nat.zero_le _), cachedTargetEnvelope]
    exact cacheMessageWeight_of_no_message parameter _ cache hnone
  have h := expected_runWithFailure_target_add_unused_le exception parameter root otsTable ftsTable q hq computation frame
    (cache, []) hit failed hsigned hbudget ∅ Finset.univ hvalid
  have hzero : survivingLogPotential (fun current => cappedCachedTargetEnvelope key q current ∅ Finset.univ) (cache, []) hit failed = 0 := by
    simp [survivingLogPotential, hinitial]
  rw [hzero, zero_add] at h
  have hrate : (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
      ((2 ^ 140 : Nat) : ENNReal)⁻¹ = ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
    norm_num [Index, totalHeight, ftsTreeHeight, ← ENNReal.mul_inv]
  have hscaled := mul_le_mul' h (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹))
  rw [add_mul, mul_right_comm _ (expectedStoppedIndexCharge _ _ _ _ _ _ (unusedTargetHashCost _) _ _ _ _ _ _ _), hrate,
    mul_right_comm _ (expectedStoppedIndexCharge _ _ _ _ _ _ (fun _ => signingMacroHashCost) _ _ _ _ _ _ _), hrate] at hscaled
  have hmacro := expectedStoppedIndexCharge_le_unstopped exception parameter root otsTable ftsTable q (fun _ => signingMacroHashCost)
    ∅ Finset.univ computation frame (cache, []) hit failed
  rw [expectedWeightedIndexCharge_macro_eq] at hmacro
  apply le_trans ?_ ((mul_le_mul' hmacro (le_refl (((2 ^ 176 : Nat) : ENNReal)⁻¹))).trans
    (expectedMacroIndexCharge_full_scaled_le_127 key q hq computation hbound cache hnone hbudget))
  simpa only [mul_comm] using hscaled

theorem probEvent_runWithFailure_liveCover_add_unused_le_127
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => result.1.2.2 = false ∧ result.2 = false ∧ SigningTranscript.Valid result.1.2.1.1.2 ∧
      SigningCacheCovered parameter root result.1.2.1.2 result.1.2.1.1.2 |
      runWithFailure exception parameter root otsTable ftsTable (withSigningLog computation []) frame cache hit failed] +
      expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (unusedTargetHashCost parameter)
        ∅ Finset.univ computation frame (cache, []) hit failed * ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≤
      (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  apply le_trans ?_ (expected_runWithFailure_target_full_add_unused_scaled_le_127 exception parameter root otsTable ftsTable q hq
    computation hbound frame cache hit failed hnone hbudget)
  apply add_le_add _ le_rfl
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro result
  split_ifs with hcover
  · rw [mul_assoc, survivingLogPotential, hcover.1, hcover.2.1]
    simp only [Bool.false_or, Bool.false_eq_true, if_false]
    exact le_mul_of_one_le_right' (one_le_cappedCachedTargetEnvelope_scaled_of_covered (secretKey parameter root otsTable ftsTable) q
      (result.1.2.1.2, result.1.2.1.1.2) hcover.2.2.1 hcover.2.2.2)
  · exact bot_le

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
