import SphincsSecurity.Proof.StoppedRemainingCoverage
import SphincsSecurity.Proof.CachedTargetCoverage
import SphincsSecurity.Proof.TargetIndexEnvelope127

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem one_le_cappedRemainingCachedTargetEnvelope_scaled_of_covered (key : SecretKey) (cap budget : Nat) (state : CoverLogState)
    (hvalid : SigningTranscript.Valid state.2) (hcover : SigningCacheCovered key.parameter key.root state.1 state.2) :
    1 ≤ cappedRemainingCachedTargetEnvelope key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ := by
  obtain ⟨input, output, hmessage, houtput, hadmissible, hcovered⟩ := hcover
  have hrow := normalizedTargetLogProduct_full_ge_of_covered key state (payloadOf input) (hashOutputFewTimeView output) hcovered
  have hmoment : ((2 ^ 140 : Nat) : ENNReal) ≤ targetShapeMoments key state.1 state.2 (payloadOf input) (hashOutputFewTimeView output) ∅ Finset.univ := by
    simpa only [targetShapeMoments, Finset.prod_empty, one_mul] using hrow
  have hentry : ((2 ^ 140 : Nat) : ENNReal) ≤ cacheMessageEntryWeight key.parameter
      (fun query target => remainingTargetEnvelope key cap budget (payloadOf query) target (signatureLimit - state.2.length) state ∅ Finset.univ) state.1 input := by
    simp only [cacheMessageEntryWeight, houtput, hmessage, hadmissible, and_self, if_true]
    exact hmoment.trans (le_targetShapeEnvelope _ _ _ _ _ _ ∅ Finset.univ)
  have htotal : ((2 ^ 140 : Nat) : ENNReal) ≤ cappedRemainingCachedTargetEnvelope key cap budget state ∅ Finset.univ := by
    rw [cappedRemainingCachedTargetEnvelope, if_pos hvalid]
    exact hentry.trans (ENNReal.le_tsum input)
  have hpositive : ((2 ^ 140 : Nat) : ENNReal) ≠ 0 := by norm_num
  have hfinite : ((2 ^ 140 : Nat) : ENNReal) ≠ ∞ := by finiteness
  rw [← ENNReal.mul_inv_cancel hpositive hfinite]
  exact mul_le_mul' htotal le_rfl

theorem remainingCoveragePotential_initial_scaled (key : SecretKey) (q : Nat) (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    remainingCoveragePotential key q q (cache, []) ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ =
      (q : ENNReal) * initialRawIndexRate q := by
  have hzero : cappedRemainingCachedTargetEnvelope key q q (cache, []) ∅ Finset.univ = 0 := by
    rw [cappedRemainingCachedTargetEnvelope, if_pos (show SigningTranscript.Valid [] from Nat.zero_le _), remainingCachedTargetEnvelope]
    exact cacheMessageWeight_of_no_message key.parameter _ cache hnone
  have hraw : cappedRemainingRawIndexEnvelope key q q (cache, []) ∅ Finset.univ = cappedRawIndexCacheEnvelope key q (cache, []) ∅ Finset.univ := by
    simp only [cappedRemainingRawIndexEnvelope, cappedRawIndexCacheEnvelope, rawIndexCacheEnvelope,
      messageCacheSlotCount_initial key.parameter q cache hnone]
    rfl
  have hrate : (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
      ((2 ^ 140 : Nat) : ENNReal)⁻¹ = ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
    norm_num [Index, totalHeight, ftsTreeHeight, ← ENNReal.mul_inv]
  rw [remainingCoveragePotential, hzero, zero_add, hraw, mul_assoc, hrate,
    mul_comm (cappedRawIndexCacheEnvelope _ _ _ _ _), mul_assoc, cappedRawIndexCacheEnvelope_initial_scaled key q cache hnone]

namespace FtsProbeSimulation.JointOriginal

open OtsProbeSimulation (OtsSecretIndex)

theorem probEvent_runWithFailure_liveCover_add_remainingUnused_le_initial
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => result.1.2.2 = false ∧ result.2 = false ∧ SigningTranscript.Valid result.1.2.1.1.2 ∧
      SigningCacheCovered parameter root result.1.2.1.2 result.1.2.1.1.2 |
      runWithFailure exception parameter root otsTable ftsTable (withSigningLog computation []) frame cache hit failed] +
      expectedRemainingUnusedCoverageCharge exception parameter root otsTable ftsTable q ∅ Finset.univ
        computation q frame (cache, []) hit failed * ((2 ^ 140 : Nat) : ENNReal)⁻¹ ≤
      (q : ENNReal) * initialRawIndexRate q := by
  let key := secretKey parameter root otsTable ftsTable
  have hsigned : SigningDigestsCached parameter cache root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hvalid : TargetShapeValid ∅ Finset.univ := by constructor <;> simp
  have h := expected_runWithFailure_remainingTarget_add_unused_le exception parameter root otsTable ftsTable q q hq computation
    frame (cache, []) hit failed hbound hsigned hcache ∅ Finset.univ hvalid
  have hsurvive : survivingLogPotential (fun current => remainingCoveragePotential key q q current ∅ Finset.univ) (cache, []) hit failed ≤
      remainingCoveragePotential key q q (cache, []) ∅ Finset.univ := by
    unfold survivingLogPotential
    split_ifs
    · exact zero_le
    · exact le_rfl
  have hscaled := mul_le_mul' (h.trans hsurvive) (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹))
  rw [add_mul, remainingCoveragePotential_initial_scaled key q cache hnone] at hscaled
  apply le_trans ?_ hscaled
  apply add_le_add ?_ le_rfl
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro result
  split_ifs with hcover
  · rw [mul_assoc, survivingLogPotential, hcover.1, hcover.2.1]
    simp only [Bool.false_or, Bool.false_eq_true, if_false]
    exact le_mul_of_one_le_right' (one_le_cappedRemainingCachedTargetEnvelope_scaled_of_covered key q 0
      (result.1.2.1.2, result.1.2.1.1.2) hcover.2.2.1 hcover.2.2.2)
  · exact bot_le

end FtsProbeSimulation.JointOriginal

end SphincsSecurity.Concrete
