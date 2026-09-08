import SphincsSecurity.Proof.AdaptiveNearUniformCoverage
import SphincsSecurity.Proof.InitialNearUniformRaw
import SphincsSecurity.Proof.CachedTargetCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

theorem one_le_cappedReuseCachedTargetEnvelope_scaled_of_covered (key : SecretKey) (reuse : ENNReal) (budget : Nat) (state : CoverLogState)
    (hvalid : SigningTranscript.Valid state.2) (hcover : SigningCacheCovered key.parameter key.root state.1 state.2) :
    1 ≤ cappedReuseCachedTargetEnvelope key reuse budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ := by
  obtain ⟨input, output, hmessage, houtput, hadmissible, hcovered⟩ := hcover
  have hrow := normalizedTargetLogProduct_full_ge_of_covered key state (payloadOf input) (hashOutputFewTimeView output) hcovered
  have hmoment : ((2 ^ 140 : Nat) : ENNReal) ≤ targetShapeMoments key state.1 state.2 (payloadOf input) (hashOutputFewTimeView output) ∅ Finset.univ := by
    simpa only [targetShapeMoments, Finset.prod_empty, one_mul] using hrow
  have hentry : ((2 ^ 140 : Nat) : ENNReal) ≤ cacheMessageEntryWeight key.parameter
      (fun query target => reuseTargetEnvelope key reuse budget (payloadOf query) target (signatureLimit - state.2.length) state ∅ Finset.univ) state.1 input := by
    simp only [cacheMessageEntryWeight, houtput, hmessage, hadmissible, and_self, if_true]
    exact hmoment.trans (le_targetShapeEnvelope _ _ _ _ _ _ ∅ Finset.univ)
  have htotal : ((2 ^ 140 : Nat) : ENNReal) ≤ cappedReuseCachedTargetEnvelope key reuse budget state ∅ Finset.univ := by
    rw [cappedReuseCachedTargetEnvelope, if_pos hvalid]
    exact hentry.trans (ENNReal.le_tsum input)
  have hpositive : ((2 ^ 140 : Nat) : ENNReal) ≠ 0 := by norm_num
  have hfinite : ((2 ^ 140 : Nat) : ENNReal) ≠ ∞ := by finiteness
  rw [← ENNReal.mul_inv_cancel hpositive hfinite]
  exact mul_le_mul' htotal le_rfl

noncomputable def initialNearUniformRawIndexRate (q : Nat) : ENNReal :=
  targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ nearUniformDigestReuseWeight
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) q signatureLimit
    initialTargetIndexVector 0 14 * ((2 ^ 176 : Nat) : ENNReal)⁻¹

theorem nearUniformCoveragePotential_initial_scaled (key : SecretKey) (q : Nat) (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    reuseCoveragePotential key nearUniformDigestReuseWeight q (cache, []) ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ =
      (q : ENNReal) * initialNearUniformRawIndexRate q := by
  have hzero : cappedReuseCachedTargetEnvelope key nearUniformDigestReuseWeight q (cache, []) ∅ Finset.univ = 0 := by
    rw [cappedReuseCachedTargetEnvelope, if_pos (show SigningTranscript.Valid [] from Nat.zero_le _), reuseCachedTargetEnvelope]
    exact cacheMessageWeight_of_no_message key.parameter _ cache hnone
  have hvalid : TargetShapeValid ∅ Finset.univ := by constructor <;> simp
  have hcard : (Finset.univ : Finset FtsTree).card = 14 := by norm_num [FtsTree, ftsTrees]
  have hraw : cappedReuseRawEnvelope key nearUniformDigestReuseWeight q (cache, []) ∅ Finset.univ =
      targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ nearUniformDigestReuseWeight
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) q signatureLimit
        initialTargetIndexVector 0 14 := by
    simp only [cappedReuseRawEnvelope, if_pos (show SigningTranscript.Valid [] from Nat.zero_le _),
      List.length_nil, Nat.sub_zero]
    rw [reuseRawEnvelope_initial key nearUniformDigestReuseWeight q signatureLimit cache hnone ∅ Finset.univ hvalid,
      Finset.card_empty, hcard]
  have hrate : (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
      ((2 ^ 140 : Nat) : ENNReal)⁻¹ = ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
    norm_num [Index, totalHeight, ftsTreeHeight, ← ENNReal.mul_inv]
  rw [reuseCoveragePotential, hzero, zero_add, mul_assoc, hrate,
    mul_comm (cappedReuseRawEnvelope _ _ _ _ _ _), mul_assoc, hraw]
  rfl

namespace FtsProbeSimulation.JointOriginal

open OtsProbeSimulation (OtsSecretIndex)

theorem probEvent_runWithFailure_liveCover_add_nearUniformUnused_le_initial
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hdetect : ∀ cache input answer,
      MessageDeficitExceptional (secretKey parameter root otsTable ftsTable) (cache.cacheQuery input answer) →
        exception cache input answer)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => result.1.2.2 = false ∧ result.2 = false ∧ SigningTranscript.Valid result.1.2.1.1.2 ∧
      SigningCacheCovered parameter root result.1.2.1.2 result.1.2.1.1.2 |
      runWithFailure exception parameter root otsTable ftsTable (withSigningLog computation []) frame cache hit failed] +
      expectedReuseUnusedCoverageCharge exception parameter root otsTable ftsTable nearUniformDigestReuseWeight ∅ Finset.univ
        computation q frame (cache, []) hit failed * ((2 ^ 140 : Nat) : ENNReal)⁻¹ ≤
      (q : ENNReal) * initialNearUniformRawIndexRate q := by
  let key := secretKey parameter root otsTable ftsTable
  have hsigned : SigningDigestsCached parameter cache root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hvalid : TargetShapeValid ∅ Finset.univ := by constructor <;> simp
  have h := expected_runWithFailure_nearUniformTarget_add_unused_le exception parameter root otsTable ftsTable hdetect q q hq computation
    frame (cache, []) hit failed hbound hsigned hcache
    (fun _ => messageDeficitExceptional_not_of_no_inputs key cache (fun payload => hnone _ ⟨payload, rfl⟩)) ∅ Finset.univ hvalid
  have hsurvive : survivingLogPotential (fun current => reuseCoveragePotential key nearUniformDigestReuseWeight q current ∅ Finset.univ) (cache, []) hit failed ≤
      reuseCoveragePotential key nearUniformDigestReuseWeight q (cache, []) ∅ Finset.univ := by
    unfold survivingLogPotential
    split_ifs
    · exact zero_le
    · exact le_rfl
  have hscaled := mul_le_mul' (h.trans hsurvive) (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹))
  rw [add_mul, nearUniformCoveragePotential_initial_scaled key q cache hnone] at hscaled
  apply le_trans ?_ hscaled
  apply add_le_add ?_ le_rfl
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro result
  split_ifs with hcover
  · rw [mul_assoc, survivingLogPotential, hcover.1, hcover.2.1]
    simp only [Bool.false_or, Bool.false_eq_true, if_false]
    exact le_mul_of_one_le_right' (one_le_cappedReuseCachedTargetEnvelope_scaled_of_covered key nearUniformDigestReuseWeight 0
      (result.1.2.1.2, result.1.2.1.1.2) hcover.2.2.1 hcover.2.2.2)
  · exact bot_le

theorem probEvent_runWithFailure_deficitStopped_liveCover_add_unused_le_initial
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
      runWithFailure (deficitStoppingException (secretKey parameter root otsTable ftsTable) exception) parameter root otsTable ftsTable (withSigningLog computation []) frame cache hit failed] +
      expectedReuseUnusedCoverageCharge (deficitStoppingException (secretKey parameter root otsTable ftsTable) exception)
        parameter root otsTable ftsTable nearUniformDigestReuseWeight ∅ Finset.univ
        computation q frame (cache, []) hit failed * ((2 ^ 140 : Nat) : ENNReal)⁻¹ ≤
      (q : ENNReal) * initialNearUniformRawIndexRate q :=
  probEvent_runWithFailure_liveCover_add_nearUniformUnused_le_initial _ parameter root otsTable ftsTable
    (fun _ _ _ h => Or.inr h) q hq computation hbound frame cache hit failed hnone hcache

end FtsProbeSimulation.JointOriginal

end SphincsSecurity.Concrete
