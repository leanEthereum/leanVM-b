import SphincsSecurity.Proof.JointTerminalParentRefund
import SphincsSecurity.Proof.SecurityOverlapParentRefund

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex retainedRestVerdict)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

theorem terminalJointParentCredit_eq_zero_of_win
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest) (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets)
    (fuel : Nat) (result)
    (hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel))
    (value : RetainedGameResult) (hv : result.1.2.1.1 = some value) (hwin : retainedRestVerdict value.2 = true) :
    terminalJointParentCredit parameter otsTable ftsTable result = 0 := by
  rw [terminalJointParentCredit, hv]
  rcases retained_win_cases_live_residual adversary q hq parameter hp otsTable hots ftsTable hfts fuel result hr value hv hwin with hf | hs | hl
  · rw [terminalPendingParentCount_eq_zero_of_stopped parameter otsTable ftsTable result (by simp [hf])]
    simp
  · rw [terminalPendingParentCount_eq_zero_of_structural parameter otsTable ftsTable result hs]
    simp
  · obtain ⟨covered, hc, hobserved⟩ := liveNonSecretResidual_observed adversary q hq parameter hp otsTable ftsTable hfts fuel result hr hl
    have he : covered = value := Option.some.inj (hc.symm.trans hv)
    subst covered
    have hvalid : SigningTranscript.Valid value.2.1.2 := by
      have h := hobserved.1
      simp only [retainedRestVerdict, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1
    have hcovered := one_le_completedCoveragePotential_scaled_of_covered (secretKey parameter value.1 otsTable ftsTable)
      (result.1.2.1.2, value.2.1.2) hvalid (observedFewTimeCover_signingCacheCovered parameter value.1 _ _ _ hobserved.2)
    simp only [boundedCompletedCoveragePotential, min_eq_left hcovered, tsub_self, zero_mul]

theorem retained_completion_add_parentCredit_le_potential
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (cap : Nat) (result)
    (hfinite : Finite result.1.2.1.2) (hcache : QueryCache.enncard result.1.2.1.2 ≤ (2 ^ 127 : Nat)) :
    retainedJointCollisionCoverageCompletionCredit parameter otsTable ftsTable cap result + terminalJointParentCredit parameter otsTable ftsTable result ≤
      retainedJointCollisionCoveragePotential parameter otsTable ftsTable cap result := by
  cases hv : result.1.2.1.1 with
  | none => simp only [retainedJointCollisionCoverageCompletionCredit, terminalJointParentCredit, retainedJointCollisionCoveragePotential, hv, add_zero, le_refl]
  | some value =>
      rw [retainedJointCollisionCoverageCompletionCredit, retainedJointCollisionCoveragePotential, hv]
      apply (add_le_add le_rfl (terminalJointParentCredit_le_completed_potential parameter otsTable ftsTable result hfinite hcache value hv)).trans_eq
      rw [add_comm, completedJointCollisionCoverage_add_credit]

theorem probEvent_original_win_add_completion_parentCredits_le_jointCollisionCoverage
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest) (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[fun result => retainedRestVerdict result.1.1.2 = true | originalParentRecords adversary parameter otsTable ftsTable] +
      (∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] *
        retainedJointCollisionCoverageCompletionCredit parameter otsTable ftsTable q result) +
      (∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] *
        terminalJointParentCredit parameter otsTable ftsTable result) ≤
      ∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] *
        retainedJointCollisionCoveragePotential parameter otsTable ftsTable q result := by
  rw [probEvent_originalRecords_eq_retained adversary q hq parameter hp otsTable ftsTable hfts fuel
    (fun result => retainedRestVerdict result.1.2 = true), probEvent_eq_tsum_ite, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel)
  · split_ifs with hwin
    · obtain ⟨value, hv, hwin⟩ := hwin
      rw [terminalJointParentCredit_eq_zero_of_win adversary q hq parameter hp otsTable hots ftsTable hfts fuel result hr value hv hwin, mul_zero, add_zero]
      have hcompleted := completedJointCollisionCoveragePotential_eq_one_of_win adversary q hq parameter hp otsTable hots ftsTable hfts fuel result hr value hv hwin
      have hcredit := completedJointCollisionCoverage_add_credit (secretKey parameter value.1 otsTable ftsTable) q
        (result.1.2.1.2, value.2.1.2) result.1.2.2 result.2
      rw [hcompleted] at hcredit
      rw [retainedJointCollisionCoverageCompletionCredit, retainedJointCollisionCoveragePotential, hv]
      simpa only [mul_add, mul_one] using (congrArg (fun amount : ENNReal =>
        Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] * amount) hcredit).le
    · rw [zero_add, ← mul_add]
      exact mul_le_mul' le_rfl (retained_completion_add_parentCredit_le_potential parameter otsTable ftsTable q result
        (runRetainedWithFailure_cache_finite _ adversary parameter otsTable ftsTable q fuel result hr)
        ((runRetainedWithFailure_cache_le_queryBound _ adversary q hq parameter hp otsTable ftsTable hfts fuel result hr).trans (Nat.cast_le.mpr hqMax)))
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul, zero_mul]
    split_ifs <;> simp

noncomputable def sampledJointTerminalParentCredit (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        ∑' result, Pr[= result | runRetainedWithFailure (parentException parameter table (curryFtsTableEquiv ftsSecret))
          adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel] *
          terminalJointParentCredit parameter table (curryFtsTableEquiv ftsSecret) result

noncomputable def sampledTerminalParentCoverageOverlap (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        ∑' result, Pr[= result | runRetainedWithFailure (parentException parameter table (curryFtsTableEquiv ftsSecret))
          adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel] *
          terminalParentCoverageOverlap parameter table (curryFtsTableEquiv ftsSecret) result

theorem sampledJointTerminalParentCredit_add_overlap (adversary : Adversary) (q fuel : Nat) :
    sampledJointTerminalParentCredit adversary q fuel + sampledTerminalParentCoverageOverlap adversary q fuel =
      sampledPendingParentCount adversary q fuel * (2 * (Fintype.card Digest : ENNReal)⁻¹) := by
  unfold sampledJointTerminalParentCredit sampledTerminalParentCoverageOverlap sampledPendingParentCount initializedPendingParentCount
  simp only [← ENNReal.tsum_mul_right, mul_assoc, ← ENNReal.tsum_add, ← mul_add, terminalJointParentCredit_add_overlap]

private theorem expected_three_le (computation : ProbComp α) (first second third bound : α → ENNReal)
    (h : ∀ result ∈ support computation, first result + second result + third result ≤ bound result) :
    (∑' result, Pr[= result | computation] * first result) + (∑' result, Pr[= result | computation] * second result) +
      (∑' result, Pr[= result | computation] * third result) ≤ ∑' result, Pr[= result | computation] * bound result := by
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [← mul_add, ← mul_add]
  by_cases hr : result ∈ support computation
  · exact mul_le_mul' le_rfl (h result hr)
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

theorem forgeAdvantage_add_completion_parentCredits_le_jointCollisionCoverage
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    forgeAdvantage scheme adversary + sampledJointCollisionCoverageCompletionCredit adversary q fuel + sampledJointTerminalParentCredit adversary q fuel ≤
      sampledJointCollisionCoverageRisk adversary q fuel := by
  rw [forgeAdvantage_eq_sampledRetained_win, probEvent_sampledRetained_eq_recordRisk]
  unfold sampledOriginalRecordRisk sampledJointCollisionCoverageCompletionCredit sampledJointTerminalParentCredit sampledJointCollisionCoverageRisk
  apply expected_three_le
  intro parameter hp
  apply expected_three_le
  intro ftsSecret hfts
  apply expected_three_le
  intro table ht
  exact probEvent_original_win_add_completion_parentCredits_le_jointCollisionCoverage adversary q hq hqMax parameter hp table ht
    (curryFtsTableEquiv ftsSecret) hfts fuel

theorem forgeAdvantage_add_jointParentCredits_overlap_le_collisionEnvelope
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    forgeAdvantage scheme adversary + sampledJointCollisionCoverageCompletionCredit adversary q fuel + sampledJointTerminalParentCredit adversary q fuel +
      sampledJointCollisionCoverageCredit adversary q fuel + sampledJointCollisionCoverageOverlap adversary q fuel ≤
      min 1 ((q : ENNReal) * initialRawIndexRate q) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
        (sampledBeforeFailureCollisionCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ + sampledParentSharedFailureRisk adversary q fuel) := by
  have h := (add_le_add (forgeAdvantage_add_completion_parentCredits_le_jointCollisionCoverage adversary q hq hqMax fuel) le_rfl).trans
    (sampledJointCollisionCoverageRisk_add_credit_le adversary q hq hqMax fuel)
  have hsum := add_le_add h (le_refl (sampledJointCollisionCoverageOverlap adversary q fuel))
  rw [add_assoc _ (sampledJointCollisionCoverageCharge adversary q fuel)] at hsum
  exact hsum.trans (add_le_add le_rfl (sampledJointCollisionCoverageCharge_add_overlap_le adversary q hq fuel))

theorem forgeAdvantage_add_jointParentCredits_executionReserves_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + sampledJointCollisionCoverageCompletionCredit adversary q (q + 1) + sampledJointTerminalParentCredit adversary q (q + 1) +
      sampledJointCollisionCoverageCredit adversary q (q + 1) +
      (sampledSharedParentDiscard adversary q (q + 1) * (2 * (Fintype.card Digest : ENNReal)⁻¹) + sampledJointCoverageAfterParentRefund adversary q (q + 1)) +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledSigningNonEncodingReserve adversary q (q + 1) + sampledOuterEncodingReserve adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + sampledBeforeFailureEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
        (min 1 ((q : ENNReal) * initialRawIndexRate q) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) := by
  apply collisionFailureBound_add_message_signing_encodingReserves_le adversary q hqMax
  have h := (add_le_add le_rfl (sampled_sharedParentDiscard_add_remainder_le_overlap adversary q hq hqMax (q + 1))).trans
    (forgeAdvantage_add_jointParentCredits_overlap_le_collisionEnvelope adversary q hq hqMax (q + 1))
  simpa only [add_assoc, add_comm, add_left_comm] using h

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
