import SphincsSecurity.Proof.CompletedCollisionCoverage
import SphincsSecurity.Proof.SecurityJointCollisionCoverageBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex retainedRestVerdict)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def retainedJointCollisionCoverageCompletionCredit
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (cap : Nat)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool) : ENNReal :=
  match result.1.2.1.1 with
  | none => 0
  | some value => jointCollisionCoverageCompletionCredit (secretKey parameter value.1 otsTable ftsTable) cap
      (result.1.2.1.2, value.2.1.2) result.1.2.2 result.2

theorem retainedJointCollisionCoverageCompletionCredit_le_potential
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (cap : Nat) (result) :
    retainedJointCollisionCoverageCompletionCredit parameter otsTable ftsTable cap result ≤
      retainedJointCollisionCoveragePotential parameter otsTable ftsTable cap result := by
  unfold retainedJointCollisionCoverageCompletionCredit retainedJointCollisionCoveragePotential
  cases result.1.2.1.1 with
  | none => exact le_rfl
  | some value => exact jointCollisionCoverageCompletionCredit_le_potential _ _ _ _ _

theorem completedJointCollisionCoveragePotential_eq_one_of_win
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest) (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets)
    (fuel : Nat) (result)
    (hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel))
    (value : RetainedGameResult) (hv : result.1.2.1.1 = some value) (hwin : retainedRestVerdict value.2 = true) :
    completedJointCollisionCoveragePotential (secretKey parameter value.1 otsTable ftsTable)
      (result.1.2.1.2, value.2.1.2) result.1.2.2 result.2 = 1 := by
  rcases retained_win_cases_live_residual adversary q hq parameter hp otsTable hots ftsTable hfts fuel result hr value hv hwin with hf | hs | hl
  · exact completedJointCollisionCoveragePotential_eq_one_of_stopped _ _ _ _ (by simp [hf])
  · rcases hs.2 with hh | hb
    · exact completedJointCollisionCoveragePotential_eq_one_of_stopped _ _ _ _ (by simp [hh])
    · exact completedJointCollisionCoveragePotential_eq_one_of_bad _ _
        (runRetainedWithFailure_cache_finite _ adversary parameter otsTable ftsTable q fuel result hr) _ _ hb
  · obtain ⟨covered, hc, hobserved⟩ := liveNonSecretResidual_observed adversary q hq parameter hp otsTable ftsTable hfts fuel result hr hl
    have he : covered = value := Option.some.inj (hc.symm.trans hv)
    subst covered
    have hvalid : SigningTranscript.Valid value.2.1.2 := by
      have h := hobserved.1
      simp only [retainedRestVerdict, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1
    exact completedJointCollisionCoveragePotential_eq_one_of_covered _ _ _ _ hvalid
      (observedFewTimeCover_signingCacheCovered parameter value.1 _ _ _ hobserved.2)

theorem probEvent_original_win_add_completionCredit_le_jointCollisionCoverage
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest) (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[fun result => retainedRestVerdict result.1.1.2 = true | originalParentRecords adversary parameter otsTable ftsTable] +
      (∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] *
        retainedJointCollisionCoverageCompletionCredit parameter otsTable ftsTable q result) ≤
      ∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] *
        retainedJointCollisionCoveragePotential parameter otsTable ftsTable q result := by
  rw [probEvent_originalRecords_eq_retained adversary q hq parameter hp otsTable ftsTable hfts fuel
    (fun result => retainedRestVerdict result.1.2 = true), probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel)
  · split_ifs with hwin
    · obtain ⟨value, hv, hwin⟩ := hwin
      have hcompleted := completedJointCollisionCoveragePotential_eq_one_of_win adversary q hq parameter hp otsTable hots ftsTable hfts fuel result hr value hv hwin
      have hcredit := completedJointCollisionCoverage_add_credit (secretKey parameter value.1 otsTable ftsTable) q
        (result.1.2.1.2, value.2.1.2) result.1.2.2 result.2
      rw [hcompleted] at hcredit
      rw [retainedJointCollisionCoverageCompletionCredit, retainedJointCollisionCoveragePotential, hv]
      simpa only [mul_add, mul_one] using (congrArg (fun amount : ENNReal =>
        Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] * amount) hcredit).le
    · simp only [zero_add]
      exact mul_le_mul' le_rfl (retainedJointCollisionCoverageCompletionCredit_le_potential parameter otsTable ftsTable q result)
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    split_ifs <;> simp

noncomputable def sampledJointCollisionCoverageCompletionCredit (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        ∑' result, Pr[= result | runRetainedWithFailure (parentException parameter table (curryFtsTableEquiv ftsSecret))
          adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel] *
          retainedJointCollisionCoverageCompletionCredit parameter table (curryFtsTableEquiv ftsSecret) q result

private theorem expected_add_le (computation : ProbComp α) (left credit risk : α → ENNReal)
    (h : ∀ result ∈ support computation, left result + credit result ≤ risk result) :
    (∑' result, Pr[= result | computation] * left result) + (∑' result, Pr[= result | computation] * credit result) ≤
      ∑' result, Pr[= result | computation] * risk result := by
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [← mul_add]
  by_cases hr : result ∈ support computation
  · exact mul_le_mul' le_rfl (h result hr)
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

theorem forgeAdvantage_add_completionCredit_le_jointCollisionCoverage
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    forgeAdvantage scheme adversary + sampledJointCollisionCoverageCompletionCredit adversary q fuel ≤
      sampledJointCollisionCoverageRisk adversary q fuel := by
  rw [forgeAdvantage_eq_sampledRetained_win, probEvent_sampledRetained_eq_recordRisk]
  unfold sampledOriginalRecordRisk sampledJointCollisionCoverageCompletionCredit sampledJointCollisionCoverageRisk
  apply expected_add_le
  intro parameter hp
  apply expected_add_le
  intro ftsSecret _
  apply expected_add_le
  intro table ht
  exact probEvent_original_win_add_completionCredit_le_jointCollisionCoverage adversary q hq parameter hp table ht
    (curryFtsTableEquiv ftsSecret) (mem_support_sampleFtsSecrets ftsSecret) fuel

theorem forgeAdvantage_add_jointCollisionCoverage_completionCredits_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    forgeAdvantage scheme adversary + sampledJointCollisionCoverageCompletionCredit adversary q fuel +
      sampledJointCollisionCoverageCredit adversary q fuel ≤
      min 1 ((q : ENNReal) * initialRawIndexRate q) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
        sampledJointCollisionCoverageCharge adversary q fuel :=
  (add_le_add (forgeAdvantage_add_completionCredit_le_jointCollisionCoverage adversary q hq fuel) le_rfl).trans
    (sampledJointCollisionCoverageRisk_add_credit_le adversary q hq hqMax fuel)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
