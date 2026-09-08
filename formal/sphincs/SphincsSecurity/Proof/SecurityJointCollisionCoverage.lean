import SphincsSecurity.Proof.CollisionCoveragePotential
import SphincsSecurity.Proof.InitializedRemainingCoverage

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex retainedRestVerdict)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def retainedJointCollisionCoveragePotential
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (cap : Nat)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool) : ENNReal :=
  match result.1.2.1.1 with
  | none => 0
  | some value => jointCollisionCoveragePotential (secretKey parameter value.1 otsTable ftsTable) cap 0
      (result.1.2.1.2, value.2.1.2) result.1.2.2 result.2

theorem retainedJointCollisionCoveragePotential_le_one
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (cap : Nat)
    (result) : retainedJointCollisionCoveragePotential parameter otsTable ftsTable cap result ≤ 1 := by
  unfold retainedJointCollisionCoveragePotential
  split
  · exact zero_le
  · exact jointCollisionCoveragePotential_le_one _ _ _ _ _ _

theorem retainedJointCollisionCoveragePotential_eq_one_of_win
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest) (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets)
    (fuel : Nat) (result)
    (hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel))
    (value : RetainedGameResult) (hv : result.1.2.1.1 = some value) (hwin : retainedRestVerdict value.2 = true) :
    retainedJointCollisionCoveragePotential parameter otsTable ftsTable q result = 1 := by
  rw [retainedJointCollisionCoveragePotential, hv]
  rcases retained_win_cases_live_residual adversary q hq parameter hp otsTable hots ftsTable hfts fuel result hr value hv hwin with hf | hs | hl
  · exact jointCollisionCoveragePotential_eq_one_of_stopped _ _ _ _ _ _ (by simp [hf])
  · rcases hs.2 with hh | hb
    · exact jointCollisionCoveragePotential_eq_one_of_stopped _ _ _ _ _ _ (by simp [hh])
    · exact jointCollisionCoveragePotential_eq_one_of_bad _ _ _ _
        (runRetainedWithFailure_cache_finite _ adversary parameter otsTable ftsTable q fuel result hr) _ _ hb
  · obtain ⟨covered, hc, hobserved⟩ := liveNonSecretResidual_observed adversary q hq parameter hp otsTable ftsTable hfts fuel result hr hl
    have he : covered = value := Option.some.inj (hc.symm.trans hv)
    subst covered
    have hvalid : SigningTranscript.Valid value.2.1.2 := by
      have h := hobserved.1
      simp only [retainedRestVerdict, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1
    exact jointCollisionCoveragePotential_eq_one_of_covered _ _ _ _ _ _ hvalid
      (observedFewTimeCover_signingCacheCovered parameter value.1 _ _ _ hobserved.2)

theorem probEvent_original_win_le_jointCollisionCoverage
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest) (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[fun result => retainedRestVerdict result.1.1.2 = true | originalParentRecords adversary parameter otsTable ftsTable] ≤
      ∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] *
        retainedJointCollisionCoveragePotential parameter otsTable ftsTable q result := by
  rw [probEvent_originalRecords_eq_retained adversary q hq parameter hp otsTable ftsTable hfts fuel
    (fun result => retainedRestVerdict result.1.2 = true), probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel)
  · split_ifs with hwin
    · obtain ⟨value, hv, hwin⟩ := hwin
      rw [retainedJointCollisionCoveragePotential_eq_one_of_win adversary q hq parameter hp otsTable hots ftsTable hfts fuel result hr value hv hwin, mul_one]
    · exact zero_le
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]
    split_ifs <;> rfl

noncomputable def sampledJointCollisionCoverageRisk (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        ∑' result, Pr[= result | runRetainedWithFailure (parentException parameter table (curryFtsTableEquiv ftsSecret))
          adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel] *
          retainedJointCollisionCoveragePotential parameter table (curryFtsTableEquiv ftsSecret) q result

theorem forgeAdvantage_le_jointCollisionCoverage
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    forgeAdvantage scheme adversary ≤ sampledJointCollisionCoverageRisk adversary q fuel := by
  rw [forgeAdvantage_eq_sampledRetained_win, probEvent_sampledRetained_eq_recordRisk]
  unfold sampledOriginalRecordRisk sampledJointCollisionCoverageRisk
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hp : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro table
    by_cases ht : table ∈ support OtsProbeSimulation.sampleOtsHashTable
    · exact mul_le_mul' le_rfl (probEvent_original_win_le_jointCollisionCoverage adversary q hq parameter hp table ht
        (curryFtsTableEquiv ftsSecret) (mem_support_sampleFtsSecrets ftsSecret) fuel)
    · rw [probOutput_eq_zero_of_not_mem_support ht, zero_mul, zero_mul]
  · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
