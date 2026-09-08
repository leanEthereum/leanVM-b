import SphincsSecurity.Proof.SecurityRetiredCoverageRefund

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

def TerminalStructuralCoverageOverlap (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool) : Prop :=
  LiveSigningCacheCovered parameter result ∧ SurvivingStructuralFailure parameter otsTable ftsTable result

theorem terminalCollisionCoverageProduct_le_collisionReserve_add_overlap
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (result) :
    (if LiveSigningCacheCovered parameter result then 1 else 0) *
        min 1 (collisionStopPotential (secretKey parameter default otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) ≤
      collisionTerminalReserve parameter otsTable ftsTable result +
        (if TerminalStructuralCoverageOverlap parameter otsTable ftsTable result then 1 else 0) := by
  by_cases hc : LiveSigningCacheCovered parameter result
  · rw [if_pos hc, one_mul]
    by_cases hs : SurvivingStructuralFailure parameter otsTable ftsTable result
    · rw [if_pos ⟨hc, hs⟩]
      exact (min_le_left _ _).trans le_add_self
    · rw [if_neg (fun h => hs h.2), add_zero, collisionTerminalReserve, if_neg hs]
      simp only [collisionStopPotential, collisionSurvivingStructuralPotential, hc.1, hc.2.1, Bool.false_eq_true, if_false]
      exact min_le_right _ _
  · rw [if_neg hc, zero_mul]
    exact zero_le

theorem liveNonSecretResidual_not_structural
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result) (hres : LiveNonSecretResidual parameter otsTable ftsTable result) :
    ¬ SurvivingStructuralFailure parameter otsTable ftsTable result := by
  obtain ⟨_, hh, value, _, hclean⟩ := hres
  rintro ⟨_, hhit | hbad | hencoding⟩
  · simp [hh] at hhit
  · exact hclean.1.1.2.1 hbad
  · exact hclean.1.2 hencoding

theorem liveNonSecretResidual_cacheCovered
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat)
    (result) (hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable)
      adversary parameter otsTable ftsTable q fuel))
    (hres : LiveNonSecretResidual parameter otsTable ftsTable result) : LiveSigningCacheCovered parameter result := by
  obtain ⟨value, hvalue, hobserved⟩ :=
    liveNonSecretResidual_observed adversary q hq parameter hp otsTable ftsTable hfts fuel result hr hres
  have hvalid : SigningTranscript.Valid value.2.1.2 := by
    have hwin := hobserved.1
    simp only [OtsProbeSimulation.retainedRestVerdict, Bool.and_eq_true, decide_eq_true_eq] at hwin
    exact hwin.1.1
  exact ⟨hres.2.1, hres.1, value, hvalue, hvalid, observedFewTimeCover_signingCacheCovered _ _ _ _ _ hobserved.2⟩

theorem probEvent_liveResidual_add_structuralOverlap_le_cacheCover
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[LiveNonSecretResidual parameter otsTable ftsTable |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] +
      Pr[TerminalStructuralCoverageOverlap parameter otsTable ftsTable |
        runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] ≤
      Pr[LiveSigningCacheCovered parameter |
        runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] := by
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable)
      adversary parameter otsTable ftsTable q fuel)
  · by_cases hres : LiveNonSecretResidual parameter otsTable ftsTable result
    · have hc := liveNonSecretResidual_cacheCovered adversary q hq parameter hp otsTable ftsTable hfts fuel result hr hres
      have hn : ¬ TerminalStructuralCoverageOverlap parameter otsTable ftsTable result :=
        fun h => liveNonSecretResidual_not_structural parameter otsTable ftsTable result hres h.2
      simp only [if_pos hres, if_neg hn, if_pos hc, add_zero, le_refl]
    · rw [if_neg hres, zero_add]
      by_cases ho : TerminalStructuralCoverageOverlap parameter otsTable ftsTable result
      · rw [if_pos ho, if_pos ho.1]
      · rw [if_neg ho]
        exact zero_le
  · simp only [probOutput_eq_zero_of_not_mem_support hr, ite_self, zero_add, le_refl]

theorem probEvent_liveResidual_overlap_pairs_retiredRefund_le_reserved_add_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[LiveNonSecretResidual parameter otsTable ftsTable |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] +
      Pr[TerminalStructuralCoverageOverlap parameter otsTable ftsTable |
        runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] +
      initializedRetiredCoverageRefund adversary parameter otsTable ftsTable q fuel +
      initializedBeforeFailureSigningCharge (encodingPairIncrementCharge (secretKey parameter default otsTable ftsTable))
        adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * initialRawIndexRate q +
        initializedBeforeFailureSigningCharge (nonMessageNonEncodingHashCharge parameter)
          adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
        initializedPaidCoverageResidual adversary parameter otsTable ftsTable q fuel :=
  (add_le_add (add_le_add (probEvent_liveResidual_add_structuralOverlap_le_cacheCover
    adversary q hq parameter hp otsTable ftsTable hfts fuel) le_rfl) le_rfl).trans
      (probEvent_liveSigningCacheCovered_pairs_retiredRefund_le_reserved_add_residual
        adversary q hq hqMax parameter hp otsTable ftsTable hfts fuel)

noncomputable def sampledTerminalStructuralCoverageOverlap (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        Pr[TerminalStructuralCoverageOverlap parameter table (curryFtsTableEquiv ftsSecret) |
          runRetainedWithFailure (parentException parameter table (curryFtsTableEquiv ftsSecret))
            adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel]

theorem sampled_liveResidual_overlap_pairs_retiredRefund_le_reserved_add_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledLiveNonSecretResidual adversary q fuel + sampledTerminalStructuralCoverageOverlap adversary q fuel +
      sampledRetiredCoverageRefund adversary q fuel +
      sampledSigningEncodingPairCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * initialRawIndexRate q +
        sampledSigningNonEncodingReserve adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
        sampledPaidCoverageResidual adversary q fuel := by
  unfold sampledLiveNonSecretResidual sampledTerminalStructuralCoverageOverlap sampledRetiredCoverageRefund sampledPaidCoverageResidual
    sampledSigningEncodingPairCharge sampledSigningNonEncodingReserve
  simp only [← ENNReal.tsum_mul_right, mul_assoc, add_assoc, ← ENNReal.tsum_add, ← mul_add]
  apply coverage_expected_le_constant_add
  intro parameter hp
  apply coverage_expected_le_constant_add
  intro ftsSecret hfts
  apply coverage_expected_le_constant_add
  intro table _
  simpa only [initializedBeforeFailureSigningCharge, ← ENNReal.tsum_mul_right, mul_assoc,
    add_assoc, ← ENNReal.tsum_add, ← mul_add] using
    probEvent_liveResidual_overlap_pairs_retiredRefund_le_reserved_add_residual adversary q hq hqMax parameter hp table
      (curryFtsTableEquiv ftsSecret) hfts fuel

theorem forgeAdvantage_add_doubleParentCredit_retiredNetRefund_structuralOverlap_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + sampledCollisionDoubleParentCredit adversary q (q + 1) +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledOuterEncodingReserveAfterPairs adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledRetiredNetCoverageRefund adversary q (q + 1) + sampledTerminalStructuralCoverageOverlap adversary q (q + 1) ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + (q : ENNReal) * initialRawIndexRate q := by
  have h := forgeAdvantage_add_doubleParentCredit_coverageRefund_le adversary q hq hqMax
    (sampledRetiredCoverageRefund adversary q (q + 1) + sampledTerminalStructuralCoverageOverlap adversary q (q + 1))
    (by simpa only [add_assoc, add_comm, add_left_comm] using
      sampled_liveResidual_overlap_pairs_retiredRefund_le_reserved_add_residual adversary q hq hqMax (q + 1))
  rw [← sampledRetiredNetCoverageRefund_add_residual] at h
  apply ENNReal.le_of_add_le_add_right (sampledPaidCoverageResidual_ne_top adversary q hq hqMax (q + 1))
  simpa only [add_assoc, add_comm, add_left_comm] using h

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
