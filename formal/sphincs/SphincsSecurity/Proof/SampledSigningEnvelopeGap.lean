import SphincsSecurity.Proof.SigningEnvelopeRefund
import SphincsSecurity.Proof.CompleteCoverageReserveLowerBound
import SphincsSecurity.Proof.StructuralCoverageOverlap

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable

noncomputable def initializedSigningEnvelopeGap (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) : ENNReal :=
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    expectedSigningEnvelopeGap (parentException parameter otsTable ftsTable) parameter initial.2.1 otsTable ftsTable q
      (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) q
      initial.1 (initial.2.2, []) false initial.1.isNone

noncomputable def sampledSigningEnvelopeGap (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedSigningEnvelopeGap adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

private theorem spmf_expected_le_constant_add {α : Type} (computation : SPMF α)
    (value risk : α → ENNReal) (bound : ENNReal)
    (h : ∀ result ∈ support computation, value result ≤ bound + risk result) :
    (∑' result, Pr[= result | computation] * value result) ≤
      bound + ∑' result, Pr[= result | computation] * risk result := by
  calc
    _ ≤ ∑' result, Pr[= result | computation] * (bound + risk result) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support computation
      · exact mul_le_mul' le_rfl (h result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl

private theorem initialized_signingEnvelope_shared_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat)
    (initial) (hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)) :
    (expectedTerminalLogPotential (parentException parameter otsTable ftsTable) parameter initial.2.1 otsTable ftsTable
      (fun current => cappedRemainingCachedTargetEnvelope (secretKey parameter initial.2.1 otsTable ftsTable)
        q 0 current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
      (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) initial.1 (initial.2.2, []) false initial.1.isNone +
      expectedBeforeFailureSigningCharge (parentException parameter otsTable ftsTable)
        (encodingPairIncrementCharge (secretKey parameter initial.2.1 otsTable ftsTable))
        parameter initial.2.1 otsTable ftsTable (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩)
        initial.1 initial.2.2 false initial.1.isNone * (Fintype.card Digest : ENNReal)⁻¹) ≤
      (q : ENNReal) * initialRawIndexRate q +
        expectedBeforeFailureSigningCharge (parentException parameter otsTable ftsTable)
          (encodingPairIncrementCharge (secretKey parameter default otsTable ftsTable))
          parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q)
          initial.1 initial.2.2 false initial.1.isNone * (Fintype.card Digest : ENNReal)⁻¹ := by
  let key := secretKey parameter initial.2.1 otsTable ftsTable
  have hconditions := initialized_stoppedTarget_conditions adversary q hq parameter hp otsTable ftsTable hfts fuel initial hi
  have hroot := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
  rw [originalRoot, simulateQ_romImpl_liftM] at hroot
  have hgame := isQueryBoundP_gameAfterSecrets adversary q hq hp
    (OtsProbeSimulation.mem_support_sampleOtsSecrets_all key.otsSecret) hfts
  have hbound := retainedRoot_expanded_rest_queryBound adversary parameter key.otsSecret ftsTable q hgame initial.2 hroot
  have hsigned : SigningDigestsCached parameter initial.2.2 initial.2.1 [] := by
    intro entry he
    simp only [List.not_mem_nil] at he
  have hterminal := mul_le_mul' (le_self_add.trans
    (expected_runWithFailure_remainingTarget_add_unused_le (parentException parameter otsTable ftsTable)
      parameter initial.2.1 otsTable ftsTable q q hqMax
      (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) initial.1 (initial.2.2, []) false initial.1.isNone
      hbound hsigned hconditions.2 ∅ Finset.univ (by constructor <;> simp)))
    (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹))
  have ht : expectedTerminalLogPotential (parentException parameter otsTable ftsTable) parameter initial.2.1 otsTable ftsTable
      (fun current => cappedRemainingCachedTargetEnvelope key q 0 current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
      (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) initial.1 (initial.2.2, []) false initial.1.isNone ≤
      (q : ENNReal) * initialRawIndexRate q := by
    rw [← remainingCoveragePotential_initial_scaled key q initial.2.2 hconditions.1]
    have hsurvive : survivingLogPotential (fun current => remainingCoveragePotential key q q current ∅ Finset.univ)
        (initial.2.2, []) false initial.1.isNone ≤ remainingCoveragePotential key q q (initial.2.2, []) ∅ Finset.univ := by
      unfold survivingLogPotential
      split_ifs
      · exact zero_le
      · exact le_rfl
    apply le_trans ?_ (mul_le_mul' hsurvive (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹)))
    simpa only [expectedTerminalLogPotential, ← ENNReal.tsum_mul_right, mul_assoc, survivingLogPotential_mul, key] using hterminal
  have htrace := OtsProbeSimulation.isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hp otsTable
    (fun index tree leaf => ftsTable (index, tree, leaf)) hfts initial.2.1
  rw [expectedBeforeFailureSigningCharge_retainedComputation _ _ adversary parameter initial.2.1 otsTable ftsTable q htrace]
  exact add_le_add ht le_rfl

theorem sampledPaidCoverageRefund_add_signingEnvelopeGap_le_complete
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledPaidCoverageRefund adversary q fuel + sampledSigningEnvelopeGap adversary q fuel ≤
      sampledCompleteCoverageRefund adversary q fuel := by
  let shared := fun parameter otsTable ftsTable (initial : Option Frame × Digest × QueryCache HashSpec) =>
    expectedTerminalLogPotential (parentException parameter otsTable ftsTable) parameter initial.2.1 otsTable ftsTable
      (fun current => cappedRemainingCachedTargetEnvelope (secretKey parameter initial.2.1 otsTable ftsTable)
        q 0 current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
      (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) initial.1 (initial.2.2, []) false initial.1.isNone +
      expectedBeforeFailureSigningCharge (parentException parameter otsTable ftsTable)
        (encodingPairIncrementCharge (secretKey parameter initial.2.1 otsTable ftsTable)) parameter initial.2.1 otsTable ftsTable
        (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) initial.1 initial.2.2 false initial.1.isNone *
          (Fintype.card Digest : ENNReal)⁻¹
  let common : ENNReal := ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        ∑' initial, Pr[= initial | initializeRoot parameter table (curryFtsTableEquiv ftsSecret) q fuel] *
          shared parameter table (curryFtsTableEquiv ftsSecret) initial
  have hc : common ≤ (q : ENNReal) * initialRawIndexRate q +
      sampledSigningEncodingPairCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ := by
    unfold common shared sampledSigningEncodingPairCharge
    simp only [← ENNReal.tsum_mul_right, mul_assoc]
    apply coverage_expected_le_constant_add
    intro parameter hp
    apply coverage_expected_le_constant_add
    intro ftsSecret hfts
    apply coverage_expected_le_constant_add
    intro table _
    apply spmf_expected_le_constant_add
    intro initial hi
    exact initialized_signingEnvelope_shared_le adversary q hq hqMax parameter hp table
      (curryFtsTableEquiv ftsSecret) hfts fuel initial hi
  have hfinite : common ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by finiteness)
      (ne_top_of_le_ne_top (by finiteness) (initialRawIndexRate_le_127_sharp q hqMax)),
      sampledSigningEncodingPairCharge_scaled_ne_top adversary q hq hqMax fuel⟩) hc
  apply ENNReal.le_of_add_le_add_right hfinite
  unfold common shared sampledPaidCoverageRefund initializedPaidCoverageRefund sampledSigningEnvelopeGap initializedSigningEnvelopeGap
    sampledCompleteCoverageRefund sampledCoverageRefund initializedCoverageRefund completeCoverageRefundFamily
  simp only [← ENNReal.tsum_add, ← mul_add]
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hp : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro table
    apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro initial
    by_cases hi : initial ∈ support (initializeRoot parameter table (curryFtsTableEquiv ftsSecret) q fuel)
    · apply mul_le_mul' le_rfl
      let ftsTable := curryFtsTableEquiv ftsSecret
      let key := secretKey parameter initial.2.1 table ftsTable
      have hfts := mem_support_sampleFtsSecrets ftsSecret
      have hconditions := initialized_stoppedTarget_conditions adversary q hq parameter hp table ftsTable hfts fuel initial hi
      have hroot := initializeRoot_original_support parameter table ftsTable q fuel initial hi
      rw [originalRoot, simulateQ_romImpl_liftM] at hroot
      have hgame := isQueryBoundP_gameAfterSecrets adversary q hq hp
        (OtsProbeSimulation.mem_support_sampleOtsSecrets_all key.otsSecret) hfts
      have hbound := retainedRoot_expanded_rest_queryBound adversary parameter key.otsSecret ftsTable q hgame initial.2 hroot
      have hsigned : SigningDigestsCached parameter initial.2.2 initial.2.1 [] := by
        intro entry he
        simp only [List.not_mem_nil] at he
      have h := expected_runWithFailure_coverage_pairs_signingEnvelopeRefund_le (parentException parameter table ftsTable)
        parameter initial.2.1 table ftsTable q q hqMax
        (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) initial.1 (initial.2.2, []) false initial.1.isNone
        hbound hsigned hconditions.2
      have hb := expected_runWithFailure_coverage_pairs_completeRefund_eq (parentException parameter table ftsTable)
        parameter initial.2.1 table ftsTable q q hqMax
        (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) initial.1 (initial.2.2, []) false initial.1.isNone
        hbound hsigned hconditions.2
      have hcomparison := h.trans_eq hb.symm
      rw [expectedSigningEnvelopeRefund_eq_paid_add_gap] at hcomparison
      unfold expectedTerminalLogPotential
      convert hcomparison using 1 <;> first | rfl | ring
    · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]
  · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]

theorem sampledSigningEnvelopeGap_le_additional
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledSigningEnvelopeGap adversary q fuel ≤ sampledAdditionalCoverageRefund adversary q fuel := by
  apply ENNReal.le_of_add_le_add_left (sampledPaidCoverageRefund_ne_top adversary q hq hqMax fuel)
  rw [sampledAdditionalCoverageRefund, add_tsub_cancel_of_le (sampledPaidCoverageRefund_le_complete adversary q fuel)]
  exact sampledPaidCoverageRefund_add_signingEnvelopeGap_le_complete adversary q hq hqMax fuel

theorem sampledNetCoverageRefund_add_signingEnvelopeGap_terminal_le_retired
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledNetCoverageRefund adversary q fuel + sampledSigningEnvelopeGap adversary q fuel +
      sampledTerminalCoverageRetirement adversary q fuel ≤ sampledRetiredNetCoverageRefund adversary q fuel := by
  rw [sampledRetiredNetCoverageRefund_eq_complete_add_terminal adversary q hq hqMax fuel,
    ← sampledNetCoverageRefund_add_additional_eq_complete adversary q hq hqMax fuel]
  exact add_le_add (add_le_add le_rfl (sampledSigningEnvelopeGap_le_additional adversary q hq hqMax fuel)) le_rfl

theorem sampledSigningEnvelopeGap_ne_top
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledSigningEnvelopeGap adversary q fuel ≠ ⊤ :=
  ne_top_of_le_ne_top (sampledCompleteCoverageRefund_ne_top adversary q hq hqMax fuel)
    (le_add_self.trans (sampledPaidCoverageRefund_add_signingEnvelopeGap_le_complete adversary q hq hqMax fuel))

theorem forgeAdvantage_add_doubleParentCredit_signingEnvelopeGap_structuralOverlap_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + sampledCollisionDoubleParentCredit adversary q (q + 1) +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledOuterEncodingReserveAfterPairs adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (sampledNetCoverageRefund adversary q (q + 1) + sampledSigningEnvelopeGap adversary q (q + 1) +
        sampledTerminalCoverageRetirement adversary q (q + 1)) +
      sampledTerminalStructuralCoverageOverlap adversary q (q + 1) ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + (q : ENNReal) * initialRawIndexRate q := by
  apply le_trans ?_ (forgeAdvantage_add_doubleParentCredit_retiredNetRefund_structuralOverlap_le adversary q hq hqMax)
  exact add_le_add (add_le_add le_rfl
    (sampledNetCoverageRefund_add_signingEnvelopeGap_terminal_le_retired adversary q hq hqMax (q + 1))) le_rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
