import SphincsSecurity.Proof.SampledRetiredCoverageRefund

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local irreducible] expectedBeforeFailureSigningCharge expectedBudgetedLogCharge expectedRemainingUnusedCoverageCharge
set_option backward.isDefEq.respectTransparency false

private theorem reserve_le_refund_of_balance
    (terminal unused initial reserve residual refund pairs : ENNReal)
    (ht : terminal ≠ ⊤) (hu : terminal + unused ≤ initial)
    (hb : terminal + refund + pairs = initial + reserve + residual) :
    unused + reserve + residual ≤ refund + pairs := by
  apply ENNReal.le_of_add_le_add_left ht
  calc
    terminal + (unused + reserve + residual) = terminal + unused + reserve + residual := by ring
    _ ≤ initial + reserve + residual := add_le_add (add_le_add hu le_rfl) le_rfl
    _ = terminal + (refund + pairs) := by simpa only [add_assoc] using hb.symm

theorem expected_remainingUnused_add_signingReserve_add_residual_le_completeRefund_add_pairs
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    expectedRemainingUnusedCoverageCharge exception parameter root otsTable ftsTable q ∅ Finset.univ
        computation q frame (cache, []) hit failed * ((2 ^ 140 : Nat) : ENNReal)⁻¹ +
      expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter)
        parameter root otsTable ftsTable computation frame cache hit failed * (Fintype.card Digest : ENNReal)⁻¹ +
      expectedPaidCoverageResidual exception parameter root otsTable ftsTable q computation q frame (cache, []) hit failed ≤
      expectedCompleteCoverageRefund exception parameter root otsTable ftsTable q computation q frame (cache, []) hit failed +
        expectedBeforeFailureSigningCharge exception (encodingPairIncrementCharge (secretKey parameter root otsTable ftsTable))
          parameter root otsTable ftsTable computation frame cache hit failed * (Fintype.card Digest : ENNReal)⁻¹ := by
  let key := secretKey parameter root otsTable ftsTable
  let terminal := expectedTerminalLogPotential exception parameter root otsTable ftsTable
    (fun current => cappedRemainingCachedTargetEnvelope key q 0 current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
    computation frame (cache, []) hit failed
  let initial := survivingLogPotential
    (fun current => remainingCoveragePotential key q q current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) (cache, []) hit failed
  have hsigned : SigningDigestsCached parameter cache root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hu : terminal + expectedRemainingUnusedCoverageCharge exception parameter root otsTable ftsTable q ∅ Finset.univ
      computation q frame (cache, []) hit failed * ((2 ^ 140 : Nat) : ENNReal)⁻¹ ≤ initial := by
    have h := mul_le_mul' (expected_runWithFailure_remainingTarget_add_unused_le exception parameter root otsTable ftsTable
      q q hq computation frame (cache, []) hit failed hbound hsigned hcache ∅ Finset.univ (by constructor <;> simp))
      (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹))
    simpa only [terminal, initial, expectedTerminalLogPotential, add_mul, ← ENNReal.tsum_mul_right,
      mul_assoc, survivingLogPotential_mul, key] using h
  have hi : initial ≤ (q : ENNReal) * initialRawIndexRate q := by
    rw [← remainingCoveragePotential_initial_scaled key q cache hnone]
    unfold initial survivingLogPotential
    split_ifs
    · exact zero_le
    · exact le_rfl
  have ht : terminal ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by finiteness)
      (ne_top_of_le_ne_top (by finiteness) (initialRawIndexRate_le_127_sharp q hq)))
    ((le_self_add.trans hu).trans hi)
  exact reserve_le_refund_of_balance terminal _ initial _ _ _ _ ht hu
    (expected_runWithFailure_coverage_pairs_completeRefund_eq exception parameter root otsTable ftsTable
      q q hq computation frame (cache, []) hit failed hbound hsigned hcache)


theorem sampled_remainingUnused_add_signingReserve_add_residual_le_completeRefund_add_pairs
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledRemainingUnusedCoverageCharge adversary q fuel +
      sampledSigningNonEncodingReserve adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledPaidCoverageResidual adversary q fuel ≤
      sampledCompleteCoverageRefund adversary q fuel +
        sampledSigningEncodingPairCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ := by
  unfold sampledRemainingUnusedCoverageCharge initializedRemainingUnusedCoverageCharge
    sampledSigningNonEncodingReserve sampledPaidCoverageResidual initializedPaidCoverageResidual
    sampledCompleteCoverageRefund sampledCoverageRefund initializedCoverageRefund sampledSigningEncodingPairCharge
  simp only [← ENNReal.tsum_mul_right, mul_assoc, ← ENNReal.tsum_add, ← mul_add]
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
      have htrace := OtsProbeSimulation.isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hp table
        (fun index tree leaf => ftsTable (index, tree, leaf)) hfts initial.2.1
      have hroot := initializeRoot_original_support parameter table ftsTable q fuel initial hi
      rw [originalRoot, simulateQ_romImpl_liftM] at hroot
      have hgame := isQueryBoundP_gameAfterSecrets adversary q hq hp
        (OtsProbeSimulation.mem_support_sampleOtsSecrets_all key.otsSecret) hfts
      have hbound := retainedRoot_expanded_rest_queryBound adversary parameter key.otsSecret ftsTable q hgame initial.2 hroot
      rw [expectedBeforeFailureSigningCharge_retainedComputation _ _ adversary parameter initial.2.1 table ftsTable q htrace,
        expectedBeforeFailureSigningCharge_retainedComputation _ _ adversary parameter initial.2.1 table ftsTable q htrace]
      exact expected_remainingUnused_add_signingReserve_add_residual_le_completeRefund_add_pairs
        (parentException parameter table ftsTable) parameter initial.2.1 table ftsTable q hqMax
        (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) hbound
        initial.1 initial.2.2 false initial.1.isNone hconditions.1 hconditions.2
    · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]
  · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]

theorem sampled_remainingUnused_add_signingAfterPairs_le_completeNetRefund
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledRemainingUnusedCoverageCharge adversary q fuel +
      sampledSigningNonEncodingReserveAfterPairs adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤
      sampledCompleteNetCoverageRefund adversary q fuel := by
  have h := sampled_remainingUnused_add_signingReserve_add_residual_le_completeRefund_add_pairs adversary q hq hqMax fuel
  rw [← sampledSigningNonEncodingReserveAfterPairs_add_pairs adversary q hq hqMax fuel,
    ← sampledCompleteNetCoverageRefund_add_residual] at h
  apply ENNReal.le_of_add_le_add_right (ENNReal.add_ne_top.mpr
    ⟨sampledPaidCoverageResidual_ne_top adversary q hq hqMax fuel,
      sampledSigningEncodingPairCharge_scaled_ne_top adversary q hq hqMax fuel⟩)
  convert h using 1 <;> ring

theorem sampled_remainingUnused_add_signingAfterPairs_add_terminal_le_retiredNetRefund
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledRemainingUnusedCoverageCharge adversary q fuel +
      sampledSigningNonEncodingReserveAfterPairs adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledTerminalCoverageRetirement adversary q fuel ≤ sampledRetiredNetCoverageRefund adversary q fuel := by
  rw [sampledRetiredNetCoverageRefund_eq_complete_add_terminal adversary q hq hqMax fuel]
  exact add_le_add (sampled_remainingUnused_add_signingAfterPairs_le_completeNetRefund adversary q hq hqMax fuel) le_rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
