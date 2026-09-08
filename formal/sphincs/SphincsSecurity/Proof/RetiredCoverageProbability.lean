import SphincsSecurity.Proof.RetiredCoverageBalance
import SphincsSecurity.Proof.InitializedPaidCoverage

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] expectedBeforeFailureSigningCharge expectedBudgetedLogCharge retainedComputation
set_option backward.isDefEq.respectTransparency false

def LiveSigningCacheCovered (parameter : PublicParameter)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool) : Prop :=
  result.1.2.2 = false ∧ result.2 = false ∧ ∃ value, result.1.2.1.1 = some value ∧
    SigningTranscript.Valid value.2.1.2 ∧ SigningCacheCovered parameter value.1 result.1.2.1.2 value.2.1.2

theorem probEvent_runWithFailure_liveCover_pairs_retiredRefund_le_reserved_add_residual
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
      expectedRetiredCoverageRefund exception parameter root otsTable ftsTable q computation q frame (cache, []) hit failed +
      expectedBeforeFailureSigningCharge exception (encodingPairIncrementCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame cache hit failed * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * initialRawIndexRate q +
        expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter)
          parameter root otsTable ftsTable computation frame cache hit failed * (Fintype.card Digest : ENNReal)⁻¹ +
        expectedPaidCoverageResidual exception parameter root otsTable ftsTable q computation q frame (cache, []) hit failed := by
  let key := secretKey parameter root otsTable ftsTable
  have hsigned : SigningDigestsCached parameter cache root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have h := expected_runWithFailure_liveCover_pairs_retiredRefund_eq exception parameter root otsTable ftsTable
    q q hq computation frame (cache, []) hit failed hbound hsigned hcache
  apply (le_of_eq h).trans
  apply add_le_add (add_le_add _ le_rfl) le_rfl
  rw [← remainingCoveragePotential_initial_scaled key q cache hnone]
  unfold survivingLogPotential
  split_ifs
  · exact zero_le
  · exact le_rfl

theorem probEvent_retained_cacheCover_pairs_retiredRefund_le_reserved_add_residual
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q : Nat) (hq : q ≤ 2 ^ 127)
    (htrace : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP (· matches Sum.inr _) q)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (unloggedRetainedRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (unloggedRetainedRestComputation adversary ⟨root, parameter⟩)).run (cache, [])), QueryCache.enncard result.2.1 ≤ q) :
    Pr[LiveSigningCacheCovered parameter |
      runWithFailure exception parameter root otsTable ftsTable (retainedComputation adversary parameter root q) frame cache hit failed] +
      expectedRetiredCoverageRefund exception parameter root otsTable ftsTable q
        (unloggedRetainedRestComputation adversary ⟨root, parameter⟩) q frame (cache, []) hit failed +
      expectedBeforeFailureSigningCharge exception (encodingPairIncrementCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable (retainedComputation adversary parameter root q) frame cache hit failed * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * initialRawIndexRate q +
        expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter)
          parameter root otsTable ftsTable (retainedComputation adversary parameter root q) frame cache hit failed * (Fintype.card Digest : ENNReal)⁻¹ +
        expectedPaidCoverageResidual exception parameter root otsTable ftsTable q
          (unloggedRetainedRestComputation adversary ⟨root, parameter⟩) q frame (cache, []) hit failed := by
  rw [runWithFailure_retainedComputation_trace exception adversary parameter root otsTable ftsTable q htrace, probEvent_map,
    expectedBeforeFailureSigningCharge_retainedComputation exception _ adversary parameter root otsTable ftsTable q htrace,
    expectedBeforeFailureSigningCharge_retainedComputation exception _ adversary parameter root otsTable ftsTable q htrace]
  apply le_trans ?_ (probEvent_runWithFailure_liveCover_pairs_retiredRefund_le_reserved_add_residual exception parameter root otsTable ftsTable q hq
    (unloggedRetainedRestComputation adversary ⟨root, parameter⟩) hbound frame cache hit failed hnone hcache)
  apply add_le_add (add_le_add ?_ le_rfl) le_rfl
  apply probEvent_mono
  intro result _ hcover
  obtain ⟨hhit, hfailed, value, hvalue, hvalid, hcovered⟩ := hcover
  have hvalue' : (root, arrangeRetainedTrace result.1.2.1.1) = value := Option.some.inj hvalue
  subst value
  exact ⟨hhit, hfailed, hvalid, hcovered⟩

noncomputable def initializedRetiredCoverageRefund (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) : ENNReal :=
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    expectedRetiredCoverageRefund (parentException parameter otsTable ftsTable) parameter initial.2.1 otsTable ftsTable q
      (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) q initial.1 (initial.2.2, []) false initial.1.isNone

theorem probEvent_liveSigningCacheCovered_pairs_retiredRefund_le_reserved_add_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[LiveSigningCacheCovered parameter |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] +
      initializedRetiredCoverageRefund adversary parameter otsTable ftsTable q fuel +
      initializedBeforeFailureSigningCharge (encodingPairIncrementCharge (secretKey parameter default otsTable ftsTable))
        adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * initialRawIndexRate q +
        initializedBeforeFailureSigningCharge (nonMessageNonEncodingHashCharge parameter)
          adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
        initializedPaidCoverageResidual adversary parameter otsTable ftsTable q fuel := by
  rw [runRetainedWithFailure, probEvent_bind_eq_tsum]
  unfold initializedRetiredCoverageRefund initializedPaidCoverageResidual initializedBeforeFailureSigningCharge
  simp only [← ENNReal.tsum_mul_right, mul_assoc, ← ENNReal.tsum_add, ← mul_add]
  calc
    _ ≤ ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
        ((q : ENNReal) * initialRawIndexRate q +
          expectedBeforeFailureSigningCharge (parentException parameter otsTable ftsTable) (nonMessageNonEncodingHashCharge parameter)
            parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q)
              initial.1 initial.2.2 false initial.1.isNone * (Fintype.card Digest : ENNReal)⁻¹ +
          expectedPaidCoverageResidual (parentException parameter otsTable ftsTable) parameter initial.2.1 otsTable ftsTable q
            (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) q initial.1 (initial.2.2, []) false initial.1.isNone) := by
      apply ENNReal.tsum_le_tsum
      intro initial
      by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
      · let key := secretKey parameter initial.2.1 otsTable ftsTable
        have hconditions := initialized_stoppedTarget_conditions adversary q hq parameter hp otsTable ftsTable hfts fuel initial hi
        have htrace := OtsProbeSimulation.isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hp otsTable
          (fun index tree leaf => ftsTable (index, tree, leaf)) hfts initial.2.1
        have hroot := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
        rw [originalRoot, simulateQ_romImpl_liftM] at hroot
        have hgame := isQueryBoundP_gameAfterSecrets adversary q hq hp
          (OtsProbeSimulation.mem_support_sampleOtsSecrets_all key.otsSecret) hfts
        have hbound := retainedRoot_expanded_rest_queryBound adversary parameter key.otsSecret ftsTable q hgame initial.2 hroot
        exact mul_le_mul' le_rfl (probEvent_retained_cacheCover_pairs_retiredRefund_le_reserved_add_residual (parentException parameter otsTable ftsTable)
          adversary parameter initial.2.1 otsTable ftsTable q hqMax htrace hbound initial.1 initial.2.2 false initial.1.isNone hconditions.1 hconditions.2)
      · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]
    _ ≤ _ := by
      simp only [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]
      apply add_le_add (add_le_add ?_ le_rfl) le_rfl
      have hmass : (∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel]) ≤ 1 := tsum_probOutput_le_one
      simpa only [one_mul, mul_assoc] using mul_le_mul' hmass (le_refl ((q : ENNReal) * initialRawIndexRate q))

theorem probEvent_retained_liveCover_pairs_retiredRefund_le_reserved_add_residual
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q : Nat) (hq : q ≤ 2 ^ 127)
    (htrace : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP (· matches Sum.inr _) q)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (unloggedRetainedRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (unloggedRetainedRestComputation adversary ⟨root, parameter⟩)).run (cache, [])), QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => result.1.2.2 = false ∧ result.2 = false ∧
      ∃ value, result.1.2.1.1 = some value ∧ ObservedRetainedCover value (messageAnswers parameter result.1.2.1.2) |
      runWithFailure exception parameter root otsTable ftsTable (retainedComputation adversary parameter root q) frame cache hit failed] +
      expectedRetiredCoverageRefund exception parameter root otsTable ftsTable q
        (unloggedRetainedRestComputation adversary ⟨root, parameter⟩) q frame (cache, []) hit failed +
      expectedBeforeFailureSigningCharge exception (encodingPairIncrementCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable (retainedComputation adversary parameter root q) frame cache hit failed * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * initialRawIndexRate q +
        expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter)
          parameter root otsTable ftsTable (retainedComputation adversary parameter root q) frame cache hit failed * (Fintype.card Digest : ENNReal)⁻¹ +
        expectedPaidCoverageResidual exception parameter root otsTable ftsTable q
          (unloggedRetainedRestComputation adversary ⟨root, parameter⟩) q frame (cache, []) hit failed := by
  apply le_trans ?_ (probEvent_retained_cacheCover_pairs_retiredRefund_le_reserved_add_residual exception
    adversary parameter root otsTable ftsTable q hq htrace hbound frame cache hit failed hnone hcache)
  apply add_le_add (add_le_add ?_ le_rfl) le_rfl
  apply probEvent_mono
  intro result _ ⟨hhit, hfailed, value, hvalue, hobserved⟩
  have hvalid : SigningTranscript.Valid value.2.1.2 := by
    have hwin := hobserved.1
    simp only [OtsProbeSimulation.retainedRestVerdict, Bool.and_eq_true, decide_eq_true_eq] at hwin
    exact hwin.1.1
  exact ⟨hhit, hfailed, value, hvalue, hvalid, observedFewTimeCover_signingCacheCovered _ _ _ _ _ hobserved.2⟩

theorem probEvent_liveNonSecretResidual_pairs_retiredRefund_le_reserved_add_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[LiveNonSecretResidual parameter otsTable ftsTable |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] +
      initializedRetiredCoverageRefund adversary parameter otsTable ftsTable q fuel +
      initializedBeforeFailureSigningCharge (encodingPairIncrementCharge (secretKey parameter default otsTable ftsTable))
        adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * initialRawIndexRate q +
        initializedBeforeFailureSigningCharge (nonMessageNonEncodingHashCharge parameter)
          adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
        initializedPaidCoverageResidual adversary parameter otsTable ftsTable q fuel := by
  apply le_trans ?_ (probEvent_liveSigningCacheCovered_pairs_retiredRefund_le_reserved_add_residual
    adversary q hq hqMax parameter hp otsTable ftsTable hfts fuel)
  apply add_le_add (add_le_add ?_ le_rfl) le_rfl
  apply probEvent_mono
  intro result hr hres
  obtain ⟨value, hvalue, hobserved⟩ :=
    liveNonSecretResidual_observed adversary q hq parameter hp otsTable ftsTable hfts fuel result hr hres
  have hvalid : SigningTranscript.Valid value.2.1.2 := by
    have hwin := hobserved.1
    simp only [OtsProbeSimulation.retainedRestVerdict, Bool.and_eq_true, decide_eq_true_eq] at hwin
    exact hwin.1.1
  exact ⟨hres.2.1, hres.1, value, hvalue, hvalid, observedFewTimeCover_signingCacheCovered _ _ _ _ _ hobserved.2⟩

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
