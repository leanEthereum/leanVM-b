import SphincsSecurity.Proof.UpperDigestSelection
import SphincsSecurity.Proof.SampledSigningEnvelopeGap

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def cachedSelectionFraction (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) /
    (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) + ((2 ^ 118 : Nat) : ENNReal))

noncomputable def rawIndexSigningIncrementEnvelope (key : SecretKey) (cap queries signings : Nat)
    (state : CoverLogState) : TargetShapeVector :=
  fun G R => (Fintype.card Index : ENNReal)⁻¹ *
    targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
      queries signings (targetFreshSigningIncrement (observedRawIndexShapeVector key state)) G R +
    digestReuseWeight cap *
      targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        queries signings (targetReuseStep (observedRawIndexShapeVector key state)) G R

theorem rawIndexSelectionGaps_ge_nonfresh_increment
    (key : SecretKey) (cap queries signings : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    (1 - freshDigestSelectionProbability key message state.1) *
        rawIndexSigningIncrementEnvelope key cap queries signings state groups remaining ≤
      rawIndexNonfreshSigningGap key cap queries signings state message groups remaining +
        rawIndexReuseSigningGap key cap queries signings state message groups remaining := by
  have h := mul_le_mul' (nonfresh_mul_digestReuseWeight_le_reuse_gap key message state.1 cap hcap hcache)
    (le_refl (targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
      queries signings (targetReuseStep (observedRawIndexShapeVector key state)) groups remaining))
  unfold rawIndexSigningIncrementEnvelope rawIndexNonfreshSigningGap rawIndexReuseSigningGap
  rw [mul_add, ← mul_assoc, ← mul_assoc]
  exact add_le_add le_rfl h

theorem rawIndexSelectionGaps_ge_cached_fraction
    (key : SecretKey) (cap queries signings : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    cachedSelectionFraction key message state.1 * rawIndexSigningIncrementEnvelope key cap queries signings state groups remaining ≤
      rawIndexNonfreshSigningGap key cap queries signings state message groups remaining +
        rawIndexReuseSigningGap key cap queries signings state message groups remaining :=
  (mul_le_mul' (nonfreshSelection_ge_cached_fraction key message state.1 cap hcache) le_rfl).trans
    (rawIndexSelectionGaps_ge_nonfresh_increment key cap queries signings hcap state hcache message groups remaining)

noncomputable def cachedSelectionCoverageGap (key : SecretKey) (cap budget : Nat) (message : Message)
    (state : CoverLogState) : ENNReal :=
  if QueryCache.enncard state.1 ≤ cap ∧ ValidSigningStep state.2 (.inr message) then
    cachedSelectionFraction key message state.1 *
      rawIndexSigningIncrementEnvelope key cap budget (signatureLimit - (state.2.length + 1)) state ∅ Finset.univ *
      (budget : ENNReal) * (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
      ((2 ^ 140 : Nat) : ENNReal)⁻¹
  else 0

theorem cachedSelectionCoverageGap_le_signingEnvelopeGap
    (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (message : Message) (state : CoverLogState) :
    cachedSelectionCoverageGap key cap budget message state ≤ signingCoverageEnvelopeGap key cap budget message state := by
  unfold cachedSelectionCoverageGap
  split_ifs with hactive
  · have h := rawIndexSelectionGaps_ge_cached_fraction key cap budget (signatureLimit - (state.2.length + 1))
      hcap state hactive.1 message ∅ Finset.univ
    unfold signingCoverageEnvelopeGap remainingRawIndexSigningGap
    rw [if_pos hactive.2]
    exact mul_le_mul' (mul_le_mul' (mul_le_mul' (h.trans le_self_add) le_rfl) le_rfl) le_rfl
  · exact zero_le

namespace FtsProbeSimulation.JointOriginal

open OtsProbeSimulation (OtsSecretIndex)
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable

noncomputable def cachedSelectionStepGap (key : SecretKey) (cap budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (_frame : Option Frame)
    (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  match input with
  | .inl _ => 0
  | .inr message => survivingLogPotential
      (cachedSelectionCoverageGap key cap (budget - signingExecutionHashCost (.inr message)) message) state hit failed

theorem cachedSelectionStepGap_le_signingEnvelopeStepGap
    (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame)
    (state : CoverLogState) (hit failed : Bool) :
    cachedSelectionStepGap key cap budget input frame state hit failed ≤
      signingEnvelopeStepGap key cap budget input frame state hit failed := by
  cases input with
  | inl world => exact le_rfl
  | inr message =>
      unfold cachedSelectionStepGap signingEnvelopeStepGap survivingLogPotential
      split_ifs
      · exact le_rfl
      · exact cachedSelectionCoverageGap_le_signingEnvelopeGap key cap _ hcap message state

noncomputable abbrev expectedCachedSelectionGap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α) :=
  expectedBudgetedLogCharge exception parameter root otsTable ftsTable (fun _ _ _ _ => 0)
    (cachedSelectionStepGap (secretKey parameter root otsTable ftsTable) cap) computation

theorem expectedCachedSelectionGap_le_signingEnvelopeGap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (hcap : cap ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (budget : Nat) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedCachedSelectionGap exception parameter root otsTable ftsTable cap computation budget frame state hit failed ≤
      expectedSigningEnvelopeGap exception parameter root otsTable ftsTable cap computation budget frame state hit failed := by
  induction computation using OracleComp.inductionOn generalizing budget frame state hit failed with
  | pure value => exact le_rfl
  | query_bind input next ih =>
      simp only [expectedCachedSelectionGap, expectedSigningEnvelopeGap, expectedBudgetedLogCharge_query_bind] at ih ⊢
      apply add_le_add (cachedSelectionStepGap_le_signingEnvelopeStepGap _ cap budget hcap input frame state hit failed)
      exact ENNReal.tsum_le_tsum (fun result => mul_le_mul' le_rfl
        (ih result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
          (stepSigningLogState input state.2 result) result.1.2.2 result.2))

noncomputable def initializedCachedSelectionGap (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) : ENNReal :=
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    expectedCachedSelectionGap (parentException parameter otsTable ftsTable) parameter initial.2.1 otsTable ftsTable q
      (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) q
      initial.1 (initial.2.2, []) false initial.1.isNone

noncomputable def sampledCachedSelectionGap (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedCachedSelectionGap adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

theorem sampledCachedSelectionGap_le_signingEnvelopeGap
    (adversary : Adversary) (q fuel : Nat) (hq : q ≤ 2 ^ 127) :
    sampledCachedSelectionGap adversary q fuel ≤ sampledSigningEnvelopeGap adversary q fuel := by
  unfold sampledCachedSelectionGap sampledSigningEnvelopeGap
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro table
  apply mul_le_mul' le_rfl
  unfold initializedCachedSelectionGap initializedSigningEnvelopeGap
  exact ENNReal.tsum_le_tsum (fun initial => mul_le_mul' le_rfl
    (expectedCachedSelectionGap_le_signingEnvelopeGap _ _ _ _ _ q hq _ _ _ _ _ _))

theorem forgeAdvantage_add_doubleParentCredit_cachedSelectionGap_structuralOverlap_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + sampledCollisionDoubleParentCredit adversary q (q + 1) +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledOuterEncodingReserveAfterPairs adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (sampledNetCoverageRefund adversary q (q + 1) + sampledCachedSelectionGap adversary q (q + 1) +
        sampledTerminalCoverageRetirement adversary q (q + 1)) +
      sampledTerminalStructuralCoverageOverlap adversary q (q + 1) ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + (q : ENNReal) * initialRawIndexRate q := by
  apply le_trans ?_ (forgeAdvantage_add_doubleParentCredit_signingEnvelopeGap_structuralOverlap_le adversary q hq hqMax)
  exact add_le_add (add_le_add le_rfl (add_le_add
    (add_le_add le_rfl (sampledCachedSelectionGap_le_signingEnvelopeGap adversary q (q + 1) hqMax)) le_rfl)) le_rfl

end FtsProbeSimulation.JointOriginal
end SphincsSecurity.Concrete
