import SphincsSecurity.Proof.OtsProbeLiveStartCounting
import SphincsSecurity.Proof.OtsProbeLiveSampledReserve

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeChronologicalRetainedComputation
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    OracleComp (LazyRevealProbe.World Coordinate) (RetainedRestResult × SplitHashCache) := do
  let (root, cache) ← maskedPublishedTreeRoot.run emptySplitHashCache
  (simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
    (retainedGameRestComputation adversary ⟨root, parameter⟩)).run cache

theorem expectedLiveNativeProbeCharge_root_eq_zero
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    expectedLiveResolvedQueryCharge nativeProbeQueryCharge (maskedPublishedTreeRoot.run cache) context fuel table = 0 := by
  have hraw : expectedResolvedQueryCharge nativeProbeQueryCharge (maskedPublishedTreeRoot.run cache) context fuel table ≤ (0 : ENNReal) := by
    simpa only [Nat.cast_zero] using expectedResolvedProbeCharge_le_probeBound _ 0 context fuel table (maskedPublishedTreeRoot_probeFree cache)
  exact le_antisymm ((expectedLiveResolvedQueryCharge_le_raw nativeProbeQueryCharge _ context fuel table).trans hraw) zero_le

theorem nativeChronologicalRetained_joint_charge_le_afterTable
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    (expectedLiveResolvedQueryCharge chainStartProbeQueryCharge (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
        { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues } fuel table +
      expectedLiveResolvedQueryCharge structuralProbeQueryCharge (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
        { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues } fuel table) * (4 / 3 : ENNReal) ≤
      liveOtsChargeAfterTable adversary parameter table ftsSecret fuel := by
  rw [expectedLiveChainStart_add_structural_eq_probeCharge]
  unfold nativeChronologicalRetainedComputation
  rw [expectedLiveResolvedQueryCharge_bind _ _ _ _ fuel table DeferredContext.valid_empty.valuesConsistent (startTableAgrees_empty table),
    expectedLiveNativeProbeCharge_root_eq_zero, zero_add, ← ENNReal.tsum_mul_right]
  unfold liveOtsChargeAfterTable
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hresult : result ∈ support (runResolvedFromTable
      { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues } fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache))
  · cases result with
    | none => simp [liveResolvedContinuationCharge]
    | some result =>
        have hcore := resolvedCore_of_mem_runResolvedFromTable _ _ fuel table result
          DeferredContext.valid_empty.valuesConsistent (startTableAgrees_empty table) hresult
        simp only [liveResolvedContinuationCharge, hcore.1, mul_assoc]
        apply mul_le_mul' le_rfl
        rw [expectedLiveNativeOuterCharge_mul]
        apply mul_le_mul' _ le_rfl
        have hlocal := chronological_liveChainStart_add_structural_le_liveOuterCharge parameter result.value.1 ftsSecret
          (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩) result.context result.remaining table result.value.2
          hcore.2.1 hcore.2.2
        rw [expectedLiveChainStart_add_structural_eq_probeCharge] at hlocal
        exact hlocal
  · simp [probOutput_eq_zero_of_not_mem_support hresult]

theorem nativeChronologicalRetained_startHits_add_structuralCharge_le_afterTable
    (adversary : Adversary) (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    (∑ ordinal ∈ Finset.range q, Pr[LiveUnresolvedStartHit nativeCutCandidate |
      sampledNativeProbeCut (nativeChronologicalRetainedComputation adversary parameter ftsSecret) fuel ordinal]) +
      (∑' table, Pr[= table | sampleOtsHashTable] *
        expectedLiveResolvedQueryCharge structuralProbeQueryCharge (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
          { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues } fuel table) *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) ≤
      (∑' table, Pr[= table | sampleOtsHashTable] * liveOtsChargeAfterTable adversary parameter table ftsSecret fuel) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply (add_le_add (sum_sampledNativeProbeCut_unresolvedStart_le_expectedChainStartCharge
    (nativeChronologicalRetainedComputation adversary parameter ftsSecret) fuel q hq) le_rfl).trans
  rw [← add_mul, ← ENNReal.tsum_add]
  simp only [← mul_add]
  rw [← mul_assoc]
  apply mul_le_mul' _ le_rfl
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro table
  rw [mul_assoc]
  exact mul_le_mul' le_rfl (nativeChronologicalRetained_joint_charge_le_afterTable adversary parameter ftsSecret fuel table)

noncomputable def sampledNativeStartRisk (adversary : Adversary) (fuel q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑ ordinal ∈ Finset.range q, Pr[LiveUnresolvedStartHit nativeCutCandidate |
        sampledNativeProbeCut (nativeChronologicalRetainedComputation adversary parameter ftsSecret) fuel ordinal]

noncomputable def sampledNativeStructuralCharge (adversary : Adversary) (fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | sampleOtsHashTable] *
        expectedLiveResolvedQueryCharge structuralProbeQueryCharge (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
          { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues } fuel table

theorem sampledNativeStartRisk_add_structuralCharge_le_liveOtsCharge
    (adversary : Adversary) (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    sampledNativeStartRisk adversary fuel q + sampledNativeStructuralCharge adversary fuel *
      ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) ≤
      sampledLiveOtsCharge adversary fuel * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let factor : ENNReal := ((2 ^ digestBits : Nat) : ENNReal)⁻¹
  have hbound := fun parameter ftsSecret => nativeChronologicalRetained_startHits_add_structuralCharge_le_afterTable
    adversary parameter ftsSecret fuel q hq
  calc
    _ = ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ((∑ ordinal ∈ Finset.range q, Pr[LiveUnresolvedStartHit nativeCutCandidate |
            sampledNativeProbeCut (nativeChronologicalRetainedComputation adversary parameter ftsSecret) fuel ordinal]) +
            (∑' table, Pr[= table | sampleOtsHashTable] *
              expectedLiveResolvedQueryCharge structuralProbeQueryCharge (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
                { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues } fuel table) * ((4 / 3 : ENNReal) * factor)) := by
      simp only [sampledNativeStartRisk, sampledNativeStructuralCharge, factor, mul_add, ENNReal.tsum_add,
        ← mul_assoc, ENNReal.tsum_mul_right]
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ((∑' table, Pr[= table | sampleOtsHashTable] * liveOtsChargeAfterTable adversary parameter table ftsSecret fuel) * factor) := by
      apply ENNReal.tsum_le_tsum
      intro parameter
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      exact mul_le_mul' le_rfl (hbound parameter ftsSecret)
    _ = _ := by
      unfold sampledLiveOtsCharge
      simp only [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right, mul_assoc]
      apply tsum_congr
      intro parameter
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro table
      apply tsum_congr
      intro ftsSecret
      ring

theorem sampledNativeStartRisk_add_structuralCharge_le_directCharge
    (adversary : Adversary) (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    sampledNativeStartRisk adversary fuel q + sampledNativeStructuralCharge adversary fuel *
      ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) ≤
      sampledQueryCharge (fun secretKey => directOtsQueryCharge secretKey.parameter) adversary *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
  (sampledNativeStartRisk_add_structuralCharge_le_liveOtsCharge adversary fuel q hq).trans
    (mul_le_mul' (sampledLiveOtsCharge_le_directCharge adversary fuel) le_rfl)

theorem sampledNativeStartRisk_add_structuralCharge_add_remaining_le_refinedReserve
    (adversary : Adversary) (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    (sampledNativeStartRisk adversary fuel q + sampledNativeStructuralCharge adversary fuel *
      ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹)) +
      sampledQueryCharge remainingOtsQueryReserve adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ ≤
      sampledQueryCharge otsOpeningRefinedQueryReserve adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply (add_le_add (sampledNativeStartRisk_add_structuralCharge_le_directCharge adversary fuel q hq) le_rfl).trans_eq
  rw [← add_mul, sampled_direct_add_remaining_otsQueryReserve]

end SphincsSecurity.Concrete.OtsProbeSimulation
