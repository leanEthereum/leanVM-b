import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedRootClosed

/-!
# Canonical private-witness assembly

The canonical witness source is covered by its recorded candidates. Splitting its first witness
between layer roots and all other structural positions combines the diagnostic, delayed-root and
non-root estimates.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible]
  maskedPublishedTreeRoot sampledGranularAllCanonicalPrivateWitnessSnapshot
  granularAllCanonicalPrivateWitnessSnapshot
set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem privateWitnessCovered_of_mem_granularAllCanonicalPlan
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (output : PrivateWitnessPlanOutput)
    (houtput : output ∈ support
      (granularAllCanonicalPrivateWitnessPlan adversary parameter table ftsSecret fuel)) :
    PrivateWitnessCovered output := by
  unfold granularAllCanonicalPrivateWitnessPlan at houtput
  apply privateWitnessCovered_of_mem_runDirectWitnessPlanObserve _ []
    emptyWitnessDeferredContext fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  · simp [PendingCoveredBy, emptyWitnessDeferredContext, LazyRevealProbe.State.empty]
  · exact OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe [])
      (maskedPublishedTreeRoot_probeFree emptySplitHashCache)
  · intro result _hresult hcovered nextOutput hnextOutput
    apply privateWitnessCovered_of_mem_canonicalizeDirectWitnessPlanObserve table _
      result.context result.remaining result.value [] hcovered
      (output := nextOutput) (houtput := hnextOutput)
    intro finalOutput hfinalOutput
    have hcanonicalCovered : PendingCoveredBy []
        (canonicalizeMaterializedValues table result.context) :=
      (pendingCoveredBy_canonicalize_iff table [] result.context).2 hcovered
    exact privateWitnessCovered_of_mem_granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve
      adversary parameter table ftsSecret (canonicalizeMaterializedValues table result.context)
      result.remaining result.value [] hcanonicalCovered finalOutput hfinalOutput
  · exact houtput

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem privateWitnessCovered_erase_of_mem_sampledGranularAllCanonical
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret fuel)) :
    PrivateWitnessCovered (erasePrivateWitnessSnapshotOutput output) := by
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨table, _htable, hfixed⟩ := houtput
  have herased : erasePrivateWitnessSnapshotOutput output ∈ support
      (granularAllCanonicalPrivateWitnessPlan adversary parameter table ftsSecret fuel) := by
    rw [← map_erase_granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
      ftsSecret fuel, support_map]
    exact ⟨output, hfixed, rfl⟩
  exact privateWitnessCovered_of_mem_granularAllCanonicalPlan adversary parameter table ftsSecret
    fuel (erasePrivateWitnessSnapshotOutput output) herased

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_sampledCanonical_privateWitness_le_eight_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hexpanded : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[fun output => output.1.isSome = true |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
      ((8 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let diagnostic := sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)
  have hfuel : 2 * q < Fintype.card Digest := by
    rw [show Fintype.card Digest = 2 ^ digestBits by simp]
    norm_num [securityBits, digestBits] at hq ⊢
    omega
  have hdiagnostic :
      Pr[fun outcome => outcome.final = none | diagnostic] +
          Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed | diagnostic] ≤
        ((5 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
    calc
      _ ≤ ((2 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
          ((3 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
        apply add_le_add
        · exact probEvent_sampledObservedMaterializedDiagnostic_final_none_le adversary
            parameter ftsSecret (2 * q) q hexpanded (by omega)
        · exact probEvent_sampledDiagnostic_successfulDoomed_le_three_mul adversary parameter
            ftsSecret q hfuel hexpanded hq
      _ = _ := by
        push_cast
        ring
  have hsplit :
      Pr[fun output => output.1.isSome = true |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
        Pr[fun output => WitnessFirstUsesSomeLayerRoot
            (erasePrivateWitnessSnapshotOutput output) |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] +
          Pr[fun output => WitnessFirstUsesSomeNonLayerRoot
            (erasePrivateWitnessSnapshotOutput output) |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] := by
    calc
      _ ≤ Pr[fun output =>
            WitnessFirstUsesSomeLayerRoot (erasePrivateWitnessSnapshotOutput output) ∨
            WitnessFirstUsesSomeNonLayerRoot (erasePrivateWitnessSnapshotOutput output) |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] := by
        apply probEvent_mono
        intro output houtput hwitness
        have hcovered : PrivateWitnessCovered (erasePrivateWitnessSnapshotOutput output) := by
          apply privateWitnessCovered_erase_of_mem_sampledGranularAllCanonical
            (adversary := adversary) (parameter := parameter) (ftsSecret := ftsSecret)
            (fuel := q) (output := output)
          exact houtput
        have herased : (erasePrivateWitnessSnapshotOutput output).1.isSome = true := by
          simpa [erasePrivateWitnessSnapshotOutput] using hwitness
        exact witnessFirstUsesSome_root_or_nonRoot hcovered herased
      _ ≤ _ := probEvent_or_le _ _ _
  calc
    _ ≤ Pr[fun output => WitnessFirstUsesSomeLayerRoot
          (erasePrivateWitnessSnapshotOutput output) |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] +
        Pr[fun output => WitnessFirstUsesSomeNonLayerRoot
          (erasePrivateWitnessSnapshotOutput output) |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] := hsplit
    _ ≤ (Pr[fun outcome => outcome.final = none | diagnostic] +
          Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed | diagnostic] +
          Pr[WitnessFirstUsesSomeDelayedLayerRootSnapshot |
            sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q]) +
        Pr[fun output => WitnessFirstUsesSomeNonLayerRoot
          (erasePrivateWitnessSnapshotOutput output) |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] := by
      gcongr
      exact probEvent_sampledCanonical_root_le_diagnostic adversary parameter ftsSecret q
        hexpanded
    _ ≤ (((5 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
          (2 * q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) +
        (q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      apply add_le_add
      · apply add_le_add
        · exact hdiagnostic
        · exact probEvent_sampledCanonical_delayed_le_two_mul_closed adversary parameter
            ftsSecret q hexpanded hq
      · exact probEvent_sampledCanonical_nonRoot_le_mul adversary parameter ftsSecret q hexpanded
    _ = _ := by
      push_cast
      ring

end SphincsSecurity.Concrete.OtsProbeSimulation
