import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionOrdinal

/-!
# Source-side ordinal aggregation

The delayed layer-root and non-root residuals are both indexed by the first source candidate used
by the retained private witness. Supported canonical sources contain at most `q` candidates, so
fixed-ordinal estimates sum over `Fin q` without a structural-position union.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot
set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledCanonical_delayed_le_sum_ordinals
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q) :
    Pr[WitnessFirstUsesSomeDelayedLayerRootSnapshot |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
      ∑ ordinal : Fin q,
        Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal.val |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] := by
  classical
  calc
    _ ≤ Pr[fun output => ∃ ordinal ∈ (Finset.univ : Finset (Fin q)),
          WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal.val output |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] := by
      apply probEvent_mono
      intro (output : PrivateWitnessSnapshotOutput) houtput hdelayed
      unfold sampledGranularAllCanonicalPrivateWitnessSnapshot at houtput
      rw [mem_support_bind_iff] at houtput
      obtain ⟨table, _htable, hrest⟩ := houtput
      have hlength : output.2.length ≤ q :=
        snapshots_length_le_of_mem_granularAllCanonical
          (adversary := adversary) (parameter := parameter) (table := table)
          (ftsSecret := ftsSecret) (q := q) (hbound := hbound table) (output := output)
          (houtput := hrest)
      obtain ⟨ordinal, witness, sourceOrdinal, hwitness, hordinal, hfirst, hroot,
        hstate, hrevealed, hvalue⟩ := hdelayed
      have hlt : ordinal < q := by
        rw [← hordinal]
        exact sourceOrdinal.isLt.trans_le hlength
      let bounded : Fin q := ⟨ordinal, hlt⟩
      exact ⟨bounded, Finset.mem_univ bounded, witness, sourceOrdinal, hwitness,
        hordinal, hfirst, hroot, hstate, hrevealed, hvalue⟩
    _ ≤ ∑ ordinal ∈ (Finset.univ : Finset (Fin q)),
          Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal.val |
            sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] :=
      probEvent_exists_finset_le_sum Finset.univ
        (sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q)
        (fun (ordinal : Fin q) (output : PrivateWitnessSnapshotOutput) =>
          WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal.val output)
    _ = _ := by simp

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledCanonical_delayed_le_mul_of_ordinals
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hordinal : ∀ ordinal : Fin q,
      Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal.val |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[WitnessFirstUsesSomeDelayedLayerRootSnapshot |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
      (q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ ∑ ordinal : Fin q,
        Pr[WitnessFirstUsesDelayedLayerRootSnapshotOrdinal ordinal.val |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] :=
      probEvent_sampledCanonical_delayed_le_sum_ordinals adversary parameter ftsSecret q hbound
    _ ≤ ∑ _ordinal : Fin q, ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      exact Finset.sum_le_sum fun ordinal _ => hordinal ordinal
    _ = _ := by simp

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledCanonical_nonRoot_le_sum_ordinals
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q) :
    Pr[fun output => WitnessFirstUsesSomeNonLayerRoot
          (erasePrivateWitnessSnapshotOutput output) |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
      ∑ ordinal : Fin q,
        Pr[fun output => WitnessFirstUsesNonLayerRootOrdinal ordinal.val
            (erasePrivateWitnessSnapshotOutput output) |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] := by
  classical
  calc
    _ ≤ Pr[fun output => ∃ ordinal ∈ (Finset.univ : Finset (Fin q)),
          WitnessFirstUsesNonLayerRootOrdinal ordinal.val
            (erasePrivateWitnessSnapshotOutput output) |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] := by
      apply probEvent_mono
      intro (output : PrivateWitnessSnapshotOutput) houtput hnonRoot
      unfold sampledGranularAllCanonicalPrivateWitnessSnapshot at houtput
      rw [mem_support_bind_iff] at houtput
      obtain ⟨table, _htable, hrest⟩ := houtput
      have hlength : output.2.length ≤ q :=
        snapshots_length_le_of_mem_granularAllCanonical
          (adversary := adversary) (parameter := parameter) (table := table)
          (ftsSecret := ftsSecret) (q := q) (hbound := hbound table) (output := output)
          (houtput := hrest)
      obtain ⟨ordinal, witness, sourceOrdinal, hwitness, hordinal, hfirst, hroot⟩ :=
        hnonRoot
      have herasedLength :
          (erasePrivateWitnessSnapshotOutput output).2.length = output.2.length := by
        simp [erasePrivateWitnessSnapshotOutput]
      have hlt : ordinal < q := by
        rw [← hordinal]
        have hsourceLt : sourceOrdinal.val < output.2.length := by
          simpa only [herasedLength] using sourceOrdinal.isLt
        exact hsourceLt.trans_le hlength
      let bounded : Fin q := ⟨ordinal, hlt⟩
      exact ⟨bounded, Finset.mem_univ bounded, witness, sourceOrdinal, hwitness,
        hordinal, hfirst, hroot⟩
    _ ≤ ∑ ordinal ∈ (Finset.univ : Finset (Fin q)),
          Pr[fun output => WitnessFirstUsesNonLayerRootOrdinal ordinal.val
              (erasePrivateWitnessSnapshotOutput output) |
            sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] :=
      probEvent_exists_finset_le_sum Finset.univ
        (sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q)
        (fun (ordinal : Fin q) (output : PrivateWitnessSnapshotOutput) =>
          WitnessFirstUsesNonLayerRootOrdinal ordinal.val
          (erasePrivateWitnessSnapshotOutput output))
    _ = _ := by simp

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledCanonical_nonRoot_le_mul_of_ordinals
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hordinal : ∀ ordinal : Fin q,
      Pr[fun output => WitnessFirstUsesNonLayerRootOrdinal ordinal.val
            (erasePrivateWitnessSnapshotOutput output) |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[fun output => WitnessFirstUsesSomeNonLayerRoot
          (erasePrivateWitnessSnapshotOutput output) |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
      (q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ ∑ ordinal : Fin q,
        Pr[fun output => WitnessFirstUsesNonLayerRootOrdinal ordinal.val
            (erasePrivateWitnessSnapshotOutput output) |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] :=
      probEvent_sampledCanonical_nonRoot_le_sum_ordinals adversary parameter ftsSecret q hbound
    _ ≤ ∑ _ordinal : Fin q, ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      exact Finset.sum_le_sum fun ordinal _ => hordinal ordinal
    _ = _ := by simp

end SphincsSecurity.Concrete.OtsProbeSimulation
