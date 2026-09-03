import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceProbability
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalNonRootRisk

/-!
# Canonical source non-root probability

Erasing snapshot contexts from the canonical source gives the existing witness-plan observer.
Its first non-root witness at a fixed ordinal is bounded by the candidate-time non-root monitor.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot
set_option linter.constructorNameAsVariable false

noncomputable def granularAllCanonicalPrivateWitnessPlan
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp PrivateWitnessPlanOutput :=
  runDirectWitnessPlanObserve
    (canonicalizeDirectWitnessPlanObserve table
      (granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
        ftsSecret))
    [] emptyWitnessDeferredContext fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache)

theorem map_erase_granularAllCanonicalPrivateWitnessSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    erasePrivateWitnessSnapshotOutput <$>
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel =
      granularAllCanonicalPrivateWitnessPlan adversary parameter table ftsSecret fuel := by
  unfold granularAllCanonicalPrivateWitnessSnapshot granularAllCanonicalPrivateWitnessPlan
  apply map_erase_runDirectWitnessSnapshotObserve
  intro context remaining value snapshots
  apply map_erase_canonicalizeDirectWitnessSnapshotObserve
  intro nextContext nextRemaining nextValue nextSnapshots
  exact map_erase_granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary
    parameter table ftsSecret nextContext nextRemaining nextValue nextSnapshots

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_granularAllCanonicalPlan_firstUsesNonRootOrdinal_le
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
        granularAllCanonicalPrivateWitnessPlan adversary parameter table ftsSecret fuel] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[fun hit : Bool => hit = true |
        granularAllCanonicalPrivateOrdinalNonRootRisk ordinal adversary parameter table ftsSecret
          fuel] := by
      unfold granularAllCanonicalPrivateWitnessPlan
        granularAllCanonicalPrivateOrdinalNonRootRisk
      apply probEvent_runDirectWitnessPlanFirstUsesNonRootOrdinal_le_risk ordinal _ _ []
        emptyWitnessDeferredContext fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache) (by simp)
      intro result hresult
      apply probEvent_canonicalizeWitnessPlanFirstUsesNonRootOrdinal_le_risk table ordinal _ _
        result.context result.remaining result.value [] (by simp)
      dsimp only
      intro _hprivate hpublished _hcompletable
      have hdetailed : DirectDetailedResult.done result ∈ support
          (runDirectResolvedDetailedFromTable emptyWitnessDeferredContext fuel table
            (maskedPublishedTreeRoot.run emptySplitHashCache)) := by
        rw [← map_erase_runDirectResolvedWitnessFromTable
          (maskedPublishedTreeRoot.run emptySplitHashCache) emptyWitnessDeferredContext fuel table,
          support_map]
        exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
      have hcore := resolvedCore_of_done_runDirectResolvedDetailedFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache) emptyWitnessDeferredContext fuel table
        result DeferredContext.valid_empty.valuesConsistent (startTableAgrees_empty table) hdetailed
      exact probEvent_granularDetailedRetainedRestWitnessFirstUsesNonRootOrdinal_le_nonRootRisk
        adversary parameter table ftsSecret ordinal
        (canonicalizeMaterializedValues table result.context) result.remaining result.value []
        (by simp) (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
        (canonicalizeMaterializedValues_startTableAgrees table result.context)
        hpublished.to_canonicalizedMaterializedValues
    _ ≤ _ := probEvent_granularAllCanonicalPrivateOrdinalNonRootRisk_le ordinal adversary
      parameter table ftsSecret fuel

theorem probEvent_granularAllCanonicalSnapshot_firstUsesNonRootOrdinal_le
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun output => WitnessFirstUsesNonLayerRootOrdinal ordinal
          (erasePrivateWitnessSnapshotOutput output) |
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ = Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
        erasePrivateWitnessSnapshotOutput <$>
          granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel] := by
      rw [probEvent_map]
      exact OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) rfl
    _ = Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
        granularAllCanonicalPrivateWitnessPlan adversary parameter table ftsSecret fuel] :=
      OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
        (congrArg evalDist
          (map_erase_granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret
            fuel))
    _ ≤ _ := probEvent_granularAllCanonicalPlan_firstUsesNonRootOrdinal_le ordinal adversary
      parameter table ftsSecret fuel

theorem probEvent_sampledCanonical_firstUsesNonRootOrdinal_le
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun output => WitnessFirstUsesNonLayerRootOrdinal ordinal
          (erasePrivateWitnessSnapshotOutput output) |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret fuel] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot
  apply probEvent_bind_le_of_forall_le
  intro table _htable
  exact probEvent_granularAllCanonicalSnapshot_firstUsesNonRootOrdinal_le ordinal adversary
    parameter table ftsSecret fuel

theorem probEvent_sampledCanonical_nonRoot_le_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    Pr[fun output => WitnessFirstUsesSomeNonLayerRoot
          (erasePrivateWitnessSnapshotOutput output) |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
      (q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
  probEvent_sampledCanonical_nonRoot_le_mul_of_ordinals adversary parameter ftsSecret q hbound
    (fun ordinal => probEvent_sampledCanonical_firstUsesNonRootOrdinal_le ordinal.val adversary
      parameter ftsSecret q)

end SphincsSecurity.Concrete.OtsProbeSimulation
