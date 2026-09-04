import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionNormalize

/-!
# Common production normalization through the public root

The local sampler normalization is lifted through the probe-free public-root computation. This
gives one target-specific resolved experiment whose only remaining target dependence is the single
deferred position resolution.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def sampledHighInstalledPermissiveRootAwareSelectionExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (Digest × Option Probe) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure (0, none)
  | some result =>
      sampledHighInstalledPermissiveRootAwareSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target result

noncomputable def resolvedInstalledPermissiveRootAwareSelectionExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (Digest × Option Probe) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure (0, none)
  | some result =>
      resolvedInstalledPermissiveRootAwareSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target result

set_option maxRecDepth 100000 in
theorem evalDist_sampledHighInstalledPermissiveExperiment_eq_resolved
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    evalDist
        (sampledHighInstalledPermissiveRootAwareSelectionExperimentAfterTable ordinal adversary
          parameter ftsSecret target fuel table) =
      evalDist
        (resolvedInstalledPermissiveRootAwareSelectionExperimentAfterTable ordinal adversary
          parameter ftsSecret target fuel table) := by
  unfold sampledHighInstalledPermissiveRootAwareSelectionExperimentAfterTable
    resolvedInstalledPermissiveRootAwareSelectionExperimentAfterTable
  apply evalDist_bind_congr
  intro rootResult hresult
  cases rootResult with
  | none => rfl
  | some rootResult =>
      exact evalDist_sampledHighInstalledPermissive_eq_resolved_afterRootResult ordinal adversary
        parameter ftsSecret target hroot hparent fuel table rootResult hresult

theorem probEvent_sampledHighInstalledPermissiveExperiment_eq_resolved
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
        sampledHighInstalledPermissiveRootAwareSelectionExperimentAfterTable ordinal adversary
          parameter ftsSecret target fuel table] =
      Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
        resolvedInstalledPermissiveRootAwareSelectionExperimentAfterTable ordinal adversary
          parameter ftsSecret target fuel table] := by
  apply OracleComp.probEvent_congr' (fun _ _ ↦ Iff.rfl)
  exact evalDist_sampledHighInstalledPermissiveExperiment_eq_resolved ordinal adversary parameter
    ftsSecret target hroot hparent fuel table

theorem probEvent_materializedRootAwareProduction_le_resolvedPermissive
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
        materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
          ftsSecret target fuel table] ≤
      Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
        resolvedInstalledPermissiveRootAwareSelectionExperimentAfterTable ordinal adversary
          parameter ftsSecret target fuel table] := by
  calc
    _ ≤ Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
          sampledHighInstalledPermissiveRootAwareSelectionExperimentAfterTable ordinal adversary
            parameter ftsSecret target fuel table] := by
      unfold materializedRootAwareOrdinalProductionExperimentAfterTable
        sampledHighInstalledPermissiveRootAwareSelectionExperimentAfterTable
      apply probEvent_bind_le_bind_of_forall_le
      intro rootResult hresult
      cases rootResult with
      | none => simp [materializedOrdinalSelectionAt]
      | some rootResult =>
          exact probEvent_materializedRootAwareProduction_le_installedPermissive ordinal adversary
            parameter ftsSecret target rootResult
    _ = _ := probEvent_sampledHighInstalledPermissiveExperiment_eq_resolved ordinal adversary
      parameter ftsSecret target hroot hparent fuel table

theorem probEvent_successfulDoomedFirstRootFiber_le_two_mul_resolvedPermissive
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (hordinal : ordinal < q)
    (hfuel : 2 * q < Fintype.card Digest)
    (hbound : ∀ root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[fun observed =>
        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
          table ordinal target observed |
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
          resolvedInstalledPermissiveRootAwareSelectionExperimentAfterTable ordinal adversary
            parameter ftsSecret target (2 * q) table] *
        (2 * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  calc
    _ ≤ Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
          materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target (2 * q) table] *
        (2 * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :=
      probEvent_successfulDoomedFirstRootFiber_le_two_mul_production ordinal adversary parameter
        table ftsSecret q target hroot hparent hordinal hfuel hbound hq
    _ ≤ _ := by
      gcongr
      exact probEvent_materializedRootAwareProduction_le_resolvedPermissive ordinal adversary
        parameter ftsSecret target hroot hparent (2 * q) table

end SphincsSecurity.Concrete.OtsProbeSimulation
