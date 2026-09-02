import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveNormalizeLift

/-! Structural synchronization and target-neutrality for adaptive normalization. -/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
theorem negatedDirectDelayedComputationObserve_observerLaws
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (snapshots : List PlannedProbeSnapshot)
      (observations : List CleanProbeObservation),
      snapshots.length ≤ ordinal →
      observations.map CleanProbeObservation.toProbe =
        snapshots.map PlannedProbeSnapshot.toProbe →
      (∀ observation ∈ observations, ¬observation.ExistingHiddenHit) →
      ObserverSynchronized table
          (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
            rightRoot computation snapshots observations) ∧
        ObserverPositionNeutralAt table target
          (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
            rightRoot computation snapshots observations) := by
  intro snapshots observations hbefore haligned hclean
  induction computation using OracleComp.inductionOn generalizing snapshots observations with
  | pure value =>
      exact ⟨
        negatedDirectDelayedComputationObserve_pure_observerSynchronized ordinal parameter root
          ftsSecret table target rightRoot value snapshots observations hbefore,
        negatedDirectDelayedComputationObserve_pure_observerPositionNeutralAt ordinal parameter
          root ftsSecret table target target rightRoot value snapshots observations hbefore⟩
  | query_bind query next ih =>
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              change Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α at next
              have hnext : ∀ output,
                  ObserverSynchronized table
                      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret
                        table target rightRoot (next output) snapshots observations) ∧
                    ObserverPositionNeutralAt table target
                      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret
                        table target rightRoot (next output) snapshots observations) :=
                fun output ↦ ih output snapshots observations hbefore haligned hclean
              exact ⟨
                negatedDirectDelayedComputationObserve_uniform_observerSynchronized ordinal
                  parameter root ftsSecret table target rightRoot n next snapshots observations
                  hbefore (fun output ↦ (hnext output).1),
                negatedDirectDelayedComputationObserve_uniform_observerPositionNeutralAt ordinal
                  parameter root ftsSecret table target rightRoot target n next snapshots
                  observations hbefore (fun output ↦ (hnext output).2)⟩
          | inr input =>
              change HashOutput → OracleComp (OracleWorld + SigningSpec) α at next
              have hnext : ∀ output laterSnapshots laterObservations,
                  laterSnapshots.length ≤ ordinal →
                  laterObservations.map CleanProbeObservation.toProbe =
                    laterSnapshots.map PlannedProbeSnapshot.toProbe →
                  (∀ observation ∈ laterObservations,
                    ¬observation.ExistingHiddenHit) →
                  ObserverSynchronized table
                      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret
                        table target rightRoot (next output) laterSnapshots laterObservations) ∧
                    ObserverPositionNeutralAt table target
                      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret
                        table target rightRoot (next output) laterSnapshots laterObservations) :=
                fun output laterSnapshots laterObservations hlaterBefore hlaterAligned
                    hlaterClean ↦
                  ih output laterSnapshots laterObservations hlaterBefore hlaterAligned hlaterClean
              exact ⟨
                negatedDirectDelayedComputationObserve_hash_observerSynchronized ordinal parameter
                  root ftsSecret table target rightRoot input next snapshots observations hbefore
                  haligned hclean
                  (fun output laterSnapshots laterObservations hlaterBefore hlaterAligned
                      hlaterClean ↦
                    (hnext output laterSnapshots laterObservations hlaterBefore hlaterAligned
                      hlaterClean).1),
                negatedDirectDelayedComputationObserve_hash_observerPositionNeutralAt ordinal
                  parameter root ftsSecret table target rightRoot input next snapshots observations
                  hbefore haligned hclean
                  (fun output laterSnapshots laterObservations hlaterBefore hlaterAligned
                      hlaterClean ↦
                    (hnext output laterSnapshots laterObservations hlaterBefore hlaterAligned
                      hlaterClean).2)⟩
      | inr message =>
          change Option Signature → OracleComp (OracleWorld + SigningSpec) α at next
          have hnext : ∀ output,
              ObserverSynchronized table
                  (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table
                    target rightRoot (next output) snapshots observations) ∧
                ObserverPositionNeutralAt table target
                  (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table
                    target rightRoot (next output) snapshots observations) :=
            fun output ↦ ih output snapshots observations hbefore haligned hclean
          exact ⟨
            negatedDirectDelayedComputationObserve_signing_observerSynchronized ordinal parameter
              root ftsSecret table target rightRoot message next snapshots observations hbefore
              (fun output ↦ (hnext output).1),
            negatedDirectDelayedComputationObserve_signing_observerPositionNeutralAt ordinal
              parameter root ftsSecret table target rightRoot target message next snapshots
              observations hbefore (fun output ↦ (hnext output).2)⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
