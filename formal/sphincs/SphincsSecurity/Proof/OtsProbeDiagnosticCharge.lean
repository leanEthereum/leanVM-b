import SphincsSecurity.Proof.OtsProbeMaterializedCharge
import SphincsSecurity.Proof.OtsProbeJointClassification
import SphincsSecurity.Proof.OtsProbeJointSnapshotErasure

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def materializedRetainedCharge (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ℝ≥0∞ :=
  ordinaryContinuationCharge
    (fun context remaining value => materializedBoundaryCharge parameter value.1 ftsSecret
      (retainedGameRestComputation adversary ⟨value.1, parameter⟩) context.state remaining value.2)
    (maskedPublishedTreeRoot.run emptySplitHashCache) emptyWitnessDeferredContext fuel

theorem probEvent_sampledMaterializedCleanUnguarded_none_le_charge
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hbudget : q ≤ fuel) :
    Pr[= none | sampledMaterializedCleanUnguarded adversary parameter ftsSecret fuel] ≤
      materializedRetainedCharge adversary parameter ftsSecret fuel * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ = Pr[= true | Option.isNone <$>
        sampledMaterializedCleanUnguarded adversary parameter ftsSecret fuel] := by
      rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map]
      exact OracleComp.probEvent_congr' (fun result _ => by cases result <;> simp) rfl
    _ = Pr[= true | runDirectDetailedSafeOrdinaryWithCompletionTable
        (fun table context remaining value => guardedMaterializedRootContinuation adversary parameter ftsSecret q
          table context.state remaining value)
        emptyWitnessDeferredContext fuel (maskedPublishedTreeRoot.run emptySplitHashCache)] :=
      OracleComp.probOutput_congr rfl
        (evalDist_sampledMaterializedCleanUnguarded_isNone_eq_safeRoot_of_fuel adversary parameter ftsSecret fuel q hbudget)
    _ ≤ _ := by
      rw [← probEvent_eq_eq_probOutput]
      have hsafe := probEvent_safeOrdinary_le_continuationCharge
        (maskedPublishedTreeRoot.run emptySplitHashCache)
        (fun table context remaining value => guardedMaterializedRootContinuation adversary parameter ftsSecret q
          table context.state remaining value)
        (fun context remaining value => materializedBoundaryCharge parameter value.1 ftsSecret
          (retainedGameRestComputation adversary ⟨value.1, parameter⟩) context.state remaining value.2)
        (by
          intro context remaining value
          rw [probEvent_eq_eq_probOutput]
          by_cases hguard : PublishedValues context.state ∧ q ≤ remaining
          · simpa [guardedMaterializedRootContinuation, hguard, sampledMaterializedCleanBoundaryFailure] using
              (probEvent_sampledMaterializedCleanBoundaryFailure_le_charge parameter value.1 ftsSecret
                (retainedGameRestComputation adversary ⟨value.1, parameter⟩) context.state remaining q value.2
                (fun table _ => hbound table value.1) hguard.2 hguard.1)
          · simp [guardedMaterializedRootContinuation, hguard])
        emptyWitnessDeferredContext fuel
      simpa only [materializedRetainedCharge, emptyWitnessDeferredContext, LazyRevealProbe.State.empty,
        LazyRevealProbe.State.unmaterializedPending, Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
        add_zero] using hsafe

theorem probEvent_sampledDiagnostic_final_none_le_charge
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hbudget : q ≤ fuel) :
    Pr[fun outcome => outcome.final = none | sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] ≤
      materializedRetainedCharge adversary parameter ftsSecret fuel * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [probEvent_sampledObservedMaterializedDiagnostic_final_none_eq]
  exact probEvent_sampledMaterializedCleanUnguarded_none_le_charge adversary parameter ftsSecret fuel q hbound hbudget

theorem probEvent_sampledDiagnostic_bad_le_charge_add_successfulDoomed
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hbudget : q ≤ fuel) :
    Pr[ObservedMaterializedDiagnostic.Bad | sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] ≤
      materializedRetainedCharge adversary parameter ftsSecret fuel * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed |
          sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] :=
  (probEvent_diagnosticBad_le_finalNone_add_successfulDoomed _).trans
    (add_le_add (probEvent_sampledDiagnostic_final_none_le_charge adversary parameter ftsSecret fuel q hbound hbudget) le_rfl)

theorem probEvent_sampledActualRetained_verifyProbe_le_charge_add_hiddenFailures
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
      materializedRetainedCharge adversary parameter ftsSecret (2 * q) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed |
          sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] +
        Pr[JointSnapshotResidual | sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q] :=
  (probEvent_sampledActualRetained_verifyProbe_le_jointBoundaryFailed adversary parameter ftsSecret q).trans
    ((probEvent_sampledJointSnapshot_failed_le_diagnostic_add_residual adversary parameter ftsSecret q hbound).trans
      (add_le_add (probEvent_sampledDiagnostic_bad_le_charge_add_successfulDoomed
        adversary parameter ftsSecret (2 * q) q hbound (by omega)) le_rfl))

theorem probEvent_sampledActualRetained_verifyProbe_le_charge_add_hiddenFailures_of_hashQueryBound
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
      materializedRetainedCharge adversary parameter ftsSecret (2 * q) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed |
          sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] +
        Pr[JointSnapshotResidual | sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q] :=
  probEvent_sampledActualRetained_verifyProbe_le_charge_add_hiddenFailures adversary parameter ftsSecret q
    (fun table root => isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hparameter table ftsSecret hfts root)

end SphincsSecurity.Concrete.OtsProbeSimulation
