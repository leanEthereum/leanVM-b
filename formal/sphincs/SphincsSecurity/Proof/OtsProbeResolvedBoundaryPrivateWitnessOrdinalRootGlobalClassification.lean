import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalProbability

/-!
# Sound global root classification

Guarded finalization conflates a fresh completion hit with a probe that matches a hidden value
materialized by an earlier outer query. This file keeps that distinction explicit. The ordinary
unguarded finalizer accounts for the fresh branch, while a Boolean records whether the state was
already non-completable before finalization. The latter branch is retained for the delayed-root
classification instead of being charged as fresh randomness.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

structure ObservedMaterializedDiagnostic (alpha : Type) where
  final : Option (ObservedCleanRunResult alpha)
  wasDoomed : Bool

def ObservedMaterializedDiagnostic.Bad
    (outcome : ObservedMaterializedDiagnostic alpha) : Prop :=
  outcome.final = none ∨ outcome.wasDoomed = true

def ObservedMaterializedDiagnostic.SuccessfulDoomed
    (outcome : ObservedMaterializedDiagnostic alpha) : Prop :=
  outcome.final.isSome = true ∧ outcome.wasDoomed = true

theorem probEvent_diagnosticBad_le_finalNone_add_successfulDoomed
    (run : ProbComp (ObservedMaterializedDiagnostic alpha)) :
    Pr[ObservedMaterializedDiagnostic.Bad | run] ≤
      Pr[fun outcome => outcome.final = none | run] +
        Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed | run] := by
  calc
    _ ≤ Pr[fun outcome => outcome.final = none ∨
          outcome.SuccessfulDoomed | run] := by
      apply probEvent_mono
      intro outcome _ hbad
      rcases hbad with hnone | hdoomed
      · exact Or.inl hnone
      · cases hfinal : outcome.final with
        | none => exact Or.inl rfl
        | some result => exact Or.inr ⟨by simp [hfinal], hdoomed⟩
    _ ≤ _ := probEvent_or_le _ _ _

noncomputable def finishObservedMaterializedDiagnostic
    (table : OtsSecretIndex → HashOutput)
    (result : Option (ObservedCleanRunResult alpha)) :
    ProbComp (ObservedMaterializedDiagnostic alpha) := by
  classical
  match result with
  | none => exact pure ⟨none, false⟩
  | some result =>
      exact do
        let final ← finishObservedCleanRunFromTable (some result)
        pure ⟨final,
          decide (¬DeferredCompletable table (directDeferredContext result.state))⟩

noncomputable def sampledObservedMaterializedDiagnostic
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (ObservedMaterializedDiagnostic
      (RetainedGameResult × SplitHashCache)) := do
  let table ← sampleOtsHashTable
  let result ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table
  finishObservedMaterializedDiagnostic table result

def ObservedMaterializedDiagnostic.project
    (outcome : ObservedMaterializedDiagnostic alpha) :
    Option (CleanRunResult alpha) :=
  projectObservedCleanRun outcome.final

theorem map_project_finishObservedMaterializedDiagnostic
    (table : OtsSecretIndex → HashOutput)
    (result : Option (ObservedCleanRunResult alpha)) :
    ObservedMaterializedDiagnostic.project <$>
        finishObservedMaterializedDiagnostic table result =
      finishCleanRunFromTable (projectObservedCleanRun result) := by
  classical
  cases result with
  | none =>
      simp [finishObservedMaterializedDiagnostic,
        ObservedMaterializedDiagnostic.project, projectObservedCleanRun,
        finishCleanRunFromTable]
  | some result =>
      unfold finishObservedMaterializedDiagnostic
      rw [map_bind]
      calc
        _ = projectObservedCleanRun <$>
            finishObservedCleanRunFromTable (some result) := by
          apply bind_congr
          intro final
          rfl
        _ = _ := map_projectObservedCleanRun_finishObservedCleanRunFromTable (some result)

set_option maxRecDepth 100000 in
theorem map_project_sampledObservedMaterializedDiagnostic
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ObservedMaterializedDiagnostic.project <$>
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel =
      sampledMaterializedCleanUnguarded adversary parameter ftsSecret fuel := by
  unfold sampledObservedMaterializedDiagnostic sampledMaterializedCleanUnguarded
  rw [map_bind]
  apply bind_congr
  intro table
  rw [map_bind]
  calc
    _ = observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table >>=
        fun result => finishCleanRunFromTable (projectObservedCleanRun result) := by
      apply bind_congr
      intro result
      exact map_project_finishObservedMaterializedDiagnostic table result
    _ = (projectObservedCleanRun <$>
          observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table) >>=
        finishCleanRunFromTable := by
      rw [map_eq_bind_pure_comp, bind_assoc]
      apply bind_congr
      intro result
      rfl
    _ = _ := by
      rw [map_projectObservedCleanRun_observedMaterializedRetainedRunFromTable]

theorem probEvent_sampledObservedMaterializedDiagnostic_final_none_eq
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun outcome => outcome.final = none |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] =
      Pr[= none | sampledMaterializedCleanUnguarded adversary parameter ftsSecret fuel] := by
  calc
    _ = Pr[= none | ObservedMaterializedDiagnostic.project <$>
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] := by
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      exact OracleComp.probEvent_congr' (fun outcome _ => by
        rcases outcome with ⟨final, doomed⟩
        cases final <;>
          simp [ObservedMaterializedDiagnostic.project, projectObservedCleanRun]) rfl
    _ = _ := OracleComp.probOutput_congr rfl
      (congrArg evalDist
        (map_project_sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel))

theorem probEvent_sampledObservedMaterializedDiagnostic_final_none_le
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (hbudget : q ≤ fuel) :
    Pr[fun outcome => outcome.final = none |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] ≤
      (fuel : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  rw [probEvent_sampledObservedMaterializedDiagnostic_final_none_eq]
  exact probEvent_sampledMaterializedCleanUnguarded_none_le_of_fuel adversary parameter
    ftsSecret fuel q hbound hbudget

def SnapshotObservedDiagnosticRootRel
    (source : PrivateWitnessSnapshotOutput)
    (outcome : ObservedMaterializedDiagnostic
      (RetainedGameResult × SplitHashCache)) : Prop :=
  outcome.Bad ∨
    (WitnessFirstUsesSomeLayerRoot (erasePrivateWitnessSnapshotOutput source) →
      WitnessFirstUsesSomeDelayedLayerRootSnapshot source)

set_option maxRecDepth 100000 in
theorem relTriple_pure_finishObservedDiagnostic_of_rootOrDoomed
    (table : OtsSecretIndex → HashOutput)
    (source : PrivateWitnessSnapshotOutput)
    (observed : Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)))
    (hrelation : SnapshotObservedRootOrDoomedRel table source observed) :
    RelTriple
      (pure source : ProbComp PrivateWitnessSnapshotOutput)
      (finishObservedMaterializedDiagnostic table observed)
      SnapshotObservedDiagnosticRootRel := by
  rcases hrelation with hfailed | hsuccess | hdoomed
  · subst observed
    simp [finishObservedMaterializedDiagnostic, SnapshotObservedDiagnosticRootRel,
      ObservedMaterializedDiagnostic.Bad]
  · obtain ⟨result, hresult, himplication⟩ := hsuccess
    subst observed
    have hbase := relTriple_true
      (pure source : ProbComp PrivateWitnessSnapshotOutput)
      (finishObservedCleanRunFromTable (some result))
    have hleft :=
      SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
        (fun output => output = source) (by intro output houtput; simpa using houtput)
    have hboth :=
      SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
    apply relTriple_bind hboth
    intro left final hfinal
    have hleftEq : left = source := hfinal.1.2
    subst left
    apply relTriple_pure_pure
    cases final with
    | none =>
        left
        left
        rfl
    | some finalResult =>
        right
        exact himplication
  · obtain ⟨result, hresult, hnotCompletable⟩ := hdoomed
    subst observed
    have hbase := relTriple_true
      (pure source : ProbComp PrivateWitnessSnapshotOutput)
      (finishObservedCleanRunFromTable (some result))
    apply relTriple_bind hbase
    intro _ final _
    apply relTriple_pure_pure
    left
    right
    simp [hnotCompletable]

set_option maxRecDepth 100000 in
theorem relTriple_finishObservedDiagnostic_of_rootOrDoomed
    (table : OtsSecretIndex → HashOutput)
    (source : ProbComp PrivateWitnessSnapshotOutput)
    (observed : ProbComp (Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))))
    (hrelation : RelTriple source observed (SnapshotObservedRootOrDoomedRel table)) :
    RelTriple source
      (observed >>= finishObservedMaterializedDiagnostic table)
      SnapshotObservedDiagnosticRootRel := by
  have hbound := relTriple_bind hrelation fun sourceOutput observedOutput houtput =>
    relTriple_pure_finishObservedDiagnostic_of_rootOrDoomed table sourceOutput observedOutput
      houtput
  simpa using hbound

end SphincsSecurity.Concrete.OtsProbeSimulation
