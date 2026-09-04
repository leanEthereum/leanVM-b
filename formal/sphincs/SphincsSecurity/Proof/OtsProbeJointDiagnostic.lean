import SphincsSecurity.Proof.OtsProbeCouplingObservation

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option linter.constructorNameAsVariable false

/-- A successful comparison preserves the witness chronology and rules out ordinary source failure. -/
def BoundarySnapshotDiagnosticRel
    (table : OtsSecretIndex → HashOutput)
    (source : BoundaryWitnessSnapshotOutput)
    (diagnostic : ObservedMaterializedDiagnostic α) : Prop :=
  diagnostic.Bad ∨
    (∃ result aligned, diagnostic.before = some result ∧
      aligned <+: result.observations ∧
      SnapshotsObservedAt table source.witnessSnapshot.2 aligned ∧
      (∀ witness, source.witnessSnapshot.1 = some witness →
        result.state.values (.position witness.position) = some witness.output)) ∧
    (source.outcome.failed = true → source.witnessSnapshot.1.isSome = true)

theorem relTriple_any_finishDiagnostic_none
    (table : OtsSecretIndex → HashOutput) (source : ProbComp BoundaryWitnessSnapshotOutput) :
    RelTriple source
      (finishObservedMaterializedDiagnostic table
        (none : Option (ObservedCleanRunResult α)))
      (BoundarySnapshotDiagnosticRel table) := by
  apply relTriple_post_mono
    (SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support
      (relTriple_true source (finishObservedMaterializedDiagnostic table none)))
  intro left right hrelation
  have heq : right = ⟨none, none, false⟩ := by
    simpa [finishObservedMaterializedDiagnostic] using hrelation.2
  subst right
  exact Or.inl (Or.inl rfl)

theorem relTriple_any_finishDiagnostic_doomed
    (table : OtsSecretIndex → HashOutput) (source : ProbComp BoundaryWitnessSnapshotOutput)
    (result : ObservedCleanRunResult α)
    (hdoomed : ¬DeferredCompletable table (directDeferredContext result.state)) :
    RelTriple source (finishObservedMaterializedDiagnostic table (some result))
      (BoundarySnapshotDiagnosticRel table) := by
  classical
  have hbase := relTriple_true source (finishObservedCleanRunFromTable (some result))
  have hstep := relTriple_bind hbase (fun left final _ =>
    relTriple_pure_pure (R := BoundarySnapshotDiagnosticRel table)
      (a := left)
      (b := ⟨some result, final, decide
        (¬DeferredCompletable table (directDeferredContext result.state))⟩)
      (Or.inl (Or.inr (by simp [hdoomed]))))
  simpa [finishObservedMaterializedDiagnostic] using hstep

theorem relTriple_pure_finishDiagnostic_aligned
    (table : OtsSecretIndex → HashOutput) (source : BoundaryWitnessSnapshotOutput)
    (result : ObservedCleanRunResult α) (aligned : List CleanProbeObservation)
    (hprefix : aligned <+: result.observations)
    (haligned : SnapshotsObservedAt table source.witnessSnapshot.2 aligned)
    (hstored : ∀ witness, source.witnessSnapshot.1 = some witness →
      result.state.values (.position witness.position) = some witness.output)
    (hprivate : source.outcome.failed = true → source.witnessSnapshot.1.isSome = true) :
    RelTriple (pure source : ProbComp BoundaryWitnessSnapshotOutput)
      (finishObservedMaterializedDiagnostic table (some result))
      (BoundarySnapshotDiagnosticRel table) := by
  classical
  have hbase := relTriple_true (pure source : ProbComp BoundaryWitnessSnapshotOutput)
    (finishObservedCleanRunFromTable (some result))
  have hleft := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
    (fun output => output = source) (by intro output houtput; simpa using houtput)
  have hstep := relTriple_bind hleft (fun left final hleft => by
    have heq : left = source := hleft.2
    subst left
    apply relTriple_pure_pure (R := BoundarySnapshotDiagnosticRel table)
      (a := source) (b := ⟨some result, final, decide
        (¬DeferredCompletable table (directDeferredContext result.state))⟩)
    exact Or.inr ⟨⟨result, aligned, rfl, hprefix, haligned, hstored⟩, hprivate⟩)
  simpa [finishObservedMaterializedDiagnostic] using hstep

set_option maxRecDepth 100000 in
theorem relTriple_any_observedDiagnostic_of_doomed
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (source : ProbComp BoundaryWitnessSnapshotOutput)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hdoomed : DoomedResolvedContext table (directDeferredContext state)) :
    RelTriple source
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache >>= finishObservedMaterializedDiagnostic table)
      (BoundarySnapshotDiagnosticRel table) := by
  have hbase := relTriple_true source
    (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
      table cache)
  have hsupported := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  have hstep := relTriple_bind hsupported (fun left observed hsupport => by
    cases observed with
    | none => exact relTriple_any_finishDiagnostic_none table (pure left)
    | some result =>
        have hnext := materializedDoomed_of_mem_observedMaterializedBoundary parameter root
          ftsSecret computation observations state fuel table cache result hdoomed hsupport.2
        exact relTriple_any_finishDiagnostic_doomed table (pure left) result hnext.2.2.2)
  simpa using hstep

set_option maxRecDepth 100000 in
theorem relTriple_pure_snapshot_observedDiagnostic
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (source : BoundaryWitnessSnapshotOutput)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (haligned : SnapshotsObservedAt table source.witnessSnapshot.2 observations)
    (hstable : ((∀ witness, source.witnessSnapshot.1 = some witness →
        state.values (.position witness.position) = some witness.output) ∧
      (source.outcome.failed = true → source.witnessSnapshot.1.isSome = true)) ∨
      DoomedResolvedContext table (directDeferredContext state)) :
    RelTriple (pure source : ProbComp BoundaryWitnessSnapshotOutput)
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache >>= finishObservedMaterializedDiagnostic table)
      (BoundarySnapshotDiagnosticRel table) := by
  rcases hstable with ⟨hstored, hprivate⟩ | hdoomed
  · have hbase := relTriple_true (pure source : ProbComp BoundaryWitnessSnapshotOutput)
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)
    have hleft := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun output => output = source) (by intro output houtput; simpa using houtput)
    have hboth := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
    have hstep := relTriple_bind hboth (fun left observed hsupport => by
      have heq : left = source := hsupport.1.2
      subst left
      cases observed with
      | none => exact relTriple_any_finishDiagnostic_none table (pure source)
      | some result =>
          apply relTriple_pure_finishDiagnostic_aligned table source result observations
          · exact observations_prefix_of_mem_observedMaterializedBoundary parameter root ftsSecret
              computation observations state fuel table cache result hsupport.2
          · exact haligned
          · intro witness hwitness
            exact valuesLE_of_mem_observedMaterializedBoundary parameter root ftsSecret computation
              observations state fuel table cache result hsupport.2 _ witness.output
              (hstored witness hwitness)
          · exact hprivate)
    simpa using hstep
  · exact relTriple_any_observedDiagnostic_of_doomed parameter root ftsSecret computation
      (pure source) observations state fuel table cache hdoomed

end SphincsSecurity.Concrete.OtsProbeSimulation
