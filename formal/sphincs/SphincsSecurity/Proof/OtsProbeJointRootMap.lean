import SphincsSecurity.Proof.OtsProbeJointFinalization

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option linter.constructorNameAsVariable false

def retainDiagnosticRoot (root : Digest)
    (diagnostic : ObservedMaterializedDiagnostic (RetainedRestResult × SplitHashCache)) :
    ObservedMaterializedDiagnostic (RetainedGameResult × SplitHashCache) :=
  ⟨retainObservedRoot root diagnostic.before, retainObservedRoot root diagnostic.final,
    diagnostic.wasDoomed⟩

theorem retainDiagnosticRoot_bad_iff (root : Digest)
    (diagnostic : ObservedMaterializedDiagnostic (RetainedRestResult × SplitHashCache)) :
    (retainDiagnosticRoot root diagnostic).Bad ↔ diagnostic.Bad := by
  cases diagnostic with
  | mk before final wasDoomed =>
      cases final <;> simp [retainDiagnosticRoot, retainObservedRoot,
        ObservedMaterializedDiagnostic.Bad]

theorem BoundarySnapshotDiagnosticRel.retainRoot
    {table : OtsSecretIndex → HashOutput}
    {source : BoundaryWitnessSnapshotOutput}
    {diagnostic : ObservedMaterializedDiagnostic (RetainedRestResult × SplitHashCache)}
    (hrelation : BoundarySnapshotDiagnosticRel table source diagnostic) (root : Digest) :
    BoundarySnapshotDiagnosticRel table source (retainDiagnosticRoot root diagnostic) := by
  rcases hrelation with hbad | ⟨⟨result, aligned, hresult, hprefix, haligned, hstored⟩, hprivate⟩
  · exact Or.inl ((retainDiagnosticRoot_bad_iff root diagnostic).2 hbad)
  · right
    refine ⟨⟨{ result with value := ((root, result.value.1), result.value.2) }, aligned,
      ?_, hprefix, haligned, hstored⟩, hprivate⟩
    simp [retainDiagnosticRoot, hresult, retainObservedRoot]

theorem map_retainDiagnosticRoot_finish
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (observed : Option (ObservedCleanRunResult (RetainedRestResult × SplitHashCache))) :
    retainDiagnosticRoot root <$> finishObservedMaterializedDiagnostic table observed =
      finishObservedMaterializedDiagnostic table (retainObservedRoot root observed) := by
  classical
  cases observed with
  | none => simp [finishObservedMaterializedDiagnostic, retainDiagnosticRoot, retainObservedRoot]
  | some result =>
      simp only [finishObservedMaterializedDiagnostic, finishObservedCleanRunFromTable,
        retainObservedRoot, map_bind, bind_assoc]
      apply bind_congr
      intro finalized
      cases finalized <;> rfl

theorem map_retainDiagnosticRoot_bind_finish
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (run : ProbComp (Option (ObservedCleanRunResult (RetainedRestResult × SplitHashCache)))) :
    retainDiagnosticRoot root <$> (run >>= finishObservedMaterializedDiagnostic table) =
      (retainObservedRoot root <$> run) >>= finishObservedMaterializedDiagnostic table := by
  rw [map_bind, bind_map_left]
  apply bind_congr
  intro observed
  exact map_retainDiagnosticRoot_finish table root observed

end SphincsSecurity.Concrete.OtsProbeSimulation
