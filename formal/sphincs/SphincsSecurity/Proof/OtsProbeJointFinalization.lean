import SphincsSecurity.Proof.OtsProbeJointDiagnostic

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option linter.constructorNameAsVariable false

set_option maxRecDepth 100000 in
theorem evalDist_finalIsNone_finishDiagnostic_eq_resolved
    (table : OtsSecretIndex → HashOutput) (result : ObservedCleanRunResult α)
    (htable : result.table = table)
    (hcomplete : DeferredCompletable table (directDeferredContext result.state)) :
    evalDist ((fun diagnostic => diagnostic.final.isNone) <$>
        finishObservedMaterializedDiagnostic table (some result)) =
      evalDist (finishResolvedRunIsNone
        (some ⟨directDeferredContext result.state, result.remaining, result.value, table⟩)) := by
  rw [evalDist_finishResolvedRunIsNone_eq_finishDirectRunIsNone _ _ _ _ hcomplete]
  apply congrArg evalDist
  simp only [finishObservedMaterializedDiagnostic, finishObservedCleanRunFromTable,
    finishDirectRunIsNone, finishCleanRunIsNone, finishCleanRunFromTable,
    projectResolvedRunResult, htable, map_bind, bind_assoc]
  apply bind_congr
  intro final
  cases final <;> rfl

set_option maxRecDepth 100000 in
theorem relTriple_resolvedFinalization_diagnostic
    (table : OtsSecretIndex → HashOutput) (left : DeferredContext)
    (leftFuel : Nat) (leftValue : α) (right : ObservedCleanRunResult β)
    (htable : right.table = table)
    (hcontext : FinalizationContextLE table left (directDeferredContext right.state)) :
    RelTriple (resolvedFinalizationObserve table left leftFuel leftValue)
      (finishObservedMaterializedDiagnostic table (some right))
      (fun failed diagnostic => failed = true → diagnostic.final = none) := by
  have hleft : resolvedFinalizationObserve table left leftFuel leftValue =
      resolvedFinalizationObserve table left leftFuel right.value := by
    unfold resolvedFinalizationObserve
    rw [finishResolvedRunIsNone_some_eq_finalize _ hcontext.leftCompletable,
      finishResolvedRunIsNone_some_eq_finalize _ hcontext.leftCompletable]
  have hbase := relTriple_finishResolvedRunIsNone_of_finalizationContextLE table left
    (directDeferredContext right.state) leftFuel right.remaining right.value right.value hcontext
  have hright := evalDist_finalIsNone_finishDiagnostic_eq_resolved table right htable
    hcontext.rightCompletable
  have hmapped := relTriple_of_evalDist_eq_right hright.symm hbase
  have hfull := relTriple_lift_right_observation
    (fun diagnostic : ObservedMaterializedDiagnostic β => diagnostic.final.isNone) hmapped
  rw [hleft]
  apply relTriple_post_mono hfull
  intro failed diagnostic himp hfailed
  exact Option.isNone_iff_eq_none.1 (himp hfailed)

set_option maxRecDepth 100000 in
theorem relTriple_retainedFinalization_jointDiagnostic
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (left : DeferredContext) (leftFuel : Nat)
    (leftValue : RetainedRestResult × SplitHashCache)
    (right : ObservedCleanRunResult α)
    (snapshots : List PlannedProbeSnapshot)
    (haligned : SnapshotsObservedAt table snapshots right.observations)
    (htable : right.table = table)
    (hcontext : FinalizationContextLE table left (directDeferredContext right.state)) :
    RelTriple
      (retainedResolvedFinalizationBoundaryWitnessSnapshotObserve table root left leftFuel
        leftValue snapshots)
      (finishObservedMaterializedDiagnostic table (some right))
      (BoundarySnapshotDiagnosticRel table) := by
  classical
  have hnotPrivate := not_privateStructuralHit_of_deferredCompletable hcontext.leftCompletable
  unfold retainedResolvedFinalizationBoundaryWitnessSnapshotObserve
  simp only [hnotPrivate, ↓reduceDIte, hcontext.leftCompletable, ↓reduceIte]
  have hbase := relTriple_resolvedFinalization_diagnostic table left leftFuel
    ((root, leftValue.1), leftValue.2) right htable hcontext
  have hsupported := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  have hstep := relTriple_bind hsupported (fun failed diagnostic hrelation => by
    apply relTriple_pure_pure (R := BoundarySnapshotDiagnosticRel table)
      (a := ⟨DirectBoundaryOutcome.ofFailed failed, none, snapshots⟩) (b := diagnostic)
    by_cases hfailed : failed = true
    · exact Or.inl (Or.inl (hrelation.1 hfailed))
    · have hbefore : diagnostic.before = some right := by
        have hsupport := hrelation.2
        unfold finishObservedMaterializedDiagnostic at hsupport
        rw [mem_support_bind_iff] at hsupport
        obtain ⟨final, _, hreturn⟩ := hsupport
        have heq : diagnostic = ⟨some right, final,
            decide (¬DeferredCompletable table (directDeferredContext right.state))⟩ := by
          simpa using hreturn
        exact congrArg ObservedMaterializedDiagnostic.before heq
      right
      refine ⟨⟨right, right.observations, hbefore, List.prefix_rfl, haligned, ?_⟩, ?_⟩
      · intro witness hwitness
        simp at hwitness
      · intro hsource
        cases failed <;> simp [DirectBoundaryOutcome.ofFailed, DirectBoundaryOutcome.failed] at hfailed hsource)
  simpa using hstep

end SphincsSecurity.Concrete.OtsProbeSimulation
