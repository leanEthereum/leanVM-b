import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalTop

/-!
# Global materialized comparison finalization

The adaptive comparison keeps a single clean-or-doomed alternative through the retained run. This
module discharges that alternative once, at finalization, and preserves the source witness value and
the chronological probe observations on every successful completion.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem observations_eq_of_mem_finishObservedCleanRunFromTable
    (result finalResult : ObservedCleanRunResult α)
    (hresult : some finalResult ∈ support
      (finishObservedCleanRunFromTable (some result))) :
    finalResult.observations = result.observations := by
  unfold finishObservedCleanRunFromTable at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨finalized, _hfinalized, hreturn⟩ := hresult
  cases finalized with
  | none => simp at hreturn
  | some value =>
      rcases value with ⟨finalState, finalTable⟩
      simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hreturn
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hreturn
      rfl

theorem relTriple_pure_finishObservedMaterialized_of_stable
    (table : OtsSecretIndex → HashOutput)
    (source : PrivateWitnessSnapshotOutput)
    (observed : Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)))
    (hrelation : SnapshotObservedPrefixStableRel table source observed) :
    RelTriple
      (pure source : ProbComp PrivateWitnessSnapshotOutput)
      (finishObservedMaterializedCleanRunFromTable table observed)
      (SnapshotObservedPrefixValueRel table) := by
  rcases hrelation with hfailed | hsuccess | hdoomed
  · subst observed
    simp [finishObservedMaterializedCleanRunFromTable,
      SnapshotObservedPrefixValueRel]
  · obtain ⟨result, aligned, hresult, hprefix, haligned, hstored⟩ := hsuccess
    subst observed
    by_cases hcompletable :
        DeferredCompletable table (directDeferredContext result.state)
    · simp only [finishObservedMaterializedCleanRunFromTable, hcompletable, ↓reduceIte]
      have hbase := relTriple_true (pure source : ProbComp PrivateWitnessSnapshotOutput)
        (finishObservedCleanRunFromTable (some result))
      have hleft :=
        SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
          (fun output => output = source) (by
            intro output houtput
            simpa using houtput)
      have hboth :=
        SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
      apply relTriple_post_mono hboth
      intro left final hfacts
      rcases hfacts with ⟨⟨_htrue, hleftEq⟩, hfinalSupport⟩
      subst left
      cases final with
      | none => exact Or.inl rfl
      | some finalResult =>
          right
          refine ⟨finalResult, aligned, rfl, ?_, haligned, ?_⟩
          · rw [observations_eq_of_mem_finishObservedCleanRunFromTable result finalResult
              hfinalSupport]
            exact hprefix
          · intro witness hwitness
            exact valuesLE_of_mem_finishObservedCleanRunFromTable result finalResult
              hfinalSupport (.position witness.position) witness.output
                (hstored witness hwitness)
    · simp [finishObservedMaterializedCleanRunFromTable, hcompletable,
        SnapshotObservedPrefixValueRel]
  · obtain ⟨result, hresult, hdoomed⟩ := hdoomed
    subst observed
    have hnotCompletable :
        ¬DeferredCompletable table (directDeferredContext result.state) := hdoomed.2.2
    simp [finishObservedMaterializedCleanRunFromTable, hnotCompletable,
      SnapshotObservedPrefixValueRel]

theorem relTriple_finishObservedMaterialized_of_stable
    (table : OtsSecretIndex → HashOutput)
    (source : ProbComp PrivateWitnessSnapshotOutput)
    (observed : ProbComp (Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))))
    (hrelation : RelTriple source observed (SnapshotObservedPrefixStableRel table)) :
    RelTriple source
      (observed >>= finishObservedMaterializedCleanRunFromTable table)
      (SnapshotObservedPrefixValueRel table) := by
  have hbound := relTriple_bind hrelation fun sourceOutput observedOutput houtput =>
    relTriple_pure_finishObservedMaterialized_of_stable table sourceOutput observedOutput houtput
  simpa using hbound

end SphincsSecurity.Concrete.OtsProbeSimulation
