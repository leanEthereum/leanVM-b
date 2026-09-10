import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeRecursiveRejectionRisk
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryDirect

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

theorem evalDist_finalize_failure_of_coreEq
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (hvalid : left.Valid) (hstarts : StartTableAgrees left.state table)
    (hcomplete : DeferredCompletable table left) (heq : left.CoreEq right) :
    evalDist (Option.isNone <$> finalizeResolvedCoordinates left.state.coordinates.toList left table) =
      evalDist (Option.isNone <$> finalizeResolvedCoordinates right.state.coordinates.toList right table) := by
  have hrightValid := hvalid.of_coreEq heq
  have hrightStarts := hstarts.of_coreEq heq
  have hvalues : resolvedCompletionValue table left = resolvedCompletionValue table right := by
    funext coordinate
    cases coordinate with
    | chainStart => rfl
    | position position => exact congrFun heq.positionValue_eq position
  have hview := finalizationViewEq_of_deferredCompletion_iff hvalid hrightValid hstarts hrightStarts
    hvalues hcomplete (fun completion =>
      ⟨fun h => h.of_coreEq heq, fun h => h.of_coreEq heq.symm⟩)
  exact evalDist_map_isNone_finalizeResolvedCoordinates_congr_covered table _ _ left right hview
    (Finset.nodup_toList _) (Finset.nodup_toList _)
    (pendingCovered_coordinates_toList _) (pendingCovered_coordinates_toList _)

theorem evalDist_resolveDeferredChainStart_then_finalize_materialized
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex) (context : DeferredContext)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hcomplete : DeferredCompletable table context)
    (hcard : context.state.pending.card < Fintype.card Digest) :
    evalDist (match resolveDeferredChainStart table index context with
      | none => (pure true : ProbComp Bool)
      | some result => Option.isNone <$> (finalizeResolvedCoordinates
          (materializeResolvedChainStart context index result).state.coordinates.toList
          (materializeResolvedChainStart context index result) table)) =
      evalDist (Option.isNone <$> finalizeResolvedCoordinates context.state.coordinates.toList context table) := by
  let coordinates := context.state.coordinates.toList
  have hbase := congrArg (Functor.map Option.isNone)
    (evalDist_map_resolveDeferredChainStart_then_finalize table index coordinates context
      hvalid (pendingCovered_coordinates_toList context))
  rw [← evalDist_map, ← evalDist_map, Functor.map_map] at hbase
  have hright : (fun option => (projectDeferredState option).isNone) =
      (Option.isNone : Option DeferredContext → Bool) := by
    funext option; cases option <;> rfl
  rw [hright] at hbase
  apply Eq.trans ?_ hbase
  cases hresult : resolveDeferredChainStart table index context with
  | none => simp
  | some result =>
      rw [Functor.map_map, hright]
      have hresultValid := hvalid.of_resolveDeferredChainStart table index result hresult
      have hresultStarts := hstarts.of_state_values_eq
        (resolveDeferredChainStart_state_values_eq table index context result hresult)
      have hpending := resolveDeferredChainStart_pending_eq table index context result hresult
      have hsubset : result.state.pending ⊆ context.state.pending := by
        rw [hpending]; exact Finset.filter_subset _ _
      have hcovered : PendingCovered coordinates result.toDeferredContext := by
        intro entry hentry
        exact pendingCovered_coordinates_toList context entry (hsubset hentry)
      have hfixed := evalDist_finalizeResolvedCoordinates_eq_dynamic table coordinates result.toDeferredContext
        hresultValid hresultStarts hcovered (Finset.nodup_toList _)
        ((Finset.card_le_card hsubset).trans_lt hcard)
      have hview := finalizationViewEq_materializeResolvedChainStart index result hvalid hstarts hresult
        (hcomplete.materializeResolvedChainStart hstarts index result hresult)
      exact (evalDist_map_isNone_finalizeResolvedCoordinates_congr_covered table _ _ _ _ hview
        (Finset.nodup_toList _) (Finset.nodup_toList _)
        (pendingCovered_coordinates_toList _) (pendingCovered_coordinates_toList _)).trans hfixed.symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem evalDist_runResolvedFinishIsNone_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card < Fintype.card Digest) :
    evalDist (runResolvedFinishIsNone context fuel table computation) =
      evalDist (Option.isNone <$> finalizeResolvedCoordinates context.state.coordinates.toList context table) := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp only [runResolvedFinishIsNone, runResolvedFromTable, OracleComp.construct_pure, pure_bind]
      exact evalDist_finishResolvedRunIsNone_eq_finalize ⟨context, fuel, value, table⟩ hvalid hstarts hcard
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
        have htail : ∀ output, (next output).IsQueryBoundP LazyRevealProbe.IsProbe 0 := by
          intro output
          simpa only [Nat.zero_sub, ite_self] using hbound.2 output
        cases input with
        | uniform n =>
            rw [runResolvedFinishIsNone, runResolvedFromTable_uniform_query_bind, bind_assoc]
            calc
              _ = evalDist (do
                  let _ ← (liftM (unifSpec.query n) : ProbComp _)
                  Option.isNone <$> finalizeResolvedCoordinates context.state.coordinates.toList context table) := by
                apply evalDist_bind_congr
                intro output _houtput
                exact ih output context fuel (htail output) hvalid hstarts hcard
              _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _
        | hashOutput =>
            rw [runResolvedFinishIsNone, runResolvedFromTable_hashOutput_query_bind, bind_assoc]
            calc
              _ = evalDist (do
                  let _ ← LazyRevealProbe.sampleHashOutput
                  Option.isNone <$> finalizeResolvedCoordinates context.state.coordinates.toList context table) := by
                apply evalDist_bind_congr
                intro output _houtput
                exact ih output context fuel (htail output) hvalid hstarts hcard
              _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _
        | ensure coordinate =>
            rw [runResolvedFinishIsNone, runResolvedFromTable_ensure_query_bind]
            have heq : context.CoreEq { context with state := context.state.ensure coordinate } := ⟨rfl, rfl, rfl⟩
            exact (ih () _ fuel (htail ()) (hvalid.of_coreEq heq) (hstarts.of_coreEq heq) hcard).trans
              (evalDist_finalize_failure_of_coreEq table _ _ hvalid hstarts hcomplete heq).symm
        | publish coordinate =>
            rw [runResolvedFinishIsNone, runResolvedFromTable_publish_query_bind]
            have heq : context.CoreEq { context with state := context.state.publish coordinate } := ⟨rfl, rfl, rfl⟩
            exact (ih () _ fuel (htail ()) (hvalid.of_coreEq heq) (hstarts.of_coreEq heq) hcard).trans
              (evalDist_finalize_failure_of_coreEq table _ _ hvalid hstarts hcomplete heq).symm
        | peek coordinate =>
            rw [runResolvedFinishIsNone, runResolvedFromTable_peek_query_bind]
            exact ih _ context fuel (htail _) hvalid hstarts hcard
        | probe coordinate candidate => simp [LazyRevealProbe.IsProbe] at hbound
        | reveal coordinate =>
            cases coordinate with
            | position position =>
                rw [runResolvedFinishIsNone, runResolvedFromTable_reveal_query_bind, bind_assoc]
                apply Eq.trans ?_ (evalDist_resolveDeferredReveal_then_finalize_materialized
                  table position context hvalid hstarts hcard)
                apply evalDist_bind_congr
                intro option hoption
                cases option with
                | none => simp [finishResolvedRunIsNone, finishResolvedRun]
                | some result =>
                    have hresolvedValid := hvalid.of_resolveDeferredReveal table position result hoption
                    have hvalues := resolveDeferredReveal_preserves_state_values table position context result hoption
                    have hresolved := resolveDeferredReveal_resolves table position context result hoption
                    exact ih result.output _ fuel (htail result.output)
                      (hvalid.materializeResolvedPosition_of position result hresolvedValid hvalues hresolved)
                      (hstarts.materialize_position position result.output)
                      ((Finset.card_le_card (Finset.filter_subset _ _)).trans_lt hcard)
            | chainStart lay tree leafIdx chainIdx =>
                let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
                rw [runResolvedFinishIsNone, runResolvedFromTable_reveal_query_bind]
                dsimp only
                rw [pure_bind]
                apply Eq.trans ?_ (evalDist_resolveDeferredChainStart_then_finalize_materialized
                  table index context hvalid hstarts hcomplete hcard)
                cases hresult : resolveDeferredChainStart table index context with
                | none => simp [finishResolvedRunIsNone, finishResolvedRun]
                | some result =>
                    have hdeferred := resolveDeferredChainStart_deferred_values_eq table index context result hresult
                    have houtput := resolveDeferredChainStart_output_of_agrees table index context result hstarts hresult
                    have hnextValid : (materializeResolvedChainStart context index result).Valid := by
                      rw [materializeResolvedChainStart, hdeferred]
                      exact hvalid.materialize_chainStart lay tree leafIdx chainIdx result.output
                    have hnextStarts : StartTableAgrees (materializeResolvedChainStart context index result).state table := by
                      simp only [materializeResolvedChainStart, houtput]
                      exact hstarts.materialize_start index
                    simpa only [index, hresult, materializeResolvedChainStart, OtsSecretIndex.coordinate,
                      runResolvedFinishIsNone] using
                      ih result.output _ fuel (htail result.output) hnextValid hnextStarts
                        ((Finset.card_le_card (Finset.filter_subset _ _)).trans_lt hcard)
      · rw [runResolvedFinishIsNone,
          evalDist_runResolvedFinishIsNone_eq_true_of_not_completable context fuel table _
            hvalid.valuesConsistent hstarts hcomplete,
          evalDist_map, evalDist_finalizeResolvedCoordinates_eq_none_of_not_completable table _ context
            hvalid hstarts (pendingCovered_coordinates_toList _) hcard hcomplete]
        simp

theorem evalDist_finish_canonicalizeResolvedRun
    (result : ResolvedRunResult α) (hvalid : result.context.Valid)
    (hstarts : StartTableAgrees result.context.state result.table) :
    evalDist (finishResolvedRunIsNone (canonicalizeResolvedRun result.table (some result))) =
      evalDist (finishResolvedRunIsNone (some result)) := by
  by_cases hcomplete : DeferredCompletable result.table result.context
  · have hcanonical := valid_completable_canonicalizeMaterializedValues result.table result.context hvalid hcomplete
    have hview := finalizationViewEq_canonicalize_left result.table result.context hvalid hstarts
      (fun coordinate output hvalue hhit => hcomplete.not_pendingResolvedHit ⟨coordinate, output, hvalue, hhit⟩)
    simp only [canonicalizeResolvedRun]
    rw [finishResolvedRunIsNone_some_eq_finalize _ hcanonical.2,
      finishResolvedRunIsNone_some_eq_finalize result hcomplete]
    exact evalDist_map_isNone_finalizeResolvedCoordinates_congr_covered result.table _ _ _ _ hview
      (Finset.nodup_toList _) (Finset.nodup_toList _)
      (pendingCovered_coordinates_toList _) (pendingCovered_coordinates_toList _)
  · have hcanonical := doomedResolvedContext_canonicalizeMaterializedValues
      (show DoomedResolvedContext result.table result.context from ⟨hvalid.valuesConsistent, hstarts, hcomplete⟩)
    simp [canonicalizeResolvedRun, finishResolvedRunIsNone, finishResolvedRun, hcomplete, hcanonical.2.2]

end SphincsSecurity.Concrete.OtsProbeSimulation
