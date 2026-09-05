import SphincsSecurity.Proof.OtsProbeCanonicalPendingHit

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

theorem evalDist_finalizeResolvedCoordinates_eq_none_of_pendingResolvedHit
    (table : OtsSecretIndex → HashOutput) (coordinates : List Coordinate) (context : DeferredContext)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hcovered : PendingCovered coordinates context)
    (hhit : PendingResolvedHit table context) :
    evalDist (finalizeResolvedCoordinates coordinates context table) =
      evalDist (pure none : ProbComp (Option DeferredContext)) := by
  obtain ⟨coordinate, output, hvalue, hhit⟩ := hhit
  have hpending : (coordinate, truncateHash output) ∈ context.state.pending := by
    rwa [← LazyRevealProbe.State.mem_pendingAt_iff]
  have hmem : coordinate ∈ coordinates := hcovered _ hpending
  have hmissing : context.state.values coordinate = none := by
    cases hstate : context.state.values coordinate with
    | none => rfl
    | some cached =>
        have heq : cached = output := by
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              have htable := hstarts ⟨lay, tree, leafIdx, chainIdx⟩ cached hstate
              simpa [resolvedCompletionValue, htable] using hvalue
          | position position => simpa [resolvedCompletionValue, DeferredContext.positionValue, hstate] using hvalue
        exact False.elim (hvalid.2 coordinate cached hstate (heq ▸ hhit))
  rw [evalDist_finalizeResolvedCoordinates_move_to_front coordinate coordinates context table hmem]
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      have heq : table ⟨lay, tree, leafIdx, chainIdx⟩ = output := by
        simpa [resolvedCompletionValue] using hvalue
      rw [finalizeResolvedCoordinates]
      simp only [hmissing]
      rw [resolveDeferredChainStart_of_missing table ⟨lay, tree, leafIdx, chainIdx⟩ context hmissing]
      simp [OtsSecretIndex.coordinate, heq, hhit]
  | position position =>
      have hdeferred : context.values position = some output := by
        simpa [resolvedCompletionValue, DeferredContext.positionValue, hmissing] using hvalue
      rw [finalizeResolvedCoordinates_cons_position_of_deferred_value position _ context table output
        hmissing hdeferred, if_pos hhit]

theorem evalDist_finalizeResolvedCoordinates_eq_none_of_not_completable
    (table : OtsSecretIndex → HashOutput) (coordinates : List Coordinate) (context : DeferredContext)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hcovered : PendingCovered coordinates context)
    (hcard : context.state.pending.card < Fintype.card Digest)
    (hstop : ¬DeferredCompletable table context) :
    evalDist (finalizeResolvedCoordinates coordinates context table) =
      evalDist (pure none : ProbComp (Option DeferredContext)) := by
  apply evalDist_finalizeResolvedCoordinates_eq_none_of_pendingResolvedHit table coordinates context
    hvalid hstarts hcovered
  exact Classical.not_not.mp fun hclean => hstop
    ((deferredCompletable_iff_no_pendingResolvedHit table context hvalid.valuesConsistent hstarts hcard).mpr hclean)

theorem evalDist_finalize_materializeResolvedReveal_dynamic
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (position : Position) (result : DeferredResolution)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card < Fintype.card Digest)
    (hresult : some result ∈ support (resolveDeferredReveal table position context)) :
    evalDist (Option.isNone <$> finalizeResolvedCoordinates
      (materializeResolvedPosition context position result).state.coordinates.toList
      (materializeResolvedPosition context position result) table) =
    evalDist (Option.isNone <$> finalizeResolvedCoordinates
      result.state.coordinates.toList result.toDeferredContext table) := by
  by_cases hcomplete : DeferredCompletable table (materializeResolvedPosition context position result)
  · exact evalDist_map_isNone_finalizeResolvedCoordinates_materializeResolvedReveal_dynamic
      position result hvalid hstarts hresult hcomplete
  · have hresolvedValid := hvalid.of_resolveDeferredReveal table position result hresult
    have hvalues := resolveDeferredReveal_preserves_state_values table position context result hresult
    have hresolved := resolveDeferredReveal_resolves table position context result hresult
    have hmaterializedValid := hvalid.materializeResolvedPosition_of position result hresolvedValid hvalues hresolved
    have hmaterializedStarts : StartTableAgrees (materializeResolvedPosition context position result).state table :=
      hstarts.materialize_position position result.output
    have hresolvedStarts := hstarts.of_state_values_eq hvalues
    have hsubset : result.state.pending ⊆ context.state.pending :=
      (resolveDeferredReveal_pendingAway_subset table position context result hresult).trans (Finset.filter_subset _ _)
    have hresolvedCard := (Finset.card_le_card hsubset).trans_lt hcard
    have hmaterializedCard : (materializeResolvedPosition context position result).state.pending.card <
        Fintype.card Digest :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_lt hcard
    have hresolvedStop : ¬DeferredCompletable table result.toDeferredContext := by
      rintro ⟨completion, hcompletion⟩
      exact hcomplete ⟨completion,
        (deferredCompletion_materializeResolvedReveal_iff position result hvalid hstarts hresult).mpr hcompletion⟩
    rw [evalDist_map, evalDist_map,
      evalDist_finalizeResolvedCoordinates_eq_none_of_not_completable table _ _ hmaterializedValid
        hmaterializedStarts (pendingCovered_coordinates_toList _) hmaterializedCard hcomplete,
      evalDist_finalizeResolvedCoordinates_eq_none_of_not_completable table _ _ hresolvedValid
        hresolvedStarts (pendingCovered_coordinates_toList _) hresolvedCard hresolvedStop]

theorem evalDist_finalizeResolvedCoordinates_eq_dynamic
    (table : OtsSecretIndex → HashOutput) (coordinates : List Coordinate) (context : DeferredContext)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hcovered : PendingCovered coordinates context) (hnodup : coordinates.Nodup)
    (hcard : context.state.pending.card < Fintype.card Digest) :
    evalDist (Option.isNone <$> finalizeResolvedCoordinates coordinates context table) =
      evalDist (Option.isNone <$> finalizeResolvedCoordinates context.state.coordinates.toList context table) := by
  by_cases hcomplete : DeferredCompletable table context
  · apply evalDist_map_isNone_finalizeResolvedCoordinates_congr_covered table coordinates
      context.state.coordinates.toList context context
      (FinalizationViewEq.refl table context hvalid hstarts ?_) hnodup (Finset.nodup_toList _)
      hcovered (pendingCovered_coordinates_toList context)
    intro coordinate output hvalue hhit
    exact hcomplete.not_pendingResolvedHit ⟨coordinate, output, hvalue, hhit⟩
  · rw [evalDist_map, evalDist_map,
      evalDist_finalizeResolvedCoordinates_eq_none_of_not_completable table coordinates context
        hvalid hstarts hcovered hcard hcomplete,
      evalDist_finalizeResolvedCoordinates_eq_none_of_not_completable table _ context
        hvalid hstarts (pendingCovered_coordinates_toList _) hcard hcomplete]

theorem evalDist_resolveDeferredReveal_then_finalize_materialized
    (table : OtsSecretIndex → HashOutput) (position : Position) (context : DeferredContext)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card < Fintype.card Digest) :
    evalDist (do
      let result ← resolveDeferredReveal table position context
      match result with
      | none => pure true
      | some result => Option.isNone <$> (finalizeResolvedCoordinates
          (materializeResolvedPosition context position result).state.coordinates.toList
          (materializeResolvedPosition context position result) table)) =
    evalDist (Option.isNone <$> finalizeResolvedCoordinates context.state.coordinates.toList context table) := by
  let coordinates := context.state.coordinates.toList
  have hbase := evalDist_map_resolveDeferredReveal_then_finalize table position coordinates context
    hvalid (pendingCovered_coordinates_toList context)
  calc
    _ = evalDist (Option.isNone <$> (do
        let result ← resolveDeferredReveal table position context
        match result with
        | none => (pure none : ProbComp (Option (LazyRevealProbe.State Coordinate)))
        | some result => projectDeferredState <$>
            finalizeResolvedCoordinates coordinates result.toDeferredContext table)) := by
      rw [map_bind]
      apply evalDist_bind_congr
      intro option hoption
      cases option with
      | none => simp
      | some result =>
          have hsubset : result.state.pending ⊆ context.state.pending :=
            (resolveDeferredReveal_pendingAway_subset table position context result hoption).trans (Finset.filter_subset _ _)
          have hresolvedValid := hvalid.of_resolveDeferredReveal table position result hoption
          have hresolvedStarts := hstarts.of_state_values_eq
            (resolveDeferredReveal_preserves_state_values table position context result hoption)
          have hresolvedCovered : PendingCovered coordinates result.toDeferredContext := by
            intro entry hentry
            exact pendingCovered_coordinates_toList context entry (hsubset hentry)
          have hfixed := evalDist_finalizeResolvedCoordinates_eq_dynamic table coordinates result.toDeferredContext
            hresolvedValid hresolvedStarts hresolvedCovered (Finset.nodup_toList _)
            ((Finset.card_le_card hsubset).trans_lt hcard)
          have hmaterialized := evalDist_finalize_materializeResolvedReveal_dynamic
            position result hvalid hstarts hcard hoption
          simpa only [Functor.map_map, Function.comp_def, projectDeferredState, Option.isNone_map] using
            hmaterialized.trans hfixed.symm
    _ = _ := by
      rw [evalDist_map]
      apply (congrArg (Functor.map Option.isNone) hbase).trans
      rw [← evalDist_map, Functor.map_map]
      simp only [projectDeferredState, Option.isNone_map, coordinates]

noncomputable def resolvedPendingFailureRisk
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) : ℝ≥0∞ :=
  Pr[fun result => result = none |
    finalizeResolvedCoordinates context.state.coordinates.toList context table]

theorem resolvedPendingFailureRisk_eq_resolveDeferredReveal
    (table : OtsSecretIndex → HashOutput) (position : Position) (context : DeferredContext)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card < Fintype.card Digest) :
    resolvedPendingFailureRisk table context =
      ∑' option, Pr[= option | resolveDeferredReveal table position context] *
        match option with
        | none => 1
        | some result => resolvedPendingFailureRisk table (materializeResolvedPosition context position result) := by
  have hdist := evalDist_resolveDeferredReveal_then_finalize_materialized table position context hvalid hstarts hcard
  have hprob := congrArg (fun distribution : SPMF Bool => distribution true) hdist
  change Pr[= true | _] = Pr[= true | _] at hprob
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
    probEvent_bind_eq_tsum, probEvent_map] at hprob
  simp only [Function.comp_def] at hprob
  have hevent : (fun result : Option DeferredContext => result.isNone = true) = (fun result => result = none) := by
    funext result; simp
  rw [hevent] at hprob
  change _ = resolvedPendingFailureRisk table context at hprob
  rw [← hprob]
  apply tsum_congr
  intro option
  cases option with
  | none => simp
  | some result => simp only [resolvedPendingFailureRisk, probEvent_map, Function.comp_def, hevent]

theorem evalDist_finishResolvedRunIsNone_eq_finalize
    (result : ResolvedRunResult α) (hvalid : result.context.Valid)
    (hstarts : StartTableAgrees result.context.state result.table)
    (hcard : result.context.state.pending.card < Fintype.card Digest) :
    evalDist (finishResolvedRunIsNone (some result)) =
      evalDist (Option.isNone <$> finalizeResolvedCoordinates
        result.context.state.coordinates.toList result.context result.table) := by
  by_cases hcomplete : DeferredCompletable result.table result.context
  · rw [finishResolvedRunIsNone_some_eq_finalize result hcomplete]
  · rw [finishResolvedRunIsNone, finishResolvedRun_of_not_deferredCompletable result hcomplete]
    simp only [evalDist_map]
    rw [evalDist_finalizeResolvedCoordinates_eq_none_of_not_completable
        result.table _ result.context hvalid hstarts (pendingCovered_coordinates_toList _) hcard hcomplete]
    simp

theorem evalDist_runResolvedFinishIsNone_revealPosition
    (table : OtsSecretIndex → HashOutput) (position : Position) (context : DeferredContext)
    (fuel : Nat) (cache : SplitHashCache)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card < Fintype.card Digest) :
    evalDist (runResolvedFinishIsNone context fuel table ((revealCoordinate (.position position)).run cache)) =
      evalDist (Option.isNone <$> finalizeResolvedCoordinates context.state.coordinates.toList context table) := by
  apply Eq.trans ?_ (evalDist_resolveDeferredReveal_then_finalize_materialized table position context hvalid hstarts hcard)
  rw [runResolvedFinishIsNone, runResolvedFromTable_revealCoordinate, bind_assoc]
  apply evalDist_bind_congr
  intro option hoption
  cases option with
  | none => simp [finishResolvedRunIsNone, finishResolvedRun]
  | some result =>
      simp only [pure_bind]
      have hresolvedValid := hvalid.of_resolveDeferredReveal table position result hoption
      have hvalues := resolveDeferredReveal_preserves_state_values table position context result hoption
      have hresolved := resolveDeferredReveal_resolves table position context result hoption
      apply evalDist_finishResolvedRunIsNone_eq_finalize
      · exact hvalid.materializeResolvedPosition_of position result hresolvedValid hvalues hresolved
      · exact hstarts.materialize_position position result.output
      · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_lt hcard

theorem probEvent_resolvedQueryRejected_le_finished (computation : ProbComp (Option (ResolvedRunResult α))) :
    Pr[ResolvedQueryRejected | computation] ≤
      Pr[fun verdict => verdict = true | computation >>= finishResolvedRunIsNone] := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro option
  by_cases hreject : ResolvedQueryRejected option
  · rw [if_pos hreject]
    cases option with
    | none => simp [finishResolvedRunIsNone, finishResolvedRun]
    | some result =>
        simp only [ResolvedQueryRejected] at hreject
        simp [finishResolvedRunIsNone, finishResolvedRun_of_not_deferredCompletable result hreject]
  · rw [if_neg hreject]
    exact bot_le

theorem probEvent_revealPosition_rejected_le_pendingFailureRisk
    (table : OtsSecretIndex → HashOutput) (position : Position) (context : DeferredContext)
    (fuel : Nat) (cache : SplitHashCache)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card < Fintype.card Digest) :
    Pr[ResolvedQueryRejected | runResolvedFromTable context fuel table
      ((revealCoordinate (.position position)).run cache)] ≤ resolvedPendingFailureRisk table context := by
  apply (probEvent_resolvedQueryRejected_le_finished _).trans_eq
  have heq := congrArg (fun distribution : SPMF Bool => distribution true)
    (evalDist_runResolvedFinishIsNone_revealPosition table position context fuel cache hvalid hstarts hcard)
  change Pr[= true | _] = Pr[= true | _] at heq
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map] at heq
  simpa only [runResolvedFinishIsNone, Function.comp_def, Option.isNone_iff_eq_none, resolvedPendingFailureRisk] using heq

end SphincsSecurity.Concrete.OtsProbeSimulation
