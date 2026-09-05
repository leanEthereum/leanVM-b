import SphincsSecurity.Proof.OtsProbePrivateValueHistoryTracking

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def privateResolvedSelectedCandidate (target : Position) (select : Nat → α → Option Digest) :
    Option (DeferredContext × Nat × α) → Option (HashOutput × Digest)
  | none => none
  | some (context, remaining, value) => do
      let output ← context.positionValue target
      let candidate ← select remaining value
      pure (output, candidate)

theorem privateResolutionResult_known_candidate
    (target : Position) (output : HashOutput) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (remaining : Nat) (value : α) (select : Nat → α → Option Digest)
    (hconsistent : context.ValuesConsistent)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = some output) :
    privateResolvedSelectedCandidate target select <$> privateResolutionResult target table context remaining value =
      pure (if DeferredCompletable table context then (select remaining value).map (fun digest => (output, digest)) else none) := by
  have hknown : context.positionValue target = some output := by simp [DeferredContext.positionValue, hstate, hvalue]
  by_cases hhit : context.state.hitAt (.position target) output
  · have hdoomed : ¬DeferredCompletable table context := by
      rintro ⟨completion, hcompletion⟩
      have houtput := hcompletion.2.1 target output hvalue
      have hpending := (LazyRevealProbe.State.mem_pendingAt_iff context.state (.position target) (truncateHash output)).mp hhit
      exact hcompletion.2.2.1 _ _ hpending (by rw [houtput])
    simp [privateResolutionResult, resolveDeferredPositionValue, hstate, hvalue, hhit, hdoomed, privateResolvedSelectedCandidate]
  · have hresolve : resolveDeferredPositionValue target context = pure (some (completePrivatePosition target context output)) := by
      have hinstall : context.values.install target output = context.values := by
        unfold DeferredStructuralValues.install
        rw [← hvalue]
        exact Function.update_eq_self target context.values
      simp [resolveDeferredPositionValue, hstate, hvalue, hhit, completePrivatePosition, hinstall]
    have hsupport : some (completePrivatePosition target context output) ∈ support (resolveDeferredPositionValue target context) := by
      rw [hresolve]
      simp
    have hcomplete : DeferredCompletable table (completePrivatePosition target context output).toDeferredContext ↔
        DeferredCompletable table context := by
      constructor
      · rintro ⟨completion, hcompletion⟩
        exact ⟨completion, ((deferredCompletion_resolveDeferredPositionValue_iff target _ hconsistent hsupport completion).mp hcompletion).1⟩
      · rintro ⟨completion, hcompletion⟩
        exact ⟨completion, (deferredCompletion_resolveDeferredPositionValue_iff target _ hconsistent hsupport completion).mpr
          ⟨hcompletion, hcompletion.2.1 target output hvalue⟩⟩
    have hresolvedValue := resolveDeferredPositionValue_resolves target context (completePrivatePosition target context output) hsupport
    unfold privateResolutionResult
    rw [hresolve]
    simp only [pure_bind]
    by_cases hcompletable : DeferredCompletable table context
    · simp only [if_pos hcompletable, if_pos (hcomplete.mpr hcompletable), map_pure, privateResolvedSelectedCandidate, hresolvedValue]
      cases select remaining value <;> rfl
    · simp [hcompletable, hcomplete, privateResolvedSelectedCandidate]

theorem evalDist_privateResolvedSelectedCandidate_preloaded
    (target : Position) (output : HashOutput) (select : Nat → α → Option Digest)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (pending : Finset Digest) (bound : Nat)
    (h : PrivateTargetState target output pending context)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0)
    (hcount : computation.IsQueryBoundP (IsPrivatePositionProbe target) bound) :
    evalDist (privateResolvedSelectedCandidate target select <$> runPrivateResolvedView target table context fuel computation) =
      evalDist ((fun result => result.bind (fun pair => (select pair.1 pair.2).map (fun digest => (output, digest)))) <$>
        runResolvedLiveValue table context fuel computation) := by
  unfold runPrivateResolvedView runResolvedLiveValue
  simp only [map_bind]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      have hfinal := (h.history_of_mem_runResolved computation context fuel table pending bound result hsafe hcount hresult).1
      have hcore := resolvedCore_of_mem_runResolvedFromTable computation context fuel table result hconsistent hstarts hresult
      dsimp only
      rw [privateResolutionResult_known_candidate target output table result.context result.remaining result.value select hcore.2.1 hfinal.1 hfinal.2.1]
      by_cases hcomplete : DeferredCompletable table result.context <;> simp [hcomplete]


def privateTrackedCandidate (target : Position) (remaining : Nat) (value : Finset Digest × PrivateValueCut α) : Option Digest :=
  privateLiveCandidateProjection target value.1 (some (remaining, value.2))

theorem evalDist_privateProbeRecords_candidate_eq_tracked
    (target : Position) (output : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed) :
    evalDist ((fun record => record.bind (privateProbeRecordCandidate target)) <$>
      runPrivateProbeRecords target computation context fuel table ordinal output) =
      evalDist ((fun result => result.bind (fun pair => privateTrackedCandidate target pair.1 pair.2)) <$>
        runResolvedLiveValue table (replacePrivatePosition target output context) fuel
          (trackPrivateProbeHistory target (privatePositionProbeCutAt target computation ordinal) (context.state.pendingAt (.position target)))) := by
  have hinitial : PrivateTargetState target output (context.state.pendingAt (.position target))
      (replacePrivatePosition target output context) :=
    ⟨hstate, by simp [replacePrivatePosition, DeferredStructuralValues.install], hhidden, rfl⟩
  have hdist := evalDist_runResolvedLiveValue_trackPrivateProbeHistory target output
    (privatePositionProbeCutAt target computation ordinal) (replacePrivatePosition target output context) fuel table _ hinitial
    (hvalid.replacePrivatePosition target output hstate).valuesConsistent (show StartTableAgrees context.state table from startTableAgrees_of_deferredCompletable hcomplete)
    (privatePositionProbeCutAt_no_disclosure target computation ordinal)
  calc
    _ = evalDist ((fun result => (privateHistoryValue target (retainCompletableResult result)).bind
        (fun pair => privateTrackedCandidate target pair.1 pair.2)) <$>
        runResolvedFromTable (replacePrivatePosition target output context) fuel table (privatePositionProbeCutAt target computation ordinal)) := by
      unfold runPrivateProbeRecords runPrivateRecords
      rw [Functor.map_map]
      congr 2
      funext result
      unfold privateRecordedResult privateHistoryValue
      cases retainCompletableResult result <;> rfl
    _ = _ := by
      simpa only [Functor.map_map, Function.comp_def] using
        (evalDist_map_eq_of_evalDist_eq hdist (fun result => result.bind (fun pair => privateTrackedCandidate target pair.1 pair.2))).symm

theorem evalDist_privateResolvedTrackedCandidate_completePrivatePosition
    (target : Position) (output : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (hclean : ¬context.state.hitAt (.position target) output) :
    evalDist (privateResolvedSelectedCandidate target (privateTrackedCandidate target) <$>
      runPrivateResolvedView target table (completePrivatePosition target context output).toDeferredContext fuel
        (trackPrivateProbeHistory target (privatePositionProbeCutAt target computation ordinal) (context.state.pendingAt (.position target)))) =
      evalDist ((fun record => (record.bind (privateProbeRecordCandidate target)).map (fun digest => (output, digest))) <$>
        runPrivateProbeRecords target computation context fuel table ordinal output) := by
  let tracked := trackPrivateProbeHistory target (privatePositionProbeCutAt target computation ordinal) (context.state.pendingAt (.position target))
  have hprevalid := hvalid.replacePrivatePosition target output hstate
  have hprecomplete := hcomplete.replacePrivatePosition target output hstate hclean
  have hinitial : PrivateTargetState target output ∅ (completePrivatePosition target context output).toDeferredContext := by
    refine ⟨hstate, ?_, hhidden, ?_⟩
    · simp [completePrivatePosition, DeferredStructuralValues.install]
    · ext digest
      simp [completePrivatePosition, LazyRevealProbe.State.pendingAt, LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway]
  have hsafe := trackPrivateProbeHistory_query_bound target (privatePositionProbeCutAt target computation ordinal)
    (context.state.pendingAt (.position target)) _ 0 (privatePositionProbeCutAt_no_disclosure target computation ordinal)
  have hcount := trackPrivateProbeHistory_query_bound target (privatePositionProbeCutAt target computation ordinal)
    (context.state.pendingAt (.position target)) _ ordinal (privatePositionProbeCutAt_probe_bound target computation ordinal)
  have hcleanup := evalDist_runResolvedLiveValue_clearPending_known target output table (replacePrivatePosition target output context) fuel tracked
    hprevalid hprecomplete (by simp [DeferredContext.positionValue, replacePrivatePosition, hstate, DeferredStructuralValues.install])
  have hprojection := evalDist_privateProbeRecords_candidate_eq_tracked target output computation context fuel table ordinal hvalid hcomplete hstate hhidden
  rw [evalDist_privateResolvedSelectedCandidate_preloaded target output _ tracked _ fuel table ∅ ordinal hinitial
    (hprevalid.clearPending (.position target)).valuesConsistent (show StartTableAgrees context.state table from startTableAgrees_of_deferredCompletable hcomplete) hsafe hcount]
  have hdist := evalDist_map_eq_of_evalDist_eq hcleanup.symm
    (fun result => result.bind (fun pair => (privateTrackedCandidate target pair.1 pair.2).map (fun digest => (output, digest))))
  calc
    _ = _ := hdist
    _ = _ := by
      have heq := evalDist_map_eq_of_evalDist_eq hprojection.symm (Option.map (fun digest => (output, digest)))
      simpa only [Functor.map_map, Function.comp_def, Option.map_bind] using heq


theorem evalDist_runPrivateProbeRecords_eq_none_of_initial_hit
    (target : Position) (output : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (hhit : context.state.hitAt (.position target) output) :
    evalDist (runPrivateProbeRecords target computation context fuel table ordinal output) = evalDist (pure none : ProbComp (Option (ResolvedRunResult (PrivateValueCut α)))) := by
  let run := runPrivateProbeRecords target computation context fuel table ordinal output
  have honly (record) (hrecord : record ∈ support run) : record = none := by
    cases record with
    | none => rfl
    | some record =>
        have hhistory := runPrivateProbeRecords_supported_history target computation context fuel table ordinal output hstate hhidden record hrecord
        exact False.elim (hhistory.2.2 (hhistory.1 hhit))
  calc
    _ = evalDist (run >>= fun record => pure record) := by simp [run]
    _ = evalDist (run >>= fun _ => pure none) := by
      apply evalDist_bind_congr
      intro record hrecord
      rw [honly record hrecord]
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails run
      (by simp [run, runPrivateProbeRecords, runPrivateRecords, runResolvedFromTable]) (pure none)

theorem evalDist_privateResolvedTrackedCandidate_eq_sampled
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed) :
    evalDist (privateResolvedSelectedCandidate target (privateTrackedCandidate target) <$>
      runPrivateResolvedView target table context fuel
        (trackPrivateProbeHistory target (privatePositionProbeCutAt target computation ordinal) (context.state.pendingAt (.position target)))) =
      evalDist (privateSampledCandidatePair <$> samplePrivateHistoryGuess
        (runPrivateProbeRecords target computation context fuel table ordinal) (privateProbeRecordCandidate target)) := by
  let tracked := trackPrivateProbeHistory target (privatePositionProbeCutAt target computation ordinal) (context.state.pendingAt (.position target))
  have hdist := evalDist_runPrivateResolvedView_eq_uniform target tracked context fuel table hvalid hcomplete hensured hstate hvalue
  calc
    _ = evalDist (privateResolvedSelectedCandidate target (privateTrackedCandidate target) <$> (do
      let output ← LazyRevealProbe.sampleHashOutput
      if context.state.hitAt (.position target) output then pure none
      else runPrivateResolvedView target table (completePrivatePosition target context output).toDeferredContext fuel tracked)) :=
        evalDist_map_eq_of_evalDist_eq hdist _
    _ = _ := by
      unfold samplePrivateHistoryGuess
      simp only [map_eq_bind_pure_comp, bind_assoc]
      apply evalDist_bind_congr
      intro output _
      by_cases hhit : context.state.hitAt (.position target) output
      · simp only [if_pos hhit, pure_bind, Function.comp_apply, privateResolvedSelectedCandidate]
        have hnone := evalDist_runPrivateProbeRecords_eq_none_of_initial_hit target output computation context fuel table ordinal hstate hhidden hhit
        have hmapped := evalDist_map_eq_of_evalDist_eq hnone
          (fun record => (record.bind (privateProbeRecordCandidate target)).map (fun digest => (output, digest)))
        simpa only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, privateSampledCandidatePair,
          Option.bind_none, Option.map_none] using hmapped.symm
      · simp only [if_neg hhit]
        have htransport := evalDist_privateResolvedTrackedCandidate_completePrivatePosition target output computation context fuel table ordinal
          hvalid hcomplete hstate hhidden hhit
        simpa only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, privateSampledCandidatePair] using htransport


theorem probEvent_privateResolvedTrackedCandidate_hit_le_charge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed)
    (hcard : (context.state.pendingAt (.position target)).card + ordinal ≤ 2 ^ 126) :
    Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateTrackedCandidate target) <$>
      runPrivateResolvedView target table context fuel
        (trackPrivateProbeHistory target (privatePositionProbeCutAt target computation ordinal) (context.state.pendingAt (.position target)))] ≤
      sampledPrivateProbeCharge target computation context fuel table ordinal *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  have hdist := evalDist_privateResolvedTrackedCandidate_eq_sampled target computation context fuel table ordinal
    hvalid hcomplete hensured hstate hvalue hhidden
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hdist, probEvent_map]
  have hevent (pair : HashOutput × Option Digest) : PrivateCandidatePairHit (privateSampledCandidatePair pair) ↔
      pair.2 = some (truncateHash pair.1) := by
    rcases pair with ⟨output, candidate⟩
    cases candidate <;> simp [privateSampledCandidatePair, PrivateCandidatePairHit]
  have hprob := probEvent_congr' (fun pair _ => hevent pair)
    (rfl : evalDist (samplePrivateHistoryGuess (runPrivateProbeRecords target computation context fuel table ordinal)
      (privateProbeRecordCandidate target)) = _)
  simp only [Function.comp_def]
  rw [hprob]
  exact probEvent_samplePrivateProbeRecords_hit_le_charge target computation context fuel table ordinal hstate hhidden hcard

theorem probEvent_privateResolvedTrackedCandidate_occurrence_eq_charge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed) :
    Pr[fun pair => pair ≠ none | privateResolvedSelectedCandidate target (privateTrackedCandidate target) <$>
      runPrivateResolvedView target table context fuel
        (trackPrivateProbeHistory target (privatePositionProbeCutAt target computation ordinal) (context.state.pendingAt (.position target)))] =
      sampledPrivateProbeCharge target computation context fuel table ordinal := by
  have hdist := evalDist_privateResolvedTrackedCandidate_eq_sampled target computation context fuel table ordinal
    hvalid hcomplete hensured hstate hvalue hhidden
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hdist, probEvent_map]
  have hevent (pair : HashOutput × Option Digest) : privateSampledCandidatePair pair ≠ none ↔ pair.2 ≠ none := by
    rcases pair with ⟨output, candidate⟩
    cases candidate <;> simp [privateSampledCandidatePair]
  have hprob := probEvent_congr' (fun pair _ => hevent pair)
    (rfl : evalDist (samplePrivateHistoryGuess (runPrivateProbeRecords target computation context fuel table ordinal)
      (privateProbeRecordCandidate target)) = _)
  simp only [Function.comp_def]
  rw [hprob]
  exact probEvent_samplePrivateProbeRecords_occurrence_eq_charge target computation context fuel table ordinal hstate hhidden

theorem probEvent_privateResolvedTrackedCandidate_hit_le_occurrence
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed)
    (hcard : (context.state.pendingAt (.position target)).card + ordinal ≤ 2 ^ 126) :
    Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateTrackedCandidate target) <$>
      runPrivateResolvedView target table context fuel
        (trackPrivateProbeHistory target (privatePositionProbeCutAt target computation ordinal) (context.state.pendingAt (.position target)))] ≤
      Pr[fun pair => pair ≠ none | privateResolvedSelectedCandidate target (privateTrackedCandidate target) <$>
        runPrivateResolvedView target table context fuel
          (trackPrivateProbeHistory target (privatePositionProbeCutAt target computation ordinal) (context.state.pendingAt (.position target)))] *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  rw [probEvent_privateResolvedTrackedCandidate_occurrence_eq_charge target computation context fuel table ordinal
    hvalid hcomplete hensured hstate hvalue hhidden]
  exact probEvent_privateResolvedTrackedCandidate_hit_le_charge target computation context fuel table ordinal
    hvalid hcomplete hensured hstate hvalue hhidden hcard

end SphincsSecurity.Concrete.OtsProbeSimulation
