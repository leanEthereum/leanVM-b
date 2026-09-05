import SphincsSecurity.Proof.OtsProbePrivateValueProbeTransport

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def privateRawCutCandidate (target : Position) (_remaining : Nat) (cut : PrivateValueCut α) : Option Digest :=
  privatePositionAccessCandidate target (some cut)

def privateRawRecordCandidate (target : Position) (record : ResolvedRunResult (PrivateValueCut α)) : Option Digest :=
  privateRawCutCandidate target record.remaining record.value

theorem evalDist_privateRawProbeRecords_candidate_eq_live_value
    (target : Position) (output : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hstate : context.state.values (.position target) = none) :
    evalDist ((fun record => record.bind (privateRawRecordCandidate target)) <$>
      runPrivateProbeRecords target computation context fuel table ordinal output) =
      evalDist ((fun result => result.bind (fun pair => privateRawCutCandidate target pair.1 pair.2)) <$>
        runResolvedLiveValue table (replacePrivatePosition target output context) fuel (privatePositionProbeCutAt target computation ordinal)) := by
  have hdist := evalDist_runResolvedLiveValue_eq_retained_value table (replacePrivatePosition target output context) fuel
    (privatePositionProbeCutAt target computation ordinal) (hvalid.replacePrivatePosition target output hstate).valuesConsistent
    (show StartTableAgrees context.state table from startTableAgrees_of_deferredCompletable hcomplete)
  calc
    _ = evalDist ((fun result => (retainCompletableResult result).bind
        (fun record => privateRawCutCandidate target record.remaining record.value)) <$>
        runResolvedFromTable (replacePrivatePosition target output context) fuel table (privatePositionProbeCutAt target computation ordinal)) := by
      unfold runPrivateProbeRecords runPrivateRecords
      rw [Functor.map_map]
      congr 2
      funext result
      unfold privateRecordedResult
      cases retainCompletableResult result <;> rfl
    _ = _ := by
      have heq := evalDist_map_eq_of_evalDist_eq hdist (fun result => result.bind (fun pair => privateRawCutCandidate target pair.1 pair.2))
      simpa only [Functor.map_map, Function.comp_def, Option.bind_map] using heq.symm

theorem evalDist_privateResolvedRawCandidate_completePrivatePosition
    (target : Position) (output : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed)
    (hclean : ¬context.state.hitAt (.position target) output) :
    evalDist (privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
      runPrivateResolvedView target table (completePrivatePosition target context output).toDeferredContext fuel
        (privatePositionProbeCutAt target computation ordinal)) =
      evalDist ((fun record => (record.bind (privateRawRecordCandidate target)).map (fun digest => (output, digest))) <$>
        runPrivateProbeRecords target computation context fuel table ordinal output) := by
  have hprevalid := hvalid.replacePrivatePosition target output hstate
  have hprecomplete := hcomplete.replacePrivatePosition target output hstate hclean
  have hinitial : PrivateTargetState target output ∅ (completePrivatePosition target context output).toDeferredContext := by
    refine ⟨hstate, ?_, hhidden, ?_⟩
    · simp [completePrivatePosition, DeferredStructuralValues.install]
    · ext digest
      simp [completePrivatePosition, LazyRevealProbe.State.pendingAt, LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway]
  have hcleanup := evalDist_runResolvedLiveValue_clearPending_known target output table (replacePrivatePosition target output context) fuel
    (privatePositionProbeCutAt target computation ordinal) hprevalid hprecomplete
    (by simp [DeferredContext.positionValue, replacePrivatePosition, hstate, DeferredStructuralValues.install])
  have hprojection := evalDist_privateRawProbeRecords_candidate_eq_live_value target output computation context fuel table ordinal hvalid hcomplete hstate
  rw [evalDist_privateResolvedSelectedCandidate_preloaded target output _ (privatePositionProbeCutAt target computation ordinal) _ fuel table ∅ ordinal hinitial
    (hprevalid.clearPending (.position target)).valuesConsistent
    (show StartTableAgrees context.state table from startTableAgrees_of_deferredCompletable hcomplete)
    (privatePositionProbeCutAt_no_disclosure target computation ordinal) (privatePositionProbeCutAt_probe_bound target computation ordinal)]
  have hdist := evalDist_map_eq_of_evalDist_eq hcleanup.symm
    (fun result => result.bind (fun pair => (privateRawCutCandidate target pair.1 pair.2).map (fun digest => (output, digest))))
  calc
    _ = _ := hdist
    _ = _ := by
      have heq := evalDist_map_eq_of_evalDist_eq hprojection.symm (Option.map (fun digest => (output, digest)))
      simpa only [Functor.map_map, Function.comp_def, Option.map_bind] using heq

theorem evalDist_privateResolvedRawCandidate_eq_sampled
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed) :
    evalDist (privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
      runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)) =
      evalDist (privateSampledCandidatePair <$> samplePrivateHistoryGuess
        (runPrivateProbeRecords target computation context fuel table ordinal) (privateRawRecordCandidate target)) := by
  have hdist := evalDist_runPrivateResolvedView_eq_uniform target (privatePositionProbeCutAt target computation ordinal)
    context fuel table hvalid hcomplete hensured hstate hvalue
  calc
    _ = evalDist (privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$> (do
      let output ← LazyRevealProbe.sampleHashOutput
      if context.state.hitAt (.position target) output then pure none
      else
        runPrivateResolvedView target table (completePrivatePosition target context output).toDeferredContext fuel
          (privatePositionProbeCutAt target computation ordinal))) := evalDist_map_eq_of_evalDist_eq hdist _
    _ = _ := by
      unfold samplePrivateHistoryGuess
      simp only [map_eq_bind_pure_comp, bind_assoc]
      apply evalDist_bind_congr
      intro output _
      by_cases hhit : context.state.hitAt (.position target) output
      · simp only [if_pos hhit, pure_bind, Function.comp_apply, privateResolvedSelectedCandidate]
        have hnone := evalDist_runPrivateProbeRecords_eq_none_of_initial_hit target output computation context fuel table ordinal hstate hhidden hhit
        have hmapped := evalDist_map_eq_of_evalDist_eq hnone
          (fun record => (record.bind (privateRawRecordCandidate target)).map (fun digest => (output, digest)))
        simpa only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, privateSampledCandidatePair,
          Option.bind_none, Option.map_none] using hmapped.symm
      · simp only [if_neg hhit]
        have htransport := evalDist_privateResolvedRawCandidate_completePrivatePosition target output computation context fuel table ordinal
          hvalid hcomplete hstate hhidden hhit
        simpa only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, privateSampledCandidatePair] using htransport

theorem probEvent_samplePrivateProbeRecords_raw_hit_eq_fresh_hit
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hstate : context.state.values (.position target) = none) (hhidden : .position target ∉ context.state.revealed) :
    Pr[fun pair => pair.2 = some (truncateHash pair.1) | samplePrivateHistoryGuess
      (runPrivateProbeRecords target computation context fuel table ordinal) (privateRawRecordCandidate target)] =
      Pr[fun pair => pair.2 = some (truncateHash pair.1) | samplePrivateHistoryGuess
        (runPrivateProbeRecords target computation context fuel table ordinal) (privateProbeRecordCandidate target)] := by
  unfold samplePrivateHistoryGuess
  apply probEvent_bind_congr
  intro output _
  apply probEvent_bind_congr
  intro record hrecord
  cases record with
  | none => rfl
  | some record =>
      have hclean := (runPrivateProbeRecords_supported_history target computation context fuel table ordinal output hstate hhidden record hrecord).2.2
      simp only [probEvent_pure, Option.bind_some]
      congr 1
      simp [privateProbeRecordCandidate, privateRawRecordCandidate, privateRawCutCandidate, hclean]

theorem probEvent_privateResolvedRawCandidate_hit_le_charge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed)
    (hcard : (context.state.pendingAt (.position target)).card + ordinal ≤ 2 ^ 126) :
    Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
      runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)] ≤
      sampledPrivateProbeCharge target computation context fuel table ordinal *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  have hdist := evalDist_privateResolvedRawCandidate_eq_sampled target computation context fuel table ordinal
    hvalid hcomplete hensured hstate hvalue hhidden
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hdist, probEvent_map]
  have hevent (pair : HashOutput × Option Digest) : PrivateCandidatePairHit (privateSampledCandidatePair pair) ↔
      pair.2 = some (truncateHash pair.1) := by
    rcases pair with ⟨output, candidate⟩
    cases candidate <;> simp [privateSampledCandidatePair, PrivateCandidatePairHit]
  have hprob := probEvent_congr' (fun pair _ => hevent pair)
    (rfl : evalDist (samplePrivateHistoryGuess (runPrivateProbeRecords target computation context fuel table ordinal)
      (privateRawRecordCandidate target)) = _)
  simp only [Function.comp_def]
  rw [hprob, probEvent_samplePrivateProbeRecords_raw_hit_eq_fresh_hit target computation context fuel table ordinal hstate hhidden]
  exact probEvent_samplePrivateProbeRecords_hit_le_charge target computation context fuel table ordinal hstate hhidden hcard


theorem sampledPrivateProbeCharge_le_raw_occurrence
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed) :
    sampledPrivateProbeCharge target computation context fuel table ordinal ≤
      Pr[fun pair => pair ≠ none | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)] := by
  rw [← probEvent_samplePrivateProbeRecords_occurrence_eq_charge target computation context fuel table ordinal hstate hhidden]
  have hdist := evalDist_privateResolvedRawCandidate_eq_sampled target computation context fuel table ordinal
    hvalid hcomplete hensured hstate hvalue hhidden
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hdist, probEvent_map]
  have hevent (pair : HashOutput × Option Digest) : privateSampledCandidatePair pair ≠ none ↔ pair.2 ≠ none := by
    rcases pair with ⟨output, candidate⟩
    cases candidate <;> simp [privateSampledCandidatePair]
  have hprob := probEvent_congr' (fun pair _ => hevent pair)
    (rfl : evalDist (samplePrivateHistoryGuess (runPrivateProbeRecords target computation context fuel table ordinal)
      (privateRawRecordCandidate target)) = _)
  simp only [Function.comp_def]
  rw [hprob]
  unfold samplePrivateHistoryGuess
  apply probEvent_bind_mono
  intro output _
  apply probEvent_bind_mono
  intro record _
  cases record with
  | none => rfl
  | some record =>
      simp only [probEvent_pure, Option.bind_some]
      by_cases hraw : privateRawRecordCandidate target record = none
      · have hfresh : privateProbeRecordCandidate target record = none := by
          simpa only [privateProbeRecordCandidate, privateRawRecordCandidate, privateRawCutCandidate,
            hraw, Option.filter_none] using congrArg (fun candidate => candidate.filter
              (fun digest => digest ∉ record.context.state.pendingAt (.position target))) hraw
        simp [hraw, hfresh]
      · simp only [ne_eq, hraw, not_false_eq_true, if_true]
        split_ifs <;> simp

def PrivateProbeCutReached (target : Position) (result : Option (ResolvedRunResult (PrivateValueCut α))) : Prop :=
  (privatePositionAccessCandidate target (result.map ResolvedRunResult.value)) ≠ none

theorem probEvent_privateResolvedRawCandidate_occurrence_le_cut_reached
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat) :
    Pr[fun pair => pair ≠ none | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
      runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)] ≤
      Pr[PrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)] := by
  unfold runPrivateResolvedView
  rw [map_bind]
  apply probEvent_bind_le_probEvent
  intro result _ hresult
  cases result with
  | none => simp [privateResolvedSelectedCandidate]
  | some result =>
      have hnone : privateRawCutCandidate target result.remaining result.value = none := by
        simpa only [PrivateProbeCutReached, Option.map_some, privateRawCutCandidate, not_not] using hresult
      unfold privateResolutionResult
      rw [map_bind, probEvent_bind_eq_tsum]
      apply ENNReal.tsum_eq_zero.mpr
      intro resolved
      cases resolved with
      | none => simp [privateResolvedSelectedCandidate]
      | some resolved =>
          by_cases hcomplete : DeferredCompletable table resolved.toDeferredContext
          · simp only [if_pos hcomplete, map_pure, privateResolvedSelectedCandidate, hnone]
            cases resolved.toDeferredContext.positionValue target <;> simp
          · simp [hcomplete, privateResolvedSelectedCandidate]

theorem probEvent_privateResolvedRawCandidate_hit_le_cut_reached
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed)
    (hcard : (context.state.pendingAt (.position target)).card + ordinal ≤ 2 ^ 126) :
    Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
      runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)] ≤
      Pr[PrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)] *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  apply (probEvent_privateResolvedRawCandidate_hit_le_charge target computation context fuel table ordinal
    hvalid hcomplete hensured hstate hvalue hhidden hcard).trans
  exact mul_le_mul' ((sampledPrivateProbeCharge_le_raw_occurrence target computation context fuel table ordinal
    hvalid hcomplete hensured hstate hvalue hhidden).trans
      (probEvent_privateResolvedRawCandidate_occurrence_le_cut_reached target computation context fuel table ordinal)) le_rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
