import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeHistoryCandidateSampling
import SphincsSecurity.Proof.OtsProbeHistoryCompletionInterpreter
import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveClean

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

noncomputable def historyAdaptiveQueryStep
    (input : (LazyRevealProbe.World Coordinate).Domain)
    (next : (LazyRevealProbe.World Coordinate).Range input → DeferredContext → Nat → List Probe →
      ProbComp (Option α))
    (context : DeferredContext) (fuel : Nat) (history : List Probe) : ProbComp (Option α) :=
  match input with
  | .probe coordinate digest =>
      match fuel with
      | 0 => pure none
      | remaining + 1 =>
          if coordinate ∈ context.state.revealed then next () context remaining history
          else
            next () { context with state := context.state.addPending coordinate digest } remaining
              (history ++ [⟨coordinate, digest⟩])
  | input => historyCompletionQueryStep history input (fun output context fuel => next output context fuel history) context fuel

noncomputable def completeResolvedHistory
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (value : α) :
    ProbComp (Option (ResolvedRunResult α)) := do
  let base ← sampleOtsHashTable
  if ChainStartHistoryHit context history base then pure none
  else pure (some ⟨context, fuel, value, completedStartTable context.state base⟩)

noncomputable def runResolvedHistoryAdaptive
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    DeferredContext → Nat → List Probe → ProbComp (Option (ResolvedRunResult α)) :=
  OracleComp.construct
    (fun value context fuel history => completeResolvedHistory context fuel history value)
    (fun input _ next => historyAdaptiveQueryStep input next) computation

theorem runResolvedHistoryAdaptive_query_bind
    (input : (LazyRevealProbe.World Coordinate).Domain)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) :
    runResolvedHistoryAdaptive (OracleSpec.query input >>= next) context fuel history =
      historyAdaptiveQueryStep input (fun output => runResolvedHistoryAdaptive (next output)) context fuel history := rfl

theorem not_completable_of_new_historyHit_addPending
    (context : DeferredContext) (history : List Probe) (coordinate : Coordinate) (digest : Digest)
    (base : OtsSecretIndex → HashOutput)
    (hprior : ¬ChainStartHistoryHit context history base)
    (hnew : ChainStartHistoryHit { context with state := context.state.addPending coordinate digest }
      (history ++ [⟨coordinate, digest⟩]) base) :
    ¬DeferredCompletable (completedStartTable context.state base)
      { context with state := context.state.addPending coordinate digest } := by
  obtain ⟨candidate, hcandidate, hmissing, hhit⟩ := hnew
  rcases List.mem_append.mp hcandidate with hold | hcurrent
  · exact False.elim (hprior ⟨candidate, hold, hmissing, hhit⟩)
  · have heq : candidate = ⟨coordinate, digest⟩ := by simpa only [List.mem_singleton] using hcurrent
    subst candidate
    cases coordinate with
    | position position => simp [ChainStartEntryHit] at hhit
    | chainStart lay tree leafIdx chainIdx =>
        let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
        have hvalue : completedStartTable context.state base index = base index := by
          change context.state.values index.coordinate = none at hmissing
          simp only [completedStartTable, hmissing, Option.getD_none]
        intro hcomplete
        apply hcomplete.not_hitAt_chainStart index
        unfold LazyRevealProbe.State.hitAt
        rw [LazyRevealProbe.State.mem_pendingAt_iff, hvalue]
        have hdigest : truncateHash (base index) = digest := hhit
        rw [hdigest]
        simp [LazyRevealProbe.State.addPending, index, OtsSecretIndex.coordinate]

theorem valuesConsistent_materialize_chainStart
    (context : DeferredContext) (index : OtsSecretIndex) (output : HashOutput)
    (hconsistent : context.ValuesConsistent) :
    ({ context with state := context.state.materialize index.coordinate output } : DeferredContext).ValuesConsistent := by
  intro position value hvalue
  apply hconsistent position value
  simpa [LazyRevealProbe.State.materialize, OtsSecretIndex.coordinate] using hvalue

set_option maxHeartbeats 800000 in
theorem evalDist_history_filtered_runResolved_eq_adaptive_observe
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe)
    (observe : Option (ResolvedRunResult α) → ProbComp β)
    (hobserve : ∀ result, result.context.ValuesConsistent → StartTableAgrees result.context.state result.table →
      ¬DeferredCompletable result.table result.context → evalDist (observe (some result)) = evalDist (observe none))
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hcard : context.state.pending.card + bound < Fintype.card Digest)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound) :
    evalDist ((do
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit context history base then pure none
      else runResolvedFromTable context fuel (completedStartTable context.state base) computation) >>= observe) =
    evalDist (runResolvedHistoryAdaptive computation context fuel history >>= observe) := by
  induction computation using OracleComp.inductionOn generalizing context fuel bound history with
  | pure value =>
      rw [runResolvedHistoryAdaptive, OracleComp.construct_pure, completeResolvedHistory]
      apply congrArg evalDist
      apply congrArg (fun run => run >>= observe)
      apply bind_congr
      intro base
      split_ifs <;> rfl
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [runResolvedHistoryAdaptive_query_bind]
      cases input with
      | uniform n =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep]
          simp_rw [runResolvedFromTable_uniform_query_bind]
          rw [evalDist_bind, evalDist_history_filtered_draw_swap, ← evalDist_bind, bind_assoc, bind_assoc]
          apply evalDist_bind_congr
          intro output _houtput
          exact ih output context fuel bound history hconsistent hcovered hcard
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
      | hashOutput =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep]
          simp_rw [runResolvedFromTable_hashOutput_query_bind]
          rw [evalDist_bind, evalDist_history_filtered_draw_swap, ← evalDist_bind, bind_assoc, bind_assoc]
          apply evalDist_bind_congr
          intro output _houtput
          exact ih output context fuel bound history hconsistent hcovered hcard
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
      | ensure coordinate =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep]
          simp_rw [runResolvedFromTable_ensure_query_bind]
          exact ih () { context with state := context.state.ensure coordinate } fuel bound history hconsistent hcovered hcard
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ())
      | peek coordinate =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep]
          simp_rw [runResolvedFromTable_peek_query_bind]
          exact ih (context.state.values coordinate) context fuel bound history hconsistent hcovered hcard
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 _)
      | publish coordinate =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep]
          simp_rw [runResolvedFromTable_publish_query_bind]
          exact ih () { context with state := context.state.publish coordinate } fuel bound history hconsistent hcovered hcard
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ())
      | probe coordinate digest =>
          have hpositive : 0 < bound := by simpa [LazyRevealProbe.IsProbe] using hbound.1
          have htailBound : (next ()).IsQueryBoundP LazyRevealProbe.IsProbe (bound - 1) := by
            simpa [LazyRevealProbe.IsProbe] using hbound.2 ()
          cases fuel with
          | zero =>
              simp only [historyAdaptiveQueryStep, runResolvedFromTable_probe_query_bind, ite_self, bind_assoc, pure_bind]
              exact evalDist_sampleOtsHashTable_bind_const (observe none)
          | succ fuel =>
              simp only [historyAdaptiveQueryStep]
              simp_rw [runResolvedFromTable_probe_query_bind]
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [if_pos hrevealed]
                exact ih () context fuel (bound - 1) history hconsistent hcovered (by omega) htailBound
              · simp only [if_neg hrevealed]
                let after : DeferredContext := { context with state := context.state.addPending coordinate digest }
                have hcardAfter : after.state.pending.card + (bound - 1) < Fintype.card Digest := by
                  have hle := Finset.card_insert_le (coordinate, digest) context.state.pending
                  change (insert (coordinate, digest) context.state.pending).card + (bound - 1) < _
                  omega
                have hrec := ih () after fuel (bound - 1) (history ++ [⟨coordinate, digest⟩])
                  (hconsistent.addPending coordinate digest) (hcovered.addPending_append history context ⟨coordinate, digest⟩)
                  hcardAfter htailBound
                calc
                  _ = evalDist ((do
                      let base ← sampleOtsHashTable
                      if ChainStartHistoryHit after (history ++ [⟨coordinate, digest⟩]) base then pure none
                      else runResolvedFromTable after fuel (completedStartTable after.state base) (next ())) >>= observe) := by
                    rw [bind_assoc, bind_assoc]
                    apply evalDist_bind_congr
                    intro base _hbase
                    have htable : completedStartTable after.state base = completedStartTable context.state base := rfl
                    rw [htable]
                    by_cases hprior : ChainStartHistoryHit context history base
                    · have hnew : ChainStartHistoryHit after (history ++ [⟨coordinate, digest⟩]) base := by
                        obtain ⟨candidate, hmem, hmissing, hhit⟩ := hprior
                        exact ⟨candidate, List.mem_append_left _ hmem, hmissing, hhit⟩
                      simp only [if_pos hprior, if_pos hnew]
                    · simp only [if_neg hprior]
                      by_cases hnew : ChainStartHistoryHit after (history ++ [⟨coordinate, digest⟩]) base
                      · simp only [if_pos hnew, pure_bind]
                        exact evalDist_runResolved_observe_of_not_completable after fuel _ (next ()) (observe none) observe rfl
                          hobserve (hconsistent.addPending coordinate digest)
                          ((startTableAgrees_completedStartTable context.state base).addPending coordinate digest)
                          (not_completable_of_new_historyHit_addPending context history coordinate digest base hprior hnew)
                      · simp only [if_neg hnew]
                        rfl
                  _ = _ := hrec
      | reveal coordinate =>
          have hcardCurrent : context.state.pending.card < Fintype.card Digest := by omega
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              cases hknown : context.state.values index.coordinate with
              | some output =>
                  have hstep := evalDist_history_filtered_runResolved_revealStart_known context history fuel index output next hknown
                  dsimp only [index, OtsSecretIndex.coordinate] at hstep
                  rw [evalDist_bind, hstep, ← evalDist_bind]
                  have hknown' := hknown
                  dsimp only [index, OtsSecretIndex.coordinate] at hknown'
                  simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, OtsSecretIndex.coordinate, hknown']
                  by_cases hhit : context.state.hitAt (.chainStart lay tree leafIdx chainIdx) output
                  · simp only [if_pos hhit]
                  · simp only [if_neg hhit]
                    apply ih output
                      { context with state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output }
                      fuel bound history (valuesConsistent_materialize_chainStart context index output hconsistent)
                      (hcovered.of_subset (Finset.filter_subset _ _))
                    · have hle := Finset.card_le_card (Finset.filter_subset
                        (fun entry : Coordinate × Digest => entry.1 ≠ .chainStart lay tree leafIdx chainIdx) context.state.pending)
                      exact lt_of_le_of_lt (Nat.add_le_add_right hle bound) hcard
                    · simpa [LazyRevealProbe.IsProbe] using hbound.2 output
              | none =>
                  have hstep := evalDist_history_filtered_runResolved_revealStart_missing context history fuel index next hcovered hknown
                  dsimp only [index, OtsSecretIndex.coordinate] at hstep
                  rw [evalDist_bind, hstep, ← evalDist_bind]
                  have hknown' := hknown
                  dsimp only [index, OtsSecretIndex.coordinate] at hknown'
                  simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, OtsSecretIndex.coordinate, hknown', bind_assoc]
                  apply evalDist_bind_congr
                  intro output _houtput
                  by_cases hhit : ChainStartHistoryOutputHit history ⟨lay, tree, leafIdx, chainIdx⟩ output
                  · simp only [if_pos hhit]
                  · simp only [if_neg hhit]
                    apply ih output
                      { context with state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output }
                      fuel bound history (valuesConsistent_materialize_chainStart context index output hconsistent)
                      (hcovered.of_subset (Finset.filter_subset _ _))
                    · have hle := Finset.card_le_card (Finset.filter_subset
                        (fun entry : Coordinate × Digest => entry.1 ≠ .chainStart lay tree leafIdx chainIdx) context.state.pending)
                      exact lt_of_le_of_lt (Nat.add_le_add_right hle bound) hcard
                    · simpa [LazyRevealProbe.IsProbe] using hbound.2 output
          | position position =>
              rw [evalDist_bind, evalDist_history_filtered_runResolved_revealPosition context history fuel position next hcovered hcardCurrent,
                ← evalDist_bind]
              simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, bind_assoc]
              apply evalDist_bind_congr
              intro option hoption
              cases option with
              | none => rfl
              | some resolved =>
                  apply ih resolved.output
                    { state := context.state.materialize (.position position) resolved.output, values := resolved.values }
                    fuel bound history
                    (hconsistent.materializeResolvedPosition_of (startTableAvoidingPending context) position resolved hoption)
                    (hcovered.of_subset (Finset.filter_subset _ _))
                  · have hle := Finset.card_le_card (Finset.filter_subset
                      (fun entry : Coordinate × Digest => entry.1 ≠ .position position) context.state.pending)
                    exact lt_of_le_of_lt (Nat.add_le_add_right hle bound) hcard
                  · simpa [LazyRevealProbe.IsProbe] using hbound.2 resolved.output

end SphincsSecurity.Concrete.OtsProbeSimulation
