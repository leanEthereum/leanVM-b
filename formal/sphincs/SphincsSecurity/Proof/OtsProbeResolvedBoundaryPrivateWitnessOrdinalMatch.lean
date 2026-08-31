import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalUnion

/-!
# Fixed-candidate witness matching

After one candidate ordinal is selected, a private stop is relevant only when its retained position
and output match that candidate. The combined matching-stop or completed-context observer remains
bounded by the candidate's current deferred firing risk.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

def PrivateHitWitness.MatchesCandidate
    (witness : PrivateHitWitness) (candidate : Probe) : Prop :=
  candidate.coordinate = .position witness.position ∧
    truncateHash witness.output = candidate.candidate

noncomputable def finishDirectWitnessPrivateCandidateMatch
    (candidate : Probe) : DirectWitnessResult α → ProbComp Bool
  | .stoppedFuel => pure false
  | .stoppedOrdinary => pure false
  | .stoppedPrivate witness => pure (decide (witness.MatchesCandidate candidate))
  | .done result => privateCandidateFire candidate result.context

theorem probEvent_privateWitnessMatch_le_privateCandidateFire_of_privateValue
    (candidate : Probe) (context : DeferredContext)
    (position : Position) (output : HashOutput)
    (hstate : context.state.values (.position position) = none)
    (hprivate : context.values position = some output) :
    Pr[= true | (pure (decide ((⟨position, output⟩ : PrivateHitWitness).MatchesCandidate
        candidate)) : ProbComp Bool)] ≤
      Pr[= true | privateCandidateFire candidate context] := by
  cases hcoordinate : candidate.coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [PrivateHitWitness.MatchesCandidate, privateCandidateFire, hcoordinate]
  | position target =>
      by_cases heq : target = position
      · subst target
        unfold privateCandidateFire deferredPositionOutput DeferredContext.positionValue
        simp [PrivateHitWitness.MatchesCandidate, hcoordinate, hstate, hprivate]
      · simp [PrivateHitWitness.MatchesCandidate, privateCandidateFire, hcoordinate, heq]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_freshPositionWitnessPrivateCandidateMatch_le
    (candidate : Probe) (context : DeferredContext) (position : Position)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α)
    (hstate : context.state.values (.position position) = none)
    (hprivate : context.values position = none)
    (htail : ∀ output,
      Pr[fun hit : Bool => hit = true |
          runDirectResolvedWitnessFromTable
              { state := context.state.materialize (.position position) output
                values := context.values.install position output }
              fuel table (next output) >>=
            finishDirectWitnessPrivateCandidateMatch candidate] ≤
        Pr[fun hit : Bool => hit = true | privateCandidateFire candidate
          { state := context.state.materialize (.position position) output
            values := context.values.install position output }]) :
    Pr[fun hit : Bool => hit = true |
        LazyRevealProbe.sampleHashOutput >>= fun output =>
          if context.state.hitAt (.position position) output then
            pure false
          else
            runDirectResolvedWitnessFromTable
                { state := context.state.materialize (.position position) output
                  values := context.values.install position output }
                fuel table (next output) >>=
              finishDirectWitnessPrivateCandidateMatch candidate] ≤
      Pr[fun hit : Bool => hit = true | privateCandidateFire candidate context] := by
  let continuation := fun output : HashOutput =>
    if context.state.hitAt (.position position) output then
      pure false
    else
      privateCandidateFire candidate
        (completePrivatePosition position context output).toDeferredContext
  have hleft :
      Pr[fun hit : Bool => hit = true |
        LazyRevealProbe.sampleHashOutput >>= fun output =>
          if context.state.hitAt (.position position) output then
            pure false
          else
            runDirectResolvedWitnessFromTable
                { state := context.state.materialize (.position position) output
                  values := context.values.install position output }
                fuel table (next output) >>=
              finishDirectWitnessPrivateCandidateMatch candidate] ≤
        Pr[fun hit : Bool => hit = true |
          LazyRevealProbe.sampleHashOutput >>= continuation] := by
    apply probEvent_bind_mono
    intro output _houtput
    by_cases hhit : context.state.hitAt (.position position) output
    · simp [hhit, continuation]
    · simp only [hhit, ↓reduceIte, continuation]
      exact (htail output).trans (le_of_eq (OracleComp.probEvent_congr'
        (fun _ _ => Iff.rfl) (congrArg evalDist
          (privateCandidateFire_materialize_install_eq_complete candidate context position
            output hstate))))
  have hresolve : evalDist
      (LazyRevealProbe.sampleHashOutput >>= continuation) =
        evalDist (resolveThenPrivateCandidateFire position candidate context) := by
    unfold resolveThenPrivateCandidateFire
    rw [resolveDeferredPositionValue_fresh position context hstate hprivate]
    simp only [bind_assoc]
    apply evalDist_bind_congr
    intro output _houtput
    by_cases hhit : context.state.hitAt (.position position) output <;>
      simp [hhit, continuation, completePrivatePosition]
  have hprob :
      Pr[fun hit : Bool => hit = true |
          LazyRevealProbe.sampleHashOutput >>= continuation] =
        Pr[fun hit : Bool => hit = true |
          resolveThenPrivateCandidateFire position candidate context] := by
    rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput]
    exact OracleComp.probOutput_congr rfl hresolve
  have hresolveBound :
      Pr[fun hit : Bool => hit = true |
          resolveThenPrivateCandidateFire position candidate context] ≤
        Pr[fun hit : Bool => hit = true | privateCandidateFire candidate context] := by
    rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput]
    exact probEvent_resolveThenPrivateCandidateFire_le position candidate context
  calc
    _ ≤ Pr[fun hit : Bool => hit = true |
        LazyRevealProbe.sampleHashOutput >>= continuation] := hleft
    _ = Pr[fun hit : Bool => hit = true |
        resolveThenPrivateCandidateFire position candidate context] := hprob
    _ ≤ _ := hresolveBound

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_runDirectWitnessPrivateCandidateMatch_le
    (candidate : Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    Pr[fun hit : Bool => hit = true |
        runDirectResolvedWitnessFromTable context fuel table computation >>=
          finishDirectWitnessPrivateCandidateMatch candidate] ≤
      Pr[fun hit : Bool => hit = true | privateCandidateFire candidate context] := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedWitnessFromTable, finishDirectWitnessPrivateCandidateMatch]
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedWitnessFromTable_uniform_query_bind, bind_assoc]
          apply probEvent_bind_le_of_forall_le
          intro output _houtput
          exact ih output context fuel
      | hashOutput =>
          rw [runDirectResolvedWitnessFromTable_hashOutput_query_bind, bind_assoc]
          apply probEvent_bind_le_of_forall_le
          intro output _houtput
          exact ih output context fuel
      | ensure coordinate =>
          rw [runDirectResolvedWitnessFromTable_ensure_query_bind]
          exact (ih () { context with state := context.state.ensure coordinate } fuel).trans
            (le_of_eq (OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
              (congrArg evalDist (privateCandidateFire_ensure candidate context coordinate))))
      | probe coordinate digest =>
          rw [runDirectResolvedWitnessFromTable_probe_query_bind]
          cases fuel with
          | zero => simp [finishDirectWitnessPrivateCandidateMatch]
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () context remaining
              · simp only [hrevealed, ↓reduceIte]
                exact (ih ()
                  { context with state := context.state.addPending coordinate digest }
                  remaining).trans
                    (le_of_eq (OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
                      (congrArg evalDist
                        (privateCandidateFire_addPending candidate context coordinate digest))))
      | peek coordinate =>
          rw [runDirectResolvedWitnessFromTable_peek_query_bind]
          exact ih (context.state.values coordinate) context fuel
      | publish coordinate =>
          rw [runDirectResolvedWitnessFromTable_publish_query_bind]
          exact (ih () { context with state := context.state.publish coordinate } fuel).trans
            (le_of_eq (OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
              (congrArg evalDist (privateCandidateFire_publish candidate context coordinate))))
      | reveal coordinate =>
          rw [runDirectResolvedWitnessFromTable_reveal_query_bind]
          cases hstate : context.state.values coordinate with
          | some output => exact ih output context fuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit, finishDirectWitnessPrivateCandidateMatch]
                  · simp only [output, hhit, ↓reduceIte]
                    exact (ih output
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output
                        values := context.values }
                      fuel).trans
                        (le_of_eq (OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
                          (congrArg evalDist
                            (privateCandidateFire_materialize_chainStart candidate context lay
                              tree leafIdx chainIdx output))))
              | position position =>
                  cases hprivate : context.values position with
                  | some output =>
                      by_cases hhit : context.state.hitAt (.position position) output
                      · have hmatch :=
                          probEvent_privateWitnessMatch_le_privateCandidateFire_of_privateValue
                            candidate context position output hstate hprivate
                        simpa [hprivate, hhit, finishDirectWitnessPrivateCandidateMatch] using hmatch
                      · simp only [hprivate, hhit, ↓reduceIte]
                        have hvalue : context.positionValue position = some output := by
                          simp [DeferredContext.positionValue, hstate, hprivate]
                        exact (ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values }
                          fuel).trans
                            (le_of_eq (OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
                              (congrArg evalDist
                                (privateCandidateFire_materialize_position_of_positionValue
                                  candidate context position output hvalue))))
                  | none =>
                      simp only [hprivate, bind_assoc]
                      have htail : ∀ output,
                          Pr[fun hit : Bool => hit = true |
                              runDirectResolvedWitnessFromTable
                                  { state := context.state.materialize
                                      (.position position) output
                                    values := context.values.install position output }
                                  fuel table (next output) >>=
                                finishDirectWitnessPrivateCandidateMatch candidate] ≤
                            Pr[fun hit : Bool => hit = true |
                              privateCandidateFire candidate
                                { state := context.state.materialize
                                    (.position position) output
                                  values := context.values.install position output }] := by
                        intro output
                        exact ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values.install position output }
                          fuel
                      have hfresh := probEvent_freshPositionWitnessPrivateCandidateMatch_le
                        (α := α) (candidate := candidate) (context := context)
                        (position := position) (fuel := fuel) (table := table) (next := next)
                        hstate hprivate htail
                      have hnormalize :
                          (LazyRevealProbe.sampleHashOutput >>= fun output =>
                            (if context.state.hitAt (.position position) output then
                              pure (.stoppedOrdinary : DirectWitnessResult α)
                            else
                              runDirectResolvedWitnessFromTable
                                { state := context.state.materialize (.position position) output
                                  values := context.values.install position output }
                                fuel table (next output)) >>=
                              finishDirectWitnessPrivateCandidateMatch candidate) =
                            (LazyRevealProbe.sampleHashOutput >>= fun output =>
                              if context.state.hitAt (.position position) output then
                                pure false
                              else
                                runDirectResolvedWitnessFromTable
                                    { state := context.state.materialize
                                        (.position position) output
                                      values := context.values.install position output }
                                    fuel table (next output) >>=
                                  finishDirectWitnessPrivateCandidateMatch candidate) := by
                        apply bind_congr
                        intro output
                        by_cases hhit : context.state.hitAt (.position position) output <;>
                          simp [hhit, finishDirectWitnessPrivateCandidateMatch]
                      rw [hnormalize]
                      exact hfresh

end SphincsSecurity.Concrete.OtsProbeSimulation
