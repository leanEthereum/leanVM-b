import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalCommute

/-!
# Fixed-candidate interpreter lift

For one fixed candidate, running any direct resolved computation before the candidate observer
cannot increase its firing probability. Stops contribute zero, while completed runs carry the same
selected structural output through the deferred context.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

noncomputable def finishDirectWitnessPrivateCandidateFire
    (candidate : Probe) : DirectWitnessResult α → ProbComp Bool
  | .stoppedFuel => pure false
  | .stoppedOrdinary => pure false
  | .stoppedPrivate _ => pure false
  | .done result => privateCandidateFire candidate result.context

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_freshPositionWitnessPrivateCandidateFire_le
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
            finishDirectWitnessPrivateCandidateFire candidate] ≤
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
              finishDirectWitnessPrivateCandidateFire candidate] ≤
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
              finishDirectWitnessPrivateCandidateFire candidate] ≤
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
theorem probEvent_runDirectWitnessPrivateCandidateFire_le
    (candidate : Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    Pr[fun hit : Bool => hit = true |
        runDirectResolvedWitnessFromTable context fuel table computation >>=
          finishDirectWitnessPrivateCandidateFire candidate] ≤
      Pr[fun hit : Bool => hit = true | privateCandidateFire candidate context] := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedWitnessFromTable, finishDirectWitnessPrivateCandidateFire]
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
          | zero => simp [finishDirectWitnessPrivateCandidateFire]
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
          | some output =>
              exact ih output context fuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit, finishDirectWitnessPrivateCandidateFire]
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
                      · simp [hprivate, hhit, finishDirectWitnessPrivateCandidateFire]
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
                                finishDirectWitnessPrivateCandidateFire candidate] ≤
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
                      have hfresh := probEvent_freshPositionWitnessPrivateCandidateFire_le
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
                              finishDirectWitnessPrivateCandidateFire candidate) =
                            (LazyRevealProbe.sampleHashOutput >>= fun output =>
                              if context.state.hitAt (.position position) output then
                                pure false
                              else
                                runDirectResolvedWitnessFromTable
                                    { state := context.state.materialize
                                        (.position position) output
                                      values := context.values.install position output }
                                    fuel table (next output) >>=
                                  finishDirectWitnessPrivateCandidateFire candidate) := by
                        apply bind_congr
                        intro output
                        by_cases hhit : context.state.hitAt (.position position) output <;>
                          simp [hhit, finishDirectWitnessPrivateCandidateFire]
                      rw [hnormalize]
                      exact hfresh

end SphincsSecurity.Concrete.OtsProbeSimulation
