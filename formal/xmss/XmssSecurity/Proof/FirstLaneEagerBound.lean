import XmssSecurity.Proof.FirstLaneHazardEnforcement

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

noncomputable def runEagerQuery
    (table : Index → Digest)
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (fuel : Nat) (input : Query Index)
    (resume : (World Index).Range input → Option EncodingMonitor.State →
      AdaptiveRevealMonitor.State Index → Nat → ProbComp Bool) :
    ProbComp Bool :=
  match input with
  | .uniform n => do
      let output ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
      resume output encodingState chainState fuel
  | .encodingQuery epoch =>
      match fuel with
      | 0 => pure (RevealProbeOracleSimulation.tableHits chainState table)
      | remaining + 1 => do
          let output ← uniformHashOutput
          match encodingState with
          | none => resume output none chainState remaining
          | some state =>
              match CappedEncodingMonitor.State.applyObserved state
                (.query epoch output) with
              | none => resume output none chainState remaining
              | some (nextState, hit) =>
                  if hit then pure true
                  else resume output (some nextState) chainState remaining
  | .encodingSignAttempt epoch => do
      let output ← uniformHashOutput
      match encodingState with
      | none => resume output none chainState fuel
      | some state =>
          match CappedEncodingMonitor.State.applyObserved state
            (.sign epoch output) with
          | none => resume output none chainState fuel
          | some (nextState, hit) =>
              if hit then pure true
              else resume output (some nextState) chainState fuel
  | .probe index target =>
      match fuel with
      | 0 => pure (RevealProbeOracleSimulation.tableHits chainState table)
      | remaining + 1 =>
          match chainState.revealed index with
          | some _ => resume () encodingState chainState remaining
          | none => resume () encodingState
              (chainState.addPending index target) remaining
  | .reveal index =>
      match chainState.revealed index with
      | some value => resume value encodingState chainState fuel
      | none =>
          let value := table index
          if value ∈ chainState.pending index then pure true
          else resume value encodingState (chainState.install index value) fuel

noncomputable def runEagerAction {Control : Type}
    (resume : Option EncodingMonitor.State →
      AdaptiveRevealMonitor.State Index → Nat → Control → ProbComp Bool)
    (table : Index → Digest)
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (fuel : Nat)
    (action : FirstLaneMonitor.ControllerAction Control Index) :
    ProbComp Bool :=
  match action with
  | .stop => pure (RevealProbeOracleSimulation.tableHits chainState table)
  | .skip next =>
      resume encodingState chainState fuel next
  | .encodingQuery epoch next =>
      runEagerQuery table encodingState chainState fuel (.encodingQuery epoch)
        fun output nextEncoding nextChain nextFuel =>
          resume nextEncoding nextChain nextFuel (next output)
  | .encodingSignAttempt epoch next =>
      runEagerQuery table encodingState chainState fuel
        (.encodingSignAttempt epoch)
        fun output nextEncoding nextChain nextFuel =>
          resume nextEncoding nextChain nextFuel (next output)
  | .probe index target next =>
      runEagerQuery table encodingState chainState fuel (.probe index target)
        fun _ nextEncoding nextChain nextFuel =>
          resume nextEncoding nextChain nextFuel (next false)
  | .reveal index next =>
      runEagerQuery table encodingState chainState fuel (.reveal index)
        fun output nextEncoding nextChain nextFuel =>
          resume nextEncoding nextChain nextFuel (next output)

noncomputable def runEager {Control : Type}
    (controller : Control → ProbComp
      (FirstLaneMonitor.ControllerAction Control Index))
    (table : Index → Digest)
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (steps fuel : Nat) (control : Control) : ProbComp Bool :=
  match steps with
  | 0 => pure (RevealProbeOracleSimulation.tableHits chainState table)
  | steps + 1 => do
      let action ← controller control
      runEagerAction
        (fun nextEncoding nextChain nextFuel next =>
          runEager controller table nextEncoding nextChain steps nextFuel next)
        table encodingState chainState fuel action

noncomputable def eagerControllerExperiment {Control : Type}
    (controller : Control → ProbComp
      (FirstLaneMonitor.ControllerAction Control Index))
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (steps fuel : Nat) (control : Control) : ProbComp Bool := do
  let base ← RevealProbeOracleSimulation.eagerTableSample
  runEager controller
    (RevealProbeOracleSimulation.extendTable chainState base)
    encodingState chainState steps fuel control

noncomputable def encodingPendingRisk : Option EncodingMonitor.State → ENNReal
  | none => 0
  | some state => CappedEncodingMonitor.State.pendingRisk state

noncomputable def potential
    (fuel : Nat) (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index) : ENNReal :=
  ((fuel + chainState.pendingCount : Nat) : ENNReal) *
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
    encodingPendingRisk encodingState

theorem evalDist_eagerTableSample_applyObserved {Control : Type}
    (controller : Control → ProbComp
      (FirstLaneMonitor.ControllerAction Control Index))
    (chainState : AdaptiveRevealMonitor.State Index)
    (steps fuel : Nat) (next : HashOutput → Control)
    (applyObserved : HashOutput → Option (EncodingMonitor.State × Bool)) :
    evalDist (RevealProbeOracleSimulation.eagerTableSample >>= fun base =>
      uniformHashOutput >>= fun output =>
        match applyObserved output with
        | none =>
            runEager controller
              (RevealProbeOracleSimulation.extendTable chainState base)
              none chainState steps fuel (next output)
        | some (nextState, hit) =>
            if hit then pure true else
              runEager controller
                (RevealProbeOracleSimulation.extendTable chainState base)
                (some nextState) chainState steps fuel (next output)) =
      evalDist (uniformHashOutput >>= fun output =>
        match applyObserved output with
        | none =>
            eagerControllerExperiment controller none chainState steps fuel
              (next output)
        | some (nextState, hit) =>
            if hit then pure true else
              eagerControllerExperiment controller (some nextState) chainState
                steps fuel (next output)) := by
  rw [OracleComp.DeferredSampling.evalDist_bind_comm]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro output
  cases happly : applyObserved output with
  | none => rfl
  | some result =>
      rcases result with ⟨nextState, hit⟩
      cases hit with
      | false => rfl
      | true =>
          change evalDist
              (RevealProbeOracleSimulation.eagerTableSample >>= fun _ =>
                pure true) = evalDist (pure true)
          exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
            RevealProbeOracleSimulation.eagerTableSample
            (by simp [RevealProbeOracleSimulation.eagerTableSample]) (pure true)

noncomputable def runObserved
    (table : Index → Digest) :
    Option EncodingMonitor.State → AdaptiveRevealMonitor.State Index →
      ActionTrace Index → Bool
  | _encodingState, chainState, [] =>
      RevealProbeOracleSimulation.tableHits chainState table
  | encodingState, chainState, .encoding action :: rest =>
      match encodingState with
      | none => runObserved table none chainState rest
      | some state =>
          match CappedEncodingMonitor.State.applyObserved state action with
          | none => runObserved table none chainState rest
          | some (nextState, hit) =>
              hit || runObserved table (some nextState) chainState rest
  | encodingState, chainState, .chain (.probe index target) :: rest =>
      match chainState.revealed index with
      | some _ => runObserved table encodingState chainState rest
      | none => runObserved table encodingState
          (chainState.addPending index target) rest
  | encodingState, chainState, .chain (.reveal index _value) :: rest =>
      match chainState.revealed index with
      | some _ => runObserved table encodingState chainState rest
      | none =>
          let value := table index
          if value ∈ chainState.pending index then true
          else runObserved table encodingState
            (chainState.install index value) rest

theorem runObserved_eq_projected
    (table : Index → Digest) (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (trace : ActionTrace Index) :
    runObserved table encodingState chainState trace =
      ((match encodingState with
        | none => false
        | some state => CappedEncodingMonitor.runObserved state
            trace.encodingActions) ||
        RevealProbeOracleSimulation.runObserved table chainState
          trace.chainActions) := by
  induction trace generalizing encodingState chainState with
  | nil =>
      cases encodingState <;>
        simp [runObserved, ActionTrace.encodingActions,
          ActionTrace.chainActions, CappedEncodingMonitor.runObserved,
          RevealProbeOracleSimulation.runObserved]
  | cons action trace ih =>
      cases action with
      | encoding action =>
          cases encodingState with
          | none =>
              simpa [runObserved, ActionTrace.encodingActions,
                ActionTrace.chainActions] using ih none chainState
          | some state =>
              cases happly :
                CappedEncodingMonitor.State.applyObserved state action with
              | none =>
                  simpa [runObserved, ActionTrace.encodingActions,
                    ActionTrace.chainActions,
                    CappedEncodingMonitor.runObserved, happly] using
                    ih none chainState
              | some result =>
                  rcases result with ⟨nextState, hit⟩
                  cases hit <;>
                    simp [runObserved, ActionTrace.encodingActions,
                      ActionTrace.chainActions,
                      CappedEncodingMonitor.runObserved, happly,
                      ih (some nextState) chainState]
      | chain action =>
          cases action with
          | probe index target =>
              cases hrevealed : chainState.revealed index with
              | none =>
                  simpa [runObserved, ActionTrace.encodingActions,
                    ActionTrace.chainActions,
                    RevealProbeOracleSimulation.runObserved, hrevealed] using
                    ih encodingState (chainState.addPending index target)
              | some value =>
                  simpa [runObserved, ActionTrace.encodingActions,
                    ActionTrace.chainActions,
                    RevealProbeOracleSimulation.runObserved, hrevealed] using
                    ih encodingState chainState
          | reveal index value =>
              cases hrevealed : chainState.revealed index with
              | some revealed =>
                  simpa [runObserved, ActionTrace.encodingActions,
                    ActionTrace.chainActions,
                    RevealProbeOracleSimulation.runObserved, hrevealed] using
                    ih encodingState chainState
              | none =>
                  by_cases hhit : table index ∈ chainState.pending index
                  · simp [runObserved, ActionTrace.encodingActions,
                      ActionTrace.chainActions,
                      RevealProbeOracleSimulation.runObserved, hrevealed, hhit]
                  · simpa [runObserved, ActionTrace.encodingActions,
                      ActionTrace.chainActions,
                      RevealProbeOracleSimulation.runObserved, hrevealed,
                      hhit] using ih encodingState
                        (chainState.install index (table index))

theorem runObserved_empty_eq_combinedHit
    (table : Index → Digest) (trace : ActionTrace Index) :
    runObserved table (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty trace = true ↔
      CombinedHit table trace := by
  rw [runObserved_eq_projected]
  simp only [Bool.or_eq_true]
  rfl

noncomputable def runStructural
    (table : Index → Digest)
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (fuel : Nat) (computation : OracleComp (World Index) α) : ProbComp Bool :=
  OracleComp.construct
    (C := fun _ => Option EncodingMonitor.State →
      AdaptiveRevealMonitor.State Index → Nat → ProbComp Bool)
    (fun _ _encodingState chainState _fuel =>
      pure (RevealProbeOracleSimulation.tableHits chainState table))
    (fun input _next recursivelyRun encodingState chainState fuel =>
      runEagerQuery table encodingState chainState fuel input recursivelyRun)
    computation encodingState chainState fuel

noncomputable def structuralExperiment
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (fuel : Nat) (computation : OracleComp (World Index) α) : ProbComp Bool := do
  let base ← RevealProbeOracleSimulation.eagerTableSample
  runStructural (RevealProbeOracleSimulation.extendTable chainState base)
    encodingState chainState fuel computation


omit [Fintype Index] [DecidableEq Index] in
theorem exists_isSpecialQueryBoundP
    (computation : OracleComp (World Index) α) :
    ∃ steps, computation.IsQueryBoundP IsSpecialQuery steps := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure result => exact ⟨0, trivial⟩
  | query_bind input next ih =>
      choose bounds hb using ih
      let total := ∑ output, bounds output
      let steps := total + if IsSpecialQuery input then 1 else 0
      refine ⟨steps, ?_⟩
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      constructor
      · by_cases hspecial : IsSpecialQuery input <;>
          simp [steps, hspecial]
      · intro output
        apply (hb output).mono
        have hle : bounds output ≤ total := by
          exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
        by_cases hspecial : IsSpecialQuery input <;>
          simp [steps, hspecial, hle]

theorem evalDist_runEager_controller_eq_runStructural
    (table : Index → Digest)
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (steps fuel : Nat) (computation : OracleComp (World Index) α)
    (hsteps : computation.IsQueryBoundP IsSpecialQuery steps) :
    evalDist (runEager controller table encodingState chainState
      steps fuel computation) =
    evalDist (runStructural table encodingState chainState fuel computation) := by
  induction computation using OracleComp.inductionOn generalizing
      encodingState chainState steps fuel with
  | pure result =>
      cases steps <;>
        simp [runEager, runEagerAction, runEagerQuery, controller,
          runStructural]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hsteps
      cases input with
      | uniform n =>
          cases steps with
          | zero =>
              simp only [runEager]
              change evalDist
                  (pure (RevealProbeOracleSimulation.tableHits chainState table)) =
                evalDist ((liftM (unifSpec.query n) : ProbComp _) >>= fun output =>
                  runStructural table encodingState chainState fuel
                    (next output))
              symm
              calc
                _ = evalDist ((liftM (unifSpec.query n) : ProbComp _) >>=
                    fun _ => pure
                      (RevealProbeOracleSimulation.tableHits chainState table)) := by
                  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                  intro output
                  exact (ih output encodingState chainState 0 fuel
                    (by simpa [IsSpecialQuery] using hsteps.2 output)).symm
                _ = _ :=
                  OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                    (liftM (unifSpec.query n) : ProbComp _)
                    (by simp) (pure
                      (RevealProbeOracleSimulation.tableHits chainState table))
          | succ steps =>
              simp only [runEager, runEagerAction]
              change evalDist ((liftM (unifSpec.query n) : ProbComp _) >>=
                  fun output => runEager controller table encodingState
                    chainState (steps + 1) fuel (next output)) =
                evalDist ((liftM (unifSpec.query n) : ProbComp _) >>= fun output =>
                  runStructural table encodingState chainState fuel
                    (next output))
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro output
              exact ih output encodingState chainState (steps + 1) fuel
                (by simpa [IsSpecialQuery] using hsteps.2 output)
      | encodingQuery epoch =>
          cases steps with
          | zero => simp [IsSpecialQuery] at hsteps
          | succ steps =>
              simp only [runEager, runEagerAction]
              cases fuel with
              | zero => simp [controller, runStructural, runEagerQuery]
              | succ remaining =>
                  simp only [controller, runStructural, runEagerQuery,
                    OracleComp.construct_query_bind,
                    pure_bind]
                  change evalDist (uniformHashOutput >>= fun output =>
                      match encodingState with
                      | none => runEager controller table none chainState steps
                          remaining (next output)
                      | some state =>
                          match CappedEncodingMonitor.State.applyObserved state
                            (.query epoch output) with
                          | none => runEager controller table none chainState
                              steps remaining (next output)
                          | some (nextState, hit) =>
                              if hit then pure true else runEager controller table
                                (some nextState) chainState steps remaining
                                  (next output)) = _
                  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                  intro output
                  cases encodingState with
                  | none =>
                      exact ih output none chainState steps remaining
                        (by simpa [IsSpecialQuery] using hsteps.2 output)
                  | some state =>
                      cases happly :
                        CappedEncodingMonitor.State.applyObserved state
                          (.query epoch output) with
                      | none =>
                          simp only [happly]
                          change evalDist (runEager controller table none
                              chainState steps remaining (next output)) =
                            evalDist (runStructural table none chainState
                              remaining (next output))
                          exact ih output none chainState steps remaining
                            (by simpa [IsSpecialQuery] using hsteps.2 output)
                      | some result =>
                          rcases result with ⟨nextState, hit⟩
                          cases hit with
                          | false =>
                              simp only [happly]
                              change evalDist (runEager controller table
                                  (some nextState) chainState steps remaining
                                    (next output)) =
                                evalDist (runStructural table (some nextState)
                                  chainState remaining (next output))
                              exact ih output (some nextState) chainState steps
                                remaining
                                (by simpa [IsSpecialQuery] using hsteps.2 output)
                          | true => simp [happly]
      | encodingSignAttempt epoch =>
          cases steps with
          | zero => simp [IsSpecialQuery] at hsteps
          | succ steps =>
              simp only [runEager, runEagerAction, runEagerQuery, controller,
                runStructural,
                OracleComp.construct_query_bind, pure_bind]
              change evalDist (uniformHashOutput >>= fun output =>
                  match encodingState with
                  | none => runEager controller table none chainState steps fuel
                      (next output)
                  | some state =>
                      match CappedEncodingMonitor.State.applyObserved state
                        (.sign epoch output) with
                      | none => runEager controller table none chainState steps
                          fuel (next output)
                      | some (nextState, hit) =>
                          if hit then pure true else runEager controller table
                            (some nextState) chainState steps fuel
                              (next output)) = _
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro output
              cases encodingState with
              | none =>
                  exact ih output none chainState steps fuel
                    (by simpa [IsSpecialQuery] using hsteps.2 output)
              | some state =>
                  cases happly : CappedEncodingMonitor.State.applyObserved state
                    (.sign epoch output) with
                  | none =>
                      simp only [happly]
                      change evalDist (runEager controller table none chainState
                          steps fuel (next output)) =
                        evalDist (runStructural table none chainState fuel
                          (next output))
                      exact ih output none chainState steps fuel
                        (by simpa [IsSpecialQuery] using hsteps.2 output)
                  | some result =>
                      rcases result with ⟨nextState, hit⟩
                      cases hit with
                      | false =>
                          simp only [happly]
                          change evalDist (runEager controller table
                              (some nextState) chainState steps fuel
                                (next output)) =
                            evalDist (runStructural table (some nextState)
                              chainState fuel (next output))
                          exact ih output (some nextState) chainState steps fuel
                            (by simpa [IsSpecialQuery] using hsteps.2 output)
                      | true => simp [happly]
      | probe index target =>
          cases steps with
          | zero => simp [IsSpecialQuery] at hsteps
          | succ steps =>
              simp only [runEager, runEagerAction, runEagerQuery, controller,
                runStructural,
                OracleComp.construct_query_bind, pure_bind]
              cases fuel with
              | zero => rfl
              | succ remaining =>
                  cases hrevealed : chainState.revealed index with
                  | some value =>
                      exact ih () encodingState chainState steps remaining
                        (by simpa [IsSpecialQuery] using hsteps.2 ())
                  | none =>
                      exact ih () encodingState
                        (chainState.addPending index target) steps remaining
                          (by simpa [IsSpecialQuery] using hsteps.2 ())
      | reveal index =>
          cases steps with
          | zero => simp [IsSpecialQuery] at hsteps
          | succ steps =>
              simp only [runEager, runEagerAction, runEagerQuery, controller,
                runStructural,
                OracleComp.construct_query_bind, pure_bind]
              cases hrevealed : chainState.revealed index with
              | some value =>
                  exact ih value encodingState chainState steps fuel
                    (by simpa [IsSpecialQuery] using hsteps.2 value)
              | none =>
                  by_cases hhit : table index ∈ chainState.pending index
                  · simp [hhit]
                  · simp only [hhit, ↓reduceIte]
                    change evalDist (runEager controller table encodingState
                        (chainState.install index (table index)) steps fuel
                          (next (table index))) =
                      evalDist (runStructural table encodingState
                        (chainState.install index (table index)) fuel
                          (next (table index)))
                    exact ih (table index) encodingState
                      (chainState.install index (table index)) steps fuel
                        (by simpa [IsSpecialQuery] using
                          hsteps.2 (table index))

theorem eagerFinalize_true_probability_le
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (hvalid : RevealProbeOracleSimulation.StateValid chainState)
    (fuel : Nat) :
    Pr[(fun hit : Bool => hit = true) |
      (fun base : Index → Digest =>
        RevealProbeOracleSimulation.tableHits chainState
          (RevealProbeOracleSimulation.extendTable chainState base)) <$>
        RevealProbeOracleSimulation.eagerTableSample] ≤
      potential fuel encodingState chainState := by
  refine (RevealProbeOracleSimulation.eagerFinalize_true_probability_le
    chainState hvalid).trans ?_
  unfold potential
  apply le_add_right
  gcongr
  omega

set_option maxRecDepth 100000 in
theorem eagerController_true_probability_le {Control : Type}
    (controller : Control → ProbComp
      (FirstLaneMonitor.ControllerAction Control Index))
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (hvalid : RevealProbeOracleSimulation.StateValid chainState)
    (steps fuel : Nat) (control : Control) :
    Pr[(fun hit : Bool => hit = true) |
      eagerControllerExperiment controller encodingState chainState
        steps fuel control] ≤
      potential fuel encodingState chainState := by
  induction steps generalizing encodingState chainState fuel control with
  | zero =>
      change Pr[(fun hit : Bool => hit = true) |
        (fun base : Index → Digest =>
          RevealProbeOracleSimulation.tableHits chainState
            (RevealProbeOracleSimulation.extendTable chainState base)) <$>
          RevealProbeOracleSimulation.eagerTableSample] ≤ _
      exact eagerFinalize_true_probability_le encodingState chainState hvalid fuel
  | succ steps ih =>
      have hswap :
          evalDist (eagerControllerExperiment controller encodingState
            chainState (steps + 1) fuel control) =
          evalDist (controller control >>= fun action =>
            RevealProbeOracleSimulation.eagerTableSample >>= fun base =>
              let table := RevealProbeOracleSimulation.extendTable chainState base
              runEagerAction
                (fun nextEncoding nextChain nextFuel next =>
                  runEager controller table nextEncoding nextChain steps
                    nextFuel next)
                table encodingState chainState fuel action) := by
        change evalDist
            (RevealProbeOracleSimulation.eagerTableSample >>= fun base =>
              controller control >>= fun action =>
                let table :=
                  RevealProbeOracleSimulation.extendTable chainState base
                runEagerAction
                  (fun nextEncoding nextChain nextFuel next =>
                    runEager controller table nextEncoding nextChain steps
                      nextFuel next)
                  table encodingState chainState fuel action) = _
        exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
      refine (probEvent_congr' (fun _ _ => Iff.rfl) hswap).le.trans ?_
      refine probEvent_bind_le_of_forall_le fun action _haction => ?_
      cases action with
      | stop =>
          change Pr[(fun hit : Bool => hit = true) |
            (fun base : Index → Digest =>
              RevealProbeOracleSimulation.tableHits chainState
                (RevealProbeOracleSimulation.extendTable chainState base)) <$>
              RevealProbeOracleSimulation.eagerTableSample] ≤ _
          exact eagerFinalize_true_probability_le encodingState chainState
            hvalid fuel
      | skip next =>
          change Pr[(fun hit : Bool => hit = true) |
            eagerControllerExperiment controller encodingState chainState
              steps fuel next] ≤ _
          exact ih encodingState chainState hvalid fuel next
      | encodingQuery epoch next =>
          cases fuel with
          | zero =>
              simp only [runEagerAction, runEagerQuery]
              exact eagerFinalize_true_probability_le encodingState chainState
                hvalid 0
          | succ remaining =>
              simp only [runEagerAction, runEagerQuery]
              cases encodingState with
              | none =>
                  let continuation := fun output : HashOutput =>
                    eagerControllerExperiment controller none chainState steps
                      remaining (next output)
                  have hdist :
                      evalDist (RevealProbeOracleSimulation.eagerTableSample >>=
                        fun base => uniformHashOutput >>= fun output =>
                          runEager controller
                            (RevealProbeOracleSimulation.extendTable chainState base)
                            none chainState steps remaining (next output)) =
                      evalDist (uniformHashOutput >>= continuation) := by
                    simpa [continuation] using
                      evalDist_eagerTableSample_applyObserved controller
                        chainState steps remaining next fun _ => none
                  refine (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans ?_
                  refine probEvent_bind_le_of_forall_le fun output _ => ?_
                  refine (ih none chainState hvalid remaining
                    (next output)).trans ?_
                  unfold potential encodingPendingRisk
                  gcongr
                  omega
              | some state =>
                  let continuation := fun output nextState =>
                    eagerControllerExperiment controller (some nextState)
                      chainState steps remaining (next output)
                  let observed := fun output : HashOutput =>
                    match CappedEncodingMonitor.State.applyObserved state
                      (.query epoch output) with
                    | none =>
                        eagerControllerExperiment controller none chainState
                          steps remaining (next output)
                    | some (nextState, hit) =>
                        if hit then pure true else continuation output nextState
                  have hobserved :
                      (uniformHashOutput >>= observed) =
                        CappedEncodingMonitor.applyHashOutputQueryMonitor epoch
                          continuation state := by
                    rw [CappedEncodingMonitor.applyHashOutputQueryMonitor_eq_observed]
                    apply bind_congr
                    intro output
                    cases hsigned : state.signed epoch with
                    | none =>
                        by_cases hdigest :
                            TargetSum.ValidDigest (truncateHash output) <;>
                          simp [observed, continuation,
                            CappedEncodingMonitor.State.applyObserved,
                            hsigned, hdigest]
                    | some target =>
                        by_cases heq : truncateHash output = target <;>
                          simp [observed, continuation,
                            CappedEncodingMonitor.State.applyObserved,
                            hsigned, heq]
                  have hdist :
                      evalDist (RevealProbeOracleSimulation.eagerTableSample >>=
                        fun base => uniformHashOutput >>= fun output =>
                          match CappedEncodingMonitor.State.applyObserved state
                            (.query epoch output) with
                          | none =>
                              runEager controller
                                (RevealProbeOracleSimulation.extendTable
                                  chainState base) none chainState steps remaining
                                    (next output)
                          | some (nextState, hit) =>
                              if hit then pure true
                              else runEager controller
                                (RevealProbeOracleSimulation.extendTable
                                  chainState base) (some nextState) chainState
                                    steps remaining (next output)) =
                      evalDist
                        (CappedEncodingMonitor.applyProgrammedQueryMonitor epoch
                          continuation state) := by
                    calc
                      _ = evalDist (uniformHashOutput >>= observed) := by
                        simpa [observed, continuation] using
                          evalDist_eagerTableSample_applyObserved controller
                            chainState steps remaining next fun output =>
                              CappedEncodingMonitor.State.applyObserved state
                                (.query epoch output)
                      _ = evalDist
                          (CappedEncodingMonitor.applyHashOutputQueryMonitor epoch
                            continuation state) := congrArg evalDist hobserved
                      _ = _ :=
                        CappedEncodingMonitor.applyProgrammedQueryMonitor_evalDist_eq
                          epoch continuation state |>.symm
                  refine (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans ?_
                  simpa [potential, encodingPendingRisk, Nat.succ_add,
                    HiddenValue.card_digest] using
                    CappedEncodingMonitor.applyProgrammedQueryMonitor_true_probability_le
                      epoch continuation state
                        (remaining + chainState.pendingCount)
                        (fun output nextState => by
                          simpa [continuation, potential, encodingPendingRisk,
                            HiddenValue.card_digest] using
                            ih (some nextState) chainState hvalid remaining
                              (next output))
      | encodingSignAttempt epoch next =>
          simp only [runEagerAction, runEagerQuery]
          cases encodingState with
          | none =>
              let continuation := fun output : HashOutput =>
                eagerControllerExperiment controller none chainState steps fuel
                  (next output)
              have hdist :
                  evalDist (RevealProbeOracleSimulation.eagerTableSample >>=
                    fun base => uniformHashOutput >>= fun output =>
                      runEager controller
                        (RevealProbeOracleSimulation.extendTable chainState base)
                        none chainState steps fuel (next output)) =
                  evalDist (uniformHashOutput >>= continuation) := by
                simpa [continuation] using
                  evalDist_eagerTableSample_applyObserved controller
                    chainState steps fuel next fun _ => none
              refine (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans ?_
              exact probEvent_bind_le_of_forall_le fun output _ =>
                ih none chainState hvalid fuel (next output)
          | some state =>
              cases hsigned : state.signed epoch with
              | some target =>
                  let continuation := fun output : HashOutput =>
                    match CappedEncodingMonitor.State.applyObserved state
                      (.sign epoch output) with
                    | none =>
                        eagerControllerExperiment controller none chainState
                          steps fuel (next output)
                    | some (nextState, hit) =>
                        if hit then pure true
                        else eagerControllerExperiment controller
                          (some nextState) chainState steps fuel (next output)
                  have hdist :
                      evalDist (RevealProbeOracleSimulation.eagerTableSample >>=
                        fun base => uniformHashOutput >>= fun output =>
                          match CappedEncodingMonitor.State.applyObserved state
                            (.sign epoch output) with
                          | none =>
                              runEager controller
                                (RevealProbeOracleSimulation.extendTable
                                  chainState base) none chainState steps fuel
                                    (next output)
                          | some (nextState, hit) =>
                              if hit then pure true else
                                runEager controller
                                  (RevealProbeOracleSimulation.extendTable
                                    chainState base) (some nextState) chainState
                                      steps fuel (next output)) =
                      evalDist (uniformHashOutput >>= continuation) := by
                    simpa [continuation] using
                      evalDist_eagerTableSample_applyObserved controller
                        chainState steps fuel next fun output =>
                          CappedEncodingMonitor.State.applyObserved state
                            (.sign epoch output)
                  refine (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans ?_
                  refine probEvent_bind_le_of_forall_le fun output _ => ?_
                  simp [continuation,
                    CappedEncodingMonitor.State.applyObserved, hsigned]
                  by_cases hvalidDigest :
                      TargetSum.ValidDigest (truncateHash output)
                  · simp [hvalidDigest]
                    rw [← probEvent_eq_eq_probOutput]
                    refine (ih none chainState hvalid fuel
                      (next output)).trans ?_
                    simp [potential, encodingPendingRisk]
                  · simp [hvalidDigest]
                    rw [← probEvent_eq_eq_probOutput]
                    exact ih (some state) chainState hvalid fuel (next output)
              | none =>
                  let continuation := fun output nextState =>
                    eagerControllerExperiment controller (some nextState)
                      chainState steps fuel (next output)
                  let observed := fun output : HashOutput =>
                    match CappedEncodingMonitor.State.applyObserved state
                      (.sign epoch output) with
                    | none =>
                        eagerControllerExperiment controller none chainState
                          steps fuel (next output)
                    | some (nextState, hit) =>
                        if hit then pure true else continuation output nextState
                  have hobserved :
                      (uniformHashOutput >>= observed) =
                        CappedEncodingMonitor.applyHashOutputSignAttemptMonitor
                          epoch continuation state := by
                    rw [CappedEncodingMonitor.applyHashOutputSignAttemptMonitor_eq_observed]
                    apply bind_congr
                    intro output
                    by_cases hdigest :
                        TargetSum.ValidDigest (truncateHash output)
                    · by_cases hmem :
                          truncateHash output ∈ state.pending epoch <;>
                        simp [observed, continuation,
                          CappedEncodingMonitor.State.applyObserved, hsigned,
                          hdigest, hmem]
                    · simp [observed, continuation,
                        CappedEncodingMonitor.State.applyObserved, hsigned,
                        hdigest]
                  have hdist :
                      evalDist (RevealProbeOracleSimulation.eagerTableSample >>=
                        fun base => uniformHashOutput >>= fun output =>
                          match CappedEncodingMonitor.State.applyObserved state
                            (.sign epoch output) with
                          | none =>
                              runEager controller
                                (RevealProbeOracleSimulation.extendTable
                                  chainState base) none chainState steps fuel
                                    (next output)
                          | some (nextState, hit) =>
                              if hit then pure true else runEager controller
                                (RevealProbeOracleSimulation.extendTable
                                  chainState base) (some nextState) chainState
                                    steps fuel (next output)) =
                      evalDist
                        (CappedEncodingMonitor.applyProgrammedSignAttemptMonitor
                          epoch continuation state) := by
                    calc
                      _ = evalDist (uniformHashOutput >>= observed) := by
                        simpa [observed, continuation] using
                          evalDist_eagerTableSample_applyObserved controller
                            chainState steps fuel next fun output =>
                              CappedEncodingMonitor.State.applyObserved state
                                (.sign epoch output)
                      _ = evalDist
                          (CappedEncodingMonitor.applyHashOutputSignAttemptMonitor
                            epoch continuation state) := congrArg evalDist hobserved
                      _ = _ :=
                        CappedEncodingMonitor.applyProgrammedSignAttemptMonitor_evalDist_eq
                          epoch continuation state |>.symm
                  refine (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans ?_
                  simpa [potential, encodingPendingRisk,
                    HiddenValue.card_digest] using
                    CappedEncodingMonitor.applyProgrammedSignAttemptMonitor_true_probability_le
                      epoch continuation state
                        (fuel + chainState.pendingCount)
                        (fun output nextState => by
                          simpa [continuation, potential, encodingPendingRisk,
                            HiddenValue.card_digest] using
                            ih (some nextState) chainState hvalid fuel
                              (next output))
      | probe index target next =>
          cases fuel with
          | zero =>
              simp only [runEagerAction, runEagerQuery]
              exact eagerFinalize_true_probability_le encodingState chainState
                hvalid 0
          | succ remaining =>
              cases hrevealed : chainState.revealed index with
              | some value =>
                  simp only [runEagerAction, runEagerQuery, hrevealed]
                  change Pr[(fun hit : Bool => hit = true) |
                    eagerControllerExperiment controller encodingState chainState
                      steps remaining (next false)] ≤ _
                  refine (ih encodingState chainState hvalid remaining
                    (next false)).trans ?_
                  unfold potential
                  gcongr
                  omega
              | none =>
                  simp only [runEagerAction, runEagerQuery, hrevealed]
                  change Pr[(fun hit : Bool => hit = true) |
                    eagerControllerExperiment controller encodingState
                      (chainState.addPending index target) steps remaining
                        (next false)] ≤ _
                  refine (ih encodingState
                    (chainState.addPending index target)
                    (hvalid.addPending index target hrevealed) remaining
                      (next false)).trans ?_
                  unfold potential
                  have hadd := chainState.pendingCount_addPending_le index target
                  have hnat : remaining +
                      (chainState.addPending index target).pendingCount ≤
                    remaining + 1 + chainState.pendingCount := by omega
                  exact add_le_add
                    (mul_le_mul_left
                      (by exact_mod_cast hnat :
                        ((remaining +
                          (chainState.addPending index target).pendingCount : Nat) :
                            ENNReal) ≤
                          ((remaining + 1 + chainState.pendingCount : Nat) :
                            ENNReal)) _)
                    le_rfl
      | reveal index next =>
          cases hrevealed : chainState.revealed index with
          | some value =>
              simp only [runEagerAction, runEagerQuery, hrevealed]
              change Pr[(fun hit : Bool => hit = true) |
                eagerControllerExperiment controller encodingState chainState
                  steps fuel (next value)] ≤ _
              exact ih encodingState chainState hvalid fuel (next value)
          | none =>
              simp only [runEagerAction, runEagerQuery, hrevealed]
              let continuation := fun (base : Index → Digest) =>
                let table :=
                  RevealProbeOracleSimulation.extendTable chainState base
                let value := table index
                if value ∈ chainState.pending index then pure true
                else runEager controller table encodingState
                  (chainState.install index value) steps fuel (next value)
              have hrevealDist :
                  evalDist
                      (RevealProbeOracleSimulation.eagerTableSample >>=
                        continuation) =
                    evalDist (do
                      let value ← $ᵗ Digest
                      let base ← RevealProbeOracleSimulation.eagerTableSample
                      if value ∈ chainState.pending index then pure true
                      else
                        runEager controller
                          (RevealProbeOracleSimulation.extendTable
                            (chainState.install index value) base)
                          encodingState (chainState.install index value) steps fuel
                            (next value)) := by
                unfold RevealProbeOracleSimulation.eagerTableSample
                rw [RevealProbeOracleSimulation.evalDist_uniformTable_eq_bind_update
                  index continuation]
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro value
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro base
                simp only [continuation]
                have htable :=
                  RevealProbeOracleSimulation.extendTable_update_eq_install
                    chainState index value base hrevealed
                rw [htable]
                have hinstalled :
                    RevealProbeOracleSimulation.extendTable
                      (chainState.install index value) base index = value := by
                  simp [RevealProbeOracleSimulation.extendTable,
                    AdaptiveRevealMonitor.State.install]
                rw [hinstalled]
              change Pr[(fun hit : Bool => hit = true) |
                RevealProbeOracleSimulation.eagerTableSample >>=
                  continuation] ≤ _
              refine (probEvent_congr' (fun _ _ => Iff.rfl)
                hrevealDist).le.trans ?_
              refine (probEvent_bind_le_probEvent_add
                (mx := ($ᵗ Digest))
                (my := fun value => do
                  let base ← RevealProbeOracleSimulation.eagerTableSample
                  if value ∈ chainState.pending index then pure true
                  else
                    runEager controller
                      (RevealProbeOracleSimulation.extendTable
                        (chainState.install index value) base)
                      encodingState (chainState.install index value) steps fuel
                        (next value))
                (q := fun hit : Bool => hit = true)
                (p := fun value : Digest => value ∈ chainState.pending index)
                (ε := potential fuel encodingState
                  (chainState.install index 0)) ?_).trans ?_
              · intro value _hvalue hmiss
                simp only [hmiss, ↓reduceIte]
                have hcount :
                    (chainState.install index value).pendingCount =
                      (chainState.install index 0).pendingCount := rfl
                change Pr[(fun hit : Bool => hit = true) |
                  eagerControllerExperiment controller encodingState
                    (chainState.install index value) steps fuel
                      (next value)] ≤ _
                simpa [potential, hcount] using
                  ih encodingState (chainState.install index value)
                    (hvalid.install index value) fuel (next value)
              · refine add_le_add
                  (RevealProbeOracleSimulation.uniformDigest_mem_finset_le
                    (chainState.pending index)) le_rfl |>.trans ?_
                have hconserve :=
                  chainState.pendingCount_install_add index 0
                unfold potential
                calc
                  ((chainState.pending index).card : ENNReal) *
                        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
                      (((fuel +
                          (chainState.install index 0).pendingCount : Nat) :
                            ENNReal) *
                          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
                        encodingPendingRisk encodingState) =
                    ((((chainState.pending index).card +
                        (fuel +
                          (chainState.install index 0).pendingCount) : Nat) :
                          ENNReal) *
                        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
                      encodingPendingRisk encodingState) := by
                        push_cast
                        ring
                  _ ≤ ((fuel + chainState.pendingCount : Nat) : ENNReal) *
                        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
                      encodingPendingRisk encodingState := by
                    have hnat :
                      (chainState.pending index).card +
                          (fuel +
                            (chainState.install index 0).pendingCount) ≤
                        fuel + chainState.pendingCount := by omega
                    have hcast :
                        (((chainState.pending index).card +
                          (fuel +
                            (chainState.install index 0).pendingCount) : Nat) :
                          ENNReal) ≤
                        ((fuel + chainState.pendingCount : Nat) : ENNReal) := by
                      exact_mod_cast hnat
                    exact add_le_add (mul_le_mul_left hcast _) le_rfl

theorem eagerController_empty_true_probability_le {Control : Type}
    (controller : Control → ProbComp
      (FirstLaneMonitor.ControllerAction Control Index))
    (steps fuel : Nat) (control : Control) :
    Pr[(fun hit : Bool => hit = true) |
      eagerControllerExperiment controller (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty steps fuel control] ≤
      (fuel : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  simpa [potential, encodingPendingRisk,
    AdaptiveRevealMonitor.State.pendingCount_empty,
    CappedEncodingMonitor.State.pendingRisk_empty, div_eq_mul_inv] using
      eagerController_true_probability_le controller
        (some EncodingMonitor.State.empty)
        (AdaptiveRevealMonitor.State.empty :
          AdaptiveRevealMonitor.State Index)
        RevealProbeOracleSimulation.stateValid_empty steps fuel control

theorem structuralExperiment_empty_true_probability_le
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    Pr[(fun hit : Bool => hit = true) |
      structuralExperiment (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty fuel computation] ≤
      (fuel : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  obtain ⟨steps, hsteps⟩ := exists_isSpecialQueryBoundP computation
  have hdist :
      evalDist
          (structuralExperiment (some EncodingMonitor.State.empty)
            AdaptiveRevealMonitor.State.empty fuel computation) =
        evalDist
          (eagerControllerExperiment controller
            (some EncodingMonitor.State.empty)
            AdaptiveRevealMonitor.State.empty steps fuel computation) := by
    unfold structuralExperiment eagerControllerExperiment
    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
    intro base
    exact (evalDist_runEager_controller_eq_runStructural
      (RevealProbeOracleSimulation.extendTable
        AdaptiveRevealMonitor.State.empty base)
      (some EncodingMonitor.State.empty)
      AdaptiveRevealMonitor.State.empty steps fuel computation hsteps).symm
  exact (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans
    (eagerController_empty_true_probability_le controller steps fuel
      computation)

end XmssSecurity.FirstLaneOracleSimulation
