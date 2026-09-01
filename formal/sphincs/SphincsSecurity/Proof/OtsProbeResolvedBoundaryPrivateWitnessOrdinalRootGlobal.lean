import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionBoundary

/-!
# Global root boundary

The early clean failure is split before the delayed witness is classified by ordinal or position.
This module contains the probability rule used by that split. The failure event lives on the
comparison run, while the residual event stays on the original run, so later unions cannot copy
the failure term.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

structure CleanProbeObservation where
  coordinate : Coordinate
  candidate : Digest
  valueAtProbe : Option HashOutput
  revealedAtProbe : Bool
deriving DecidableEq

structure ObservedCleanRunResult (alpha : Type) where
  state : LazyRevealProbe.State Coordinate
  remaining : Nat
  value : alpha
  table : OtsSecretIndex → HashOutput
  observations : List CleanProbeObservation

def ObservedCleanRunResult.toClean
    (result : ObservedCleanRunResult α) : CleanRunResult α :=
  ⟨result.state, result.remaining, result.value, result.table⟩

def projectObservedCleanRun :
    Option (ObservedCleanRunResult α) → Option (CleanRunResult α)
  | none => none
  | some result => some result.toClean

noncomputable def runObservedCleanFromTable
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    ProbComp (Option (ObservedCleanRunResult α)) :=
  OracleComp.construct
    (C := fun _ : OracleComp (LazyRevealProbe.World Coordinate) α =>
      List CleanProbeObservation → LazyRevealProbe.State Coordinate → Nat →
        (OtsSecretIndex → HashOutput) →
          ProbComp (Option (ObservedCleanRunResult α)))
    (fun value observations state remaining table =>
      pure (some ⟨state, remaining, value, table, observations⟩))
    (fun input _next recursivelyRun observations state fuel table =>
      match input with
      | .uniform n => do
          let output ← liftM (unifSpec.query n)
          recursivelyRun output observations state fuel table
      | .hashOutput => do
          let output ← LazyRevealProbe.sampleHashOutput
          recursivelyRun output observations state fuel table
      | .ensure coordinate =>
          recursivelyRun () observations (state.ensure coordinate) fuel table
      | .probe coordinate candidate =>
          match fuel with
          | 0 => pure none
          | remaining + 1 =>
              let observation :=
                { coordinate := coordinate
                  candidate := candidate
                  valueAtProbe := state.values coordinate
                  revealedAtProbe := decide (coordinate ∈ state.revealed) }
              let nextObservations := observations ++ [observation]
              if coordinate ∈ state.revealed then
                recursivelyRun () nextObservations state remaining table
              else
                recursivelyRun () nextObservations
                  (state.addPending coordinate candidate) remaining table
      | .peek coordinate =>
          recursivelyRun (state.values coordinate) observations state fuel table
      | .publish coordinate =>
          recursivelyRun () observations (state.publish coordinate) fuel table
      | .reveal coordinate =>
          match state.values coordinate with
          | some output => recursivelyRun output observations state fuel table
          | none =>
              match coordinate with
              | .chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  if state.hitAt coordinate output then
                    pure none
                  else
                    recursivelyRun output observations
                      (state.materialize coordinate output) fuel table
              | .position _ => do
                  let output ← LazyRevealProbe.sampleHashOutput
                  if state.hitAt coordinate output then
                    pure none
                  else
                    recursivelyRun output observations
                      (state.materialize coordinate output) fuel table)
    computation observations state fuel table

theorem runObservedCleanFromTable_probe_query_bind
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (candidate : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runObservedCleanFromTable observations state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.probe coordinate candidate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure none
      | remaining + 1 =>
          let observation : CleanProbeObservation :=
            { coordinate := coordinate
              candidate := candidate
              valueAtProbe := state.values coordinate
              revealedAtProbe := decide (coordinate ∈ state.revealed) }
          let nextObservations := observations ++ [observation]
          if coordinate ∈ state.revealed then
            runObservedCleanFromTable nextObservations state remaining table (next ())
          else
            runObservedCleanFromTable nextObservations
              (state.addPending coordinate candidate) remaining table (next ()) := by
  rfl

set_option maxRecDepth 100000 in
theorem map_projectObservedCleanRun_runObservedCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    projectObservedCleanRun <$>
        runObservedCleanFromTable observations state fuel table computation =
      runCleanFromTable state fuel table computation := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel with
  | pure value =>
      simp [runObservedCleanFromTable, runCleanFromTable, projectObservedCleanRun,
        ObservedCleanRunResult.toClean]
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            runCleanFromTable_uniform_query_bind, map_bind]
          apply bind_congr
          intro output
          exact ih output observations state fuel
      | hashOutput =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            runCleanFromTable_hashOutput_query_bind, map_bind]
          apply bind_congr
          intro output
          exact ih output observations state fuel
      | ensure coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            runCleanFromTable_ensure_query_bind]
          exact ih () observations (state.ensure coordinate) fuel
      | probe coordinate candidate =>
          rw [runObservedCleanFromTable_probe_query_bind,
            runCleanFromTable_probe_query_bind]
          cases fuel with
          | zero => simp [projectObservedCleanRun]
          | succ remaining =>
              let observation : CleanProbeObservation :=
                { coordinate := coordinate
                  candidate := candidate
                  valueAtProbe := state.values coordinate
                  revealedAtProbe := decide (coordinate ∈ state.revealed) }
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte]
                simpa [observation, hrevealed] using
                  (ih () (observations ++ [observation]) state remaining)
              · simp only [hrevealed, ↓reduceIte]
                simpa [observation, hrevealed] using
                  (ih () (observations ++ [observation])
                    (state.addPending coordinate candidate) remaining)
      | peek coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            runCleanFromTable_peek_query_bind]
          exact ih (state.values coordinate) observations state fuel
      | publish coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            runCleanFromTable_publish_query_bind]
          exact ih () observations (state.publish coordinate) fuel
      | reveal coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            runCleanFromTable_reveal_query_bind]
          cases hvalue : state.values coordinate with
          | some output =>
              simp only [hvalue]
              exact ih output observations state fuel
          | none =>
              simp only [hvalue]
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : state.hitAt (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit, projectObservedCleanRun]
                  · simp only [output, hhit, ↓reduceIte]
                    exact ih output observations
                      (state.materialize (.chainStart lay tree leafIdx chainIdx) output) fuel
              | position position =>
                  simp only [map_bind]
                  apply bind_congr
                  intro output
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit, projectObservedCleanRun]
                  · simp only [hhit, ↓reduceIte]
                    exact ih output observations
                      (state.materialize (.position position) output) fuel

noncomputable def finishObservedCleanRunFromTable :
    Option (ObservedCleanRunResult α) →
      ProbComp (Option (ObservedCleanRunResult α))
  | none => pure none
  | some result => do
      let finalized ← finalizeCleanFromTable result.state.coordinates.toList
        result.state result.table
      match finalized with
      | none => pure none
      | some (finalState, finalTable) =>
          pure (some
            ⟨finalState, result.remaining, result.value, finalTable, result.observations⟩)

theorem map_projectObservedCleanRun_finishObservedCleanRunFromTable
    (result : Option (ObservedCleanRunResult α)) :
    projectObservedCleanRun <$> finishObservedCleanRunFromTable result =
      finishCleanRunFromTable (projectObservedCleanRun result) := by
  cases result with
  | none => simp [finishObservedCleanRunFromTable, finishCleanRunFromTable,
      projectObservedCleanRun]
  | some result =>
      unfold finishObservedCleanRunFromTable finishCleanRunFromTable
      rw [map_bind]
      apply bind_congr
      intro finalized
      cases finalized <;>
        simp [projectObservedCleanRun, ObservedCleanRunResult.toClean]

theorem map_projectObservedCleanRun_bind_finishObservedCleanRunFromTable
    (run : ProbComp (Option (ObservedCleanRunResult α))) :
    projectObservedCleanRun <$> (run >>= finishObservedCleanRunFromTable) =
      (projectObservedCleanRun <$> run) >>= finishCleanRunFromTable := by
  calc
    _ = run >>= fun result =>
        projectObservedCleanRun <$> finishObservedCleanRunFromTable result := map_bind _ _ _
    _ = run >>= fun result =>
        finishCleanRunFromTable (projectObservedCleanRun result) := by
      apply bind_congr
      intro result
      exact map_projectObservedCleanRun_finishObservedCleanRunFromTable result
    _ = _ := by simp [map_eq_bind_pure_comp, bind_assoc]

noncomputable def sampledObservedRootAwareClean
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))) := do
  let base ← sampleOtsHashTable
  let table := completedStartTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) base
  let result ← runObservedCleanFromTable [] LazyRevealProbe.State.empty fuel table
    (rootAwareCleanRetainedRun adversary parameter ftsSecret)
  finishObservedCleanRunFromTable result

set_option maxRecDepth 100000 in
theorem map_projectObservedCleanRun_sampledObservedRootAwareClean
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    projectObservedCleanRun <$>
        sampledObservedRootAwareClean adversary parameter ftsSecret fuel =
      sampledRunThenFinalizeClean
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel
        (rootAwareCleanRetainedRun adversary parameter ftsSecret) := by
  unfold sampledObservedRootAwareClean sampledRunThenFinalizeClean
  rw [map_bind]
  apply bind_congr
  intro base
  dsimp only
  rw [map_projectObservedCleanRun_bind_finishObservedCleanRunFromTable,
    map_projectObservedCleanRun_runObservedCleanFromTable]

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledObservedRootAwareClean_none_le
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    Pr[= none |
        sampledObservedRootAwareClean adversary parameter ftsSecret q] ≤
      (q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ = Pr[= none | projectObservedCleanRun <$>
        sampledObservedRootAwareClean adversary parameter ftsSecret q] := by
      rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map]
      apply OracleComp.probEvent_congr'
      · intro result _hresult
        cases result <;> simp [projectObservedCleanRun]
      · rfl
    _ = Pr[= none | sampledRunThenFinalizeClean
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) q
        (rootAwareCleanRetainedRun adversary parameter ftsSecret)] :=
      OracleComp.probOutput_congr rfl
        (congrArg evalDist
          (map_projectObservedCleanRun_sampledObservedRootAwareClean adversary parameter
            ftsSecret q))
    _ ≤ _ := probEvent_sampledRootAwareCleanRetainedRun_none_le adversary parameter
      ftsSecret q hbound

theorem probEvent_le_failure_add_residual_of_relTriple
    (left : ProbComp α) (right : ProbComp β)
    (relation : α → β → Prop)
    (event residual : α → Prop) (failure : β → Prop)
    (hrel : RelTriple left right relation)
    (hclassify : ∀ leftOutput rightOutput,
      relation leftOutput rightOutput → event leftOutput →
        ¬residual leftOutput → failure rightOutput) :
    Pr[event | left] ≤ Pr[failure | right] + Pr[residual | left] := by
  calc
    _ = Pr[fun output =>
        (event output ∧ residual output) ∨
          (event output ∧ ¬residual output) | left] := by
      apply OracleComp.probEvent_congr'
      intro output _houtput
      tauto
      rfl
    _ ≤ Pr[fun output => event output ∧ residual output | left] +
        Pr[fun output => event output ∧ ¬residual output | left] :=
      probEvent_or_le _ _ _
    _ ≤ Pr[residual | left] + Pr[failure | right] := by
      apply add_le_add
      · apply probEvent_mono
        intro output _houtput hboth
        exact hboth.2
      · apply probEvent_le_of_relTriple hrel
        intro leftOutput rightOutput hrelation hboth
        exact hclassify leftOutput rightOutput hrelation hboth.1 hboth.2
    _ = Pr[failure | right] + Pr[residual | left] := add_comm _ _

end SphincsSecurity.Concrete.OtsProbeSimulation
