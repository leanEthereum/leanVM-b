import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.Honest

/-!
# Lazy hidden values with selective reveals

An honest computation may reserve an opaque cell without sampling its value. A later materialization
samples the cell and checks every earlier probe. A separate publication marks values returned by a
successful computation as public. Cells that remain hidden are sampled only when the experiment
finishes. Thus the construction stays lazy: no random-oracle table is sampled in advance.

Every probe against a hidden cell contributes one candidate. Reveals and finalization consume all
candidates at a cell against one fresh uniform hash output, so the total hit probability is at most
the number of probes times `2^-128`.
-/

namespace SphincsSecurity.LazyRevealProbe

open OracleComp OracleSpec ENNReal

variable {Coordinate : Type} [DecidableEq Coordinate]

structure State (Coordinate : Type) where
  pending : Finset (Coordinate × Digest)
  values : Coordinate → Option HashOutput
  revealed : Finset Coordinate
  ensured : Finset Coordinate

def State.empty : State Coordinate :=
  { pending := ∅
    values := fun _ => none
    revealed := ∅
    ensured := ∅ }

def State.Valid (state : State Coordinate) : Prop :=
  ∀ coordinate, coordinate ∈ state.revealed ↔ state.values coordinate ≠ none

def State.pendingAt (state : State Coordinate) (coordinate : Coordinate) : Finset Digest :=
  (state.pending.filter fun entry => entry.1 = coordinate).image Prod.snd

def State.pendingAway (state : State Coordinate) (coordinate : Coordinate) :
    Finset (Coordinate × Digest) :=
  state.pending.filter fun entry => entry.1 ≠ coordinate

def State.addPending (state : State Coordinate) (coordinate : Coordinate)
    (candidate : Digest) : State Coordinate :=
  { state with pending := insert (coordinate, candidate) state.pending }

def State.ensure (state : State Coordinate) (coordinate : Coordinate) : State Coordinate :=
  { state with ensured := insert coordinate state.ensured }

def State.install (state : State Coordinate) (coordinate : Coordinate)
    (output : HashOutput) : State Coordinate :=
  { pending := state.pendingAway coordinate
    values := Function.update state.values coordinate (some output)
    revealed := insert coordinate state.revealed
    ensured := insert coordinate state.ensured }

def State.materialize (state : State Coordinate) (coordinate : Coordinate)
    (output : HashOutput) : State Coordinate :=
  { state with
    pending := state.pendingAway coordinate
    values := Function.update state.values coordinate (some output)
    ensured := insert coordinate state.ensured }

def State.publish (state : State Coordinate) (coordinate : Coordinate) : State Coordinate :=
  { state with revealed := insert coordinate state.revealed }

def State.complete (state : State Coordinate) (coordinate : Coordinate)
    (output : HashOutput) : State Coordinate :=
  { state with
    pending := state.pendingAway coordinate
    values := Function.update state.values coordinate (some output) }

def State.clearPending (state : State Coordinate) (coordinate : Coordinate) : State Coordinate :=
  { state with pending := state.pendingAway coordinate }

def State.coordinates (state : State Coordinate) : Finset Coordinate :=
  state.ensured ∪ state.pending.image Prod.fst

def State.hitAt (state : State Coordinate) (coordinate : Coordinate)
    (output : HashOutput) : Prop :=
  truncateHash output ∈ state.pendingAt coordinate

noncomputable instance instDecidableHitAt (state : State Coordinate) (coordinate : Coordinate)
    (output : HashOutput) : Decidable (state.hitAt coordinate output) :=
  Classical.propDecidable _

theorem State.pendingAt_card_le (state : State Coordinate) (coordinate : Coordinate) :
    (state.pendingAt coordinate).card ≤
      (state.pending.filter fun entry => entry.1 = coordinate).card := by
  exact Finset.card_image_le

theorem State.pendingAway_card_add_filter_card (state : State Coordinate)
    (coordinate : Coordinate) :
    (state.pendingAway coordinate).card +
        (state.pending.filter fun entry => entry.1 = coordinate).card =
      state.pending.card := by
  simpa [State.pendingAway, add_comm] using
    (Finset.card_filter_add_card_filter_not
      (s := state.pending) (p := fun entry : Coordinate × Digest => entry.1 = coordinate))

theorem State.pendingAway_card_add_pendingAt_card_le (state : State Coordinate)
    (coordinate : Coordinate) :
    (state.pendingAway coordinate).card + (state.pendingAt coordinate).card ≤
      state.pending.card := by
  rw [← state.pendingAway_card_add_filter_card coordinate]
  gcongr
  exact state.pendingAt_card_le coordinate

theorem State.Valid.install {state : State Coordinate} (hvalid : state.Valid)
    (coordinate : Coordinate) (output : HashOutput) :
    (state.install coordinate output).Valid := by
  intro other
  by_cases heq : other = coordinate
  · subst other
    simp [State.install]
  · simp only [State.install, Finset.mem_insert, Function.update_of_ne heq,
      heq, false_or]
    exact hvalid other

noncomputable def sampleHashOutput : ProbComp HashOutput :=
  $ᵗ HashOutput

inductive Query (Coordinate : Type) where
  | uniform (n : Nat)
  | hashOutput
  | ensure (coordinate : Coordinate)
  | probe (coordinate : Coordinate) (candidate : Digest)
  | peek (coordinate : Coordinate)
  | publish (coordinate : Coordinate)
  | reveal (coordinate : Coordinate)

@[reducible] def World (Coordinate : Type) : OracleSpec (Query Coordinate) :=
  OracleSpec.ofFn fun
  | .uniform n => Fin (n + 1)
  | .hashOutput => HashOutput
  | .ensure _ => Unit
  | .probe _ _ => Unit
  | .peek _ => Option HashOutput
  | .publish _ => Unit
  | .reveal _ => HashOutput

def IsProbe : (World Coordinate).Domain → Prop
  | .uniform _ => False
  | .hashOutput => False
  | .ensure _ => False
  | .probe _ _ => True
  | .peek _ => False
  | .publish _ => False
  | .reveal _ => False

noncomputable instance instDecidablePredDomainQueryWorldIsProbe : DecidablePred (IsProbe (Coordinate := Coordinate)) :=
  fun input => match input with
  | .uniform _ => isFalse (by simp [IsProbe])
  | .hashOutput => isFalse (by simp [IsProbe])
  | .ensure _ => isFalse (by simp [IsProbe])
  | .probe _ _ => isTrue (by simp [IsProbe])
  | .peek _ => isFalse (by simp [IsProbe])
  | .publish _ => isFalse (by simp [IsProbe])
  | .reveal _ => isFalse (by simp [IsProbe])

def uniformQuery (n : Nat) : OracleComp (World Coordinate) (Fin (n + 1)) :=
  liftM ((World Coordinate).query (.uniform n))

def hashOutputQuery : OracleComp (World Coordinate) HashOutput :=
  liftM ((World Coordinate).query .hashOutput)

def ensureQuery (coordinate : Coordinate) : OracleComp (World Coordinate) Unit :=
  liftM ((World Coordinate).query (.ensure coordinate))

def probeQuery (coordinate : Coordinate) (candidate : Digest) :
    OracleComp (World Coordinate) Unit :=
  liftM ((World Coordinate).query (.probe coordinate candidate))

def peekQuery (coordinate : Coordinate) :
    OracleComp (World Coordinate) (Option HashOutput) :=
  liftM ((World Coordinate).query (.peek coordinate))

def publishQuery (coordinate : Coordinate) : OracleComp (World Coordinate) Unit :=
  liftM ((World Coordinate).query (.publish coordinate))

def revealQuery (coordinate : Coordinate) : OracleComp (World Coordinate) HashOutput :=
  liftM ((World Coordinate).query (.reveal coordinate))

omit [DecidableEq Coordinate] in
theorem ensureQuery_isProbeBound (coordinate : Coordinate) (fuel : Nat) :
    (ensureQuery coordinate).IsQueryBoundP IsProbe fuel := by
  rw [ensureQuery, OracleComp.isQueryBoundP_query_iff]
  simp [IsProbe]

omit [DecidableEq Coordinate] in
theorem probeQuery_isProbeBound (coordinate : Coordinate) (candidate : Digest) :
    (probeQuery coordinate candidate).IsQueryBoundP IsProbe 1 := by
  rw [probeQuery, OracleComp.isQueryBoundP_query_iff]
  simp [IsProbe]

omit [DecidableEq Coordinate] in
theorem peekQuery_isProbeBound (coordinate : Coordinate) (fuel : Nat) :
    (peekQuery coordinate).IsQueryBoundP IsProbe fuel := by
  rw [peekQuery, OracleComp.isQueryBoundP_query_iff]
  simp [IsProbe]

omit [DecidableEq Coordinate] in
theorem publishQuery_isProbeBound (coordinate : Coordinate) (fuel : Nat) :
    (publishQuery coordinate).IsQueryBoundP IsProbe fuel := by
  rw [publishQuery, OracleComp.isQueryBoundP_query_iff]
  simp [IsProbe]

omit [DecidableEq Coordinate] in
theorem revealQuery_isProbeBound (coordinate : Coordinate) (fuel : Nat) :
    (revealQuery coordinate).IsQueryBoundP IsProbe fuel := by
  rw [revealQuery, OracleComp.isQueryBoundP_query_iff]
  simp [IsProbe]

omit [DecidableEq Coordinate] in
theorem hashOutputQuery_isProbeBound (fuel : Nat) :
    (hashOutputQuery (Coordinate := Coordinate)).IsQueryBoundP IsProbe fuel := by
  rw [hashOutputQuery, OracleComp.isQueryBoundP_query_iff]
  simp [IsProbe]

noncomputable def finalizeFrom : List Coordinate → State Coordinate → ProbComp Bool
  | [], _ => pure false
  | coordinate :: remaining, state =>
      match state.values coordinate with
      | some _ => finalizeFrom remaining (state.clearPending coordinate)
      | none => do
          let output ← sampleHashOutput
          if state.hitAt coordinate output then
            pure true
          else
            finalizeFrom remaining (state.complete coordinate output)

noncomputable def finalizeDetailedFrom :
    List Coordinate → State Coordinate → ProbComp (Bool × State Coordinate)
  | [], state => pure (false, state)
  | coordinate :: remaining, state =>
      match state.values coordinate with
      | some _ => finalizeDetailedFrom remaining (state.clearPending coordinate)
      | none => do
          let output ← sampleHashOutput
          if state.hitAt coordinate output then
            pure (true, state)
          else
            finalizeDetailedFrom remaining (state.complete coordinate output)

noncomputable def finalizeDetailed (state : State Coordinate) :
    ProbComp (Bool × State Coordinate) :=
  finalizeDetailedFrom state.coordinates.toList state

inductive RawResult (Coordinate : Type) (alpha : Type) where
  | stopped (hit : Bool)
  | done (state : State Coordinate) (remaining : Nat) (value : alpha)

noncomputable def runRaw (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) alpha) :
    ProbComp (RawResult Coordinate alpha) :=
  OracleComp.construct
    (C := fun _ : OracleComp (World Coordinate) alpha =>
      State Coordinate → Nat → ProbComp (RawResult Coordinate alpha))
    (fun value state remaining => pure (.done state remaining value))
    (fun input _next recursivelyRun state fuel =>
      match input with
      | .uniform n => do
          let output ← liftM (unifSpec.query n)
          recursivelyRun output state fuel
      | .hashOutput => do
          let output ← sampleHashOutput
          recursivelyRun output state fuel
      | .ensure coordinate =>
          recursivelyRun () (state.ensure coordinate) fuel
      | .probe coordinate candidate =>
          match fuel with
          | 0 => pure (.stopped false)
          | remaining + 1 =>
              if coordinate ∈ state.revealed then
                recursivelyRun () state remaining
              else
                recursivelyRun () (state.addPending coordinate candidate) remaining
      | .peek coordinate =>
          recursivelyRun (state.values coordinate) state fuel
      | .publish coordinate =>
          recursivelyRun () (state.publish coordinate) fuel
      | .reveal coordinate =>
          match state.values coordinate with
          | some output => recursivelyRun output state fuel
          | none => do
              let output ← sampleHashOutput
              if state.hitAt coordinate output then
                pure (.stopped true)
              else
                recursivelyRun output (state.materialize coordinate output) fuel)
    computation state fuel

theorem runRaw_uniform_query_bind (state : State Coordinate) (fuel n : Nat)
    (next : Fin (n + 1) → OracleComp (World Coordinate) alpha) :
    runRaw state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.uniform n)) :
          OracleComp (World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      runRaw state fuel (next output)) := by
  rw [runRaw, OracleComp.construct_query_bind]
  rfl

theorem runRaw_hashOutput_query_bind (state : State Coordinate) (fuel : Nat)
    (next : HashOutput → OracleComp (World Coordinate) alpha) :
    runRaw state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) .hashOutput) :
          OracleComp (World Coordinate) HashOutput) >>= next) = (do
      let output ← sampleHashOutput
      runRaw state fuel (next output)) := by
  rw [runRaw, OracleComp.construct_query_bind]
  rfl

theorem runRaw_ensure_query_bind (state : State Coordinate) (fuel : Nat)
    (coordinate : Coordinate) (next : Unit → OracleComp (World Coordinate) alpha) :
    runRaw state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.ensure coordinate)) :
          OracleComp (World Coordinate) Unit) >>= next) =
      runRaw (state.ensure coordinate) fuel (next ()) := by
  rw [runRaw, OracleComp.construct_query_bind]
  rfl

theorem runRaw_probe_query_bind (state : State Coordinate) (fuel : Nat)
    (coordinate : Coordinate) (candidate : Digest)
    (next : Unit → OracleComp (World Coordinate) alpha) :
    runRaw state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.probe coordinate candidate)) :
          OracleComp (World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure (.stopped false)
      | remaining + 1 =>
          if coordinate ∈ state.revealed then
            runRaw state remaining (next ())
          else
            runRaw (state.addPending coordinate candidate) remaining (next ()) := by
  rw [runRaw, OracleComp.construct_query_bind]
  rfl

theorem runRaw_peek_query_bind (state : State Coordinate) (fuel : Nat)
    (coordinate : Coordinate)
    (next : Option HashOutput → OracleComp (World Coordinate) alpha) :
    runRaw state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.peek coordinate)) :
          OracleComp (World Coordinate) (Option HashOutput)) >>= next) =
      runRaw state fuel (next (state.values coordinate)) := by
  rw [runRaw, OracleComp.construct_query_bind]
  rfl

theorem runRaw_publish_query_bind (state : State Coordinate) (fuel : Nat)
    (coordinate : Coordinate) (next : Unit → OracleComp (World Coordinate) alpha) :
    runRaw state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.publish coordinate)) :
          OracleComp (World Coordinate) Unit) >>= next) =
      runRaw (state.publish coordinate) fuel (next ()) := by
  rw [runRaw, OracleComp.construct_query_bind]
  rfl

theorem runRaw_reveal_query_bind (state : State Coordinate) (fuel : Nat)
    (coordinate : Coordinate) (next : HashOutput → OracleComp (World Coordinate) alpha) :
    runRaw state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.reveal coordinate)) :
          OracleComp (World Coordinate) HashOutput) >>= next) =
      (match state.values coordinate with
      | some output => runRaw state fuel (next output)
      | none => do
          let output ← sampleHashOutput
          if state.hitAt coordinate output then
            pure (.stopped true)
          else
            runRaw (state.materialize coordinate output) fuel (next output)) := by
  rw [runRaw, OracleComp.construct_query_bind]
  rfl

theorem runRaw_bind (state : State Coordinate) (fuel : Nat)
    (left : OracleComp (World Coordinate) alpha)
    (next : alpha → OracleComp (World Coordinate) beta) :
    runRaw state fuel (left >>= next) =
      runRaw state fuel left >>= fun result =>
        match result with
        | .stopped hit => pure (.stopped hit)
        | .done finalState remaining value =>
            runRaw finalState remaining (next value) := by
  induction left using OracleComp.inductionOn generalizing state fuel with
  | pure value => simp [runRaw]
  | query_bind input continuation ih =>
      cases input with
      | uniform n =>
          rw [bind_assoc, runRaw_uniform_query_bind, runRaw_uniform_query_bind]
          simp only [bind_assoc]
          apply bind_congr
          intro output
          exact ih output state fuel
      | hashOutput =>
          rw [bind_assoc, runRaw_hashOutput_query_bind, runRaw_hashOutput_query_bind]
          simp only [bind_assoc]
          apply bind_congr
          intro output
          exact ih output state fuel
      | ensure coordinate =>
          rw [bind_assoc, runRaw_ensure_query_bind, runRaw_ensure_query_bind]
          exact ih () (state.ensure coordinate) fuel
      | probe coordinate candidate =>
          rw [bind_assoc, runRaw_probe_query_bind, runRaw_probe_query_bind]
          cases fuel with
          | zero => simp
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () state remaining
              · simp only [hrevealed, ↓reduceIte]
                exact ih () (state.addPending coordinate candidate) remaining
      | peek coordinate =>
          rw [bind_assoc, runRaw_peek_query_bind, runRaw_peek_query_bind]
          exact ih (state.values coordinate) state fuel
      | publish coordinate =>
          rw [bind_assoc, runRaw_publish_query_bind, runRaw_publish_query_bind]
          exact ih () (state.publish coordinate) fuel
      | reveal coordinate =>
          rw [bind_assoc, runRaw_reveal_query_bind, runRaw_reveal_query_bind]
          cases hvalue : state.values coordinate with
          | some output => exact ih output state fuel
          | none =>
              simp only [bind_assoc]
              apply bind_congr
              intro output
              by_cases hhit : state.hitAt coordinate output
              · simp [hhit]
              · simp only [hhit, ↓reduceIte]
                exact ih output (state.materialize coordinate output) fuel

inductive DetailedResult (Coordinate : Type) (alpha : Type) where
  | stopped (hit : Bool)
  | done (hit : Bool) (state : State Coordinate) (remaining : Nat) (value : alpha)

noncomputable def RawResult.finishDetailed :
    RawResult Coordinate alpha → ProbComp (DetailedResult Coordinate alpha)
  | .stopped hit => pure (.stopped hit)
  | .done state remaining value => do
      let (hit, finalState) ← finalizeDetailed state
      pure (.done hit finalState remaining value)

noncomputable def detailedExperiment (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) alpha) :
    ProbComp (DetailedResult Coordinate alpha) :=
  runRaw state fuel computation >>= RawResult.finishDetailed

end SphincsSecurity.LazyRevealProbe
