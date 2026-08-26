import SphincsSecurity.Proof.EncodingProbability
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Lazy hidden values with selective reveals

An honest computation may reserve an opaque cell without sampling its value. A later reveal samples
the cell, checks every earlier probe, and then makes the value public. Cells that remain hidden are
sampled only when the experiment finishes. Thus the construction stays lazy: no random-oracle table
is sampled in advance.

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

omit [DecidableEq Coordinate] in
theorem State.valid_empty : (State.empty : State Coordinate).Valid := by
  intro coordinate
  simp [State.empty]

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

noncomputable instance (state : State Coordinate) (coordinate : Coordinate)
    (output : HashOutput) : Decidable (state.hitAt coordinate output) :=
  Classical.propDecidable _

theorem State.pendingAt_addPending_self (state : State Coordinate)
    (coordinate : Coordinate) (candidate : Digest) :
    candidate ∈ (state.addPending coordinate candidate).pendingAt coordinate := by
  simp [State.pendingAt, State.addPending]

theorem State.pending_card_addPending_le (state : State Coordinate)
    (coordinate : Coordinate) (candidate : Digest) :
    (state.addPending coordinate candidate).pending.card ≤ state.pending.card + 1 := by
  simpa [State.addPending, Nat.add_comm] using
    Finset.card_insert_le (coordinate, candidate) state.pending

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

theorem State.Valid.addPending {state : State Coordinate} (hvalid : state.Valid)
    (coordinate : Coordinate) (candidate : Digest) :
    (state.addPending coordinate candidate).Valid := by
  simpa [State.Valid, State.addPending] using hvalid

theorem State.Valid.ensure {state : State Coordinate} (hvalid : state.Valid)
    (coordinate : Coordinate) : (state.ensure coordinate).Valid := by
  simpa [State.Valid, State.ensure] using hvalid

omit [DecidableEq Coordinate] in
theorem State.Valid.value_of_revealed {state : State Coordinate} (hvalid : state.Valid)
    {coordinate : Coordinate} (hrevealed : coordinate ∈ state.revealed) :
    ∃ output, state.values coordinate = some output := by
  exact Option.ne_none_iff_exists'.mp ((hvalid coordinate).mp hrevealed)

omit [DecidableEq Coordinate] in
theorem State.Valid.not_revealed_value_none {state : State Coordinate}
    (hvalid : state.Valid) {coordinate : Coordinate}
    (hhidden : coordinate ∉ state.revealed) : state.values coordinate = none := by
  cases hvalue : state.values coordinate with
  | none => rfl
  | some output =>
      exact (hhidden ((hvalid coordinate).mpr (by simp [hvalue]))).elim

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

theorem State.pending_card_ensure (state : State Coordinate) (coordinate : Coordinate) :
    (state.ensure coordinate).pending.card = state.pending.card := rfl

theorem State.pending_card_install (state : State Coordinate) (coordinate : Coordinate)
    (output : HashOutput) :
    (state.install coordinate output).pending.card = (state.pendingAway coordinate).card := rfl

theorem State.pending_card_complete (state : State Coordinate) (coordinate : Coordinate)
    (output : HashOutput) :
    (state.complete coordinate output).pending.card = (state.pendingAway coordinate).card := rfl

theorem State.pending_card_clearPending (state : State Coordinate) (coordinate : Coordinate) :
    (state.clearPending coordinate).pending.card = (state.pendingAway coordinate).card := rfl

noncomputable def sampleHashOutput : ProbComp HashOutput :=
  $ᵗ HashOutput

theorem probEvent_sampleHashOutput_hitAt_le (state : State Coordinate)
    (coordinate : Coordinate) :
    Pr[state.hitAt coordinate | sampleHashOutput] ≤
      ((state.pendingAt coordinate).card : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold State.hitAt sampleHashOutput
  rw [probEvent_uniform_truncateHash_mem]
  rw [show Fintype.card Digest = 2 ^ digestBits by simp]
  rfl

inductive Query (Coordinate : Type) where
  | uniform (n : Nat)
  | hashOutput
  | ensure (coordinate : Coordinate)
  | probe (coordinate : Coordinate) (candidate : Digest)
  | peek (coordinate : Coordinate)
  | reveal (coordinate : Coordinate)

@[reducible] def World (Coordinate : Type) : OracleSpec (Query Coordinate) :=
  OracleSpec.ofFn fun
  | .uniform n => Fin (n + 1)
  | .hashOutput => HashOutput
  | .ensure _ => Unit
  | .probe _ _ => Unit
  | .peek _ => Option HashOutput
  | .reveal _ => HashOutput

def IsProbe : (World Coordinate).Domain → Prop
  | .uniform _ => False
  | .hashOutput => False
  | .ensure _ => False
  | .probe _ _ => True
  | .peek _ => False
  | .reveal _ => False

noncomputable instance : DecidablePred (IsProbe (Coordinate := Coordinate)) :=
  fun input => match input with
  | .uniform _ => isFalse (by simp [IsProbe])
  | .hashOutput => isFalse (by simp [IsProbe])
  | .ensure _ => isFalse (by simp [IsProbe])
  | .probe _ _ => isTrue (by simp [IsProbe])
  | .peek _ => isFalse (by simp [IsProbe])
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

def revealQuery (coordinate : Coordinate) : OracleComp (World Coordinate) HashOutput :=
  liftM ((World Coordinate).query (.reveal coordinate))

def uniformForwardImpl : QueryImpl unifSpec (OracleComp (World Coordinate)) :=
  fun n => uniformQuery n

def liftProbComp (computation : ProbComp alpha) : OracleComp (World Coordinate) alpha :=
  simulateQ uniformForwardImpl computation

omit [DecidableEq Coordinate] in
theorem liftProbComp_isProbeBound (computation : ProbComp alpha) (fuel : Nat) :
    (liftProbComp (Coordinate := Coordinate) computation).IsQueryBoundP IsProbe fuel := by
  induction computation using OracleComp.inductionOn with
  | pure result => trivial
  | query_bind n next ih =>
      rw [liftProbComp, simulateQ_query_bind]
      change (uniformQuery n >>= fun output =>
        liftProbComp (next output)).IsQueryBoundP IsProbe fuel
      rw [uniformQuery, OracleComp.isQueryBoundP_query_bind_iff]
      constructor
      · simp [IsProbe]
      · intro output
        simpa [IsProbe] using ih output

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

noncomputable def finalize (state : State Coordinate) : ProbComp Bool :=
  finalizeFrom state.coordinates.toList state

theorem finalizeFrom_probability_le (coordinates : List Coordinate)
    (state : State Coordinate) :
    Pr[fun hit : Bool => hit = true | finalizeFrom coordinates state] ≤
      (state.pending.card : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction coordinates generalizing state with
  | nil => simp [finalizeFrom]
  | cons coordinate remaining ih =>
      rw [finalizeFrom]
      cases hvalue : state.values coordinate with
      | some output =>
          refine (ih (state.clearPending coordinate)).trans ?_
          have hcard : (state.clearPending coordinate).pending.card ≤ state.pending.card := by
            rw [State.pending_card_clearPending]
            simpa only [State.pendingAway] using
              (Finset.card_filter_le (s := state.pending)
                (p := fun entry : Coordinate × Digest => entry.1 ≠ coordinate))
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) zero_le
      | none =>
          refine (probEvent_bind_le_probEvent_add
            (mx := sampleHashOutput)
            (my := fun output =>
              if state.hitAt coordinate output then pure true
              else finalizeFrom remaining (state.complete coordinate output))
            (q := fun hit : Bool => hit = true)
            (p := state.hitAt coordinate)
            (ε := ((state.pendingAway coordinate).card : ℝ≥0∞) *
              ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
          · intro output _ hmiss
            simp only [hmiss, ↓reduceIte]
            simpa only [State.pending_card_complete] using
              ih (state.complete coordinate output)
          · refine add_le_add (probEvent_sampleHashOutput_hitAt_le state coordinate) le_rfl |>.trans ?_
            calc
              ((state.pendingAt coordinate).card : ℝ≥0∞) *
                    ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
                  ((state.pendingAway coordinate).card : ℝ≥0∞) *
                    ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ =
                (((state.pendingAt coordinate).card +
                    (state.pendingAway coordinate).card : Nat) : ℝ≥0∞) *
                  ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
                    push_cast
                    ring
              _ ≤ (state.pending.card : ℝ≥0∞) *
                    ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
                  have hcard : (state.pendingAt coordinate).card +
                      (state.pendingAway coordinate).card ≤ state.pending.card := by
                    rw [Nat.add_comm]
                    exact state.pendingAway_card_add_pendingAt_card_le coordinate
                  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) zero_le

theorem finalize_probability_le (state : State Coordinate) :
    Pr[fun hit : Bool => hit = true | finalize state] ≤
      (state.pending.card : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
  finalizeFrom_probability_le state.coordinates.toList state

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

theorem finalizeDetailedFrom_fst (coordinates : List Coordinate)
    (state : State Coordinate) :
    Prod.fst <$> finalizeDetailedFrom coordinates state =
      finalizeFrom coordinates state := by
  induction coordinates generalizing state with
  | nil => simp [finalizeDetailedFrom, finalizeFrom]
  | cons coordinate remaining ih =>
      rw [finalizeDetailedFrom, finalizeFrom]
      cases hvalue : state.values coordinate with
      | some output => exact ih (state.clearPending coordinate)
      | none =>
          simp only [map_bind]
          apply bind_congr
          intro output
          by_cases hhit : state.hitAt coordinate output
          · simp [hhit]
          · simp only [hhit, ↓reduceIte]
            exact ih (state.complete coordinate output)

theorem finalizeDetailed_fst (state : State Coordinate) :
    Prod.fst <$> finalizeDetailed state = finalize state :=
  finalizeDetailedFrom_fst state.coordinates.toList state

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
      | .reveal coordinate =>
          match state.values coordinate with
          | some output => recursivelyRun output state fuel
          | none => do
              let output ← sampleHashOutput
              if state.hitAt coordinate output then
                pure (.stopped true)
              else
                recursivelyRun output (state.install coordinate output) fuel)
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
            runRaw (state.install coordinate output) fuel (next output)) := by
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
                exact ih output (state.install coordinate output) fuel

inductive DetailedResult (Coordinate : Type) (alpha : Type) where
  | stopped (hit : Bool)
  | done (hit : Bool) (state : State Coordinate) (remaining : Nat) (value : alpha)

def DetailedResult.hit : DetailedResult Coordinate alpha → Bool
  | .stopped hit => hit
  | .done hit _ _ _ => hit

noncomputable def RawResult.finish : RawResult Coordinate alpha → ProbComp Bool
  | .stopped hit => pure hit
  | .done state _ _ => finalize state

noncomputable def RawResult.finishDetailed :
    RawResult Coordinate alpha → ProbComp (DetailedResult Coordinate alpha)
  | .stopped hit => pure (.stopped hit)
  | .done state remaining value => do
      let (hit, finalState) ← finalizeDetailed state
      pure (.done hit finalState remaining value)

theorem RawResult.finishDetailed_hit (result : RawResult Coordinate alpha) :
    DetailedResult.hit <$> result.finishDetailed = result.finish := by
  cases result with
  | stopped hit => simp [RawResult.finishDetailed, RawResult.finish, DetailedResult.hit]
  | done state remaining value =>
      simpa [RawResult.finishDetailed, RawResult.finish, DetailedResult.hit] using
        finalizeDetailed_fst state

noncomputable def detailedExperiment (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) alpha) :
    ProbComp (DetailedResult Coordinate alpha) :=
  runRaw state fuel computation >>= RawResult.finishDetailed

noncomputable def experiment (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) alpha) : ProbComp Bool :=
  OracleComp.construct
    (C := fun _ => State Coordinate → Nat → ProbComp Bool)
    (fun _ state _ => finalize state)
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
          | 0 => finalize state
          | remaining + 1 =>
              if coordinate ∈ state.revealed then
                recursivelyRun () state remaining
              else
                recursivelyRun () (state.addPending coordinate candidate) remaining
      | .peek coordinate =>
          recursivelyRun (state.values coordinate) state fuel
      | .reveal coordinate =>
          match state.values coordinate with
          | some output => recursivelyRun output state fuel
          | none => do
              let output ← sampleHashOutput
              if state.hitAt coordinate output then
                pure true
              else
                recursivelyRun output (state.install coordinate output) fuel)
    computation state fuel

theorem experiment_uniform_query_bind (state : State Coordinate) (fuel n : Nat)
    (next : Fin (n + 1) → OracleComp (World Coordinate) alpha) :
    experiment state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.uniform n)) :
          OracleComp (World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      experiment state fuel (next output)) := by
  rw [experiment, OracleComp.construct_query_bind]
  rfl

theorem experiment_hashOutput_query_bind (state : State Coordinate) (fuel : Nat)
    (next : HashOutput → OracleComp (World Coordinate) alpha) :
    experiment state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) .hashOutput) :
          OracleComp (World Coordinate) HashOutput) >>= next) = (do
      let output ← sampleHashOutput
      experiment state fuel (next output)) := by
  rw [experiment, OracleComp.construct_query_bind]
  rfl

theorem experiment_ensure_query_bind (state : State Coordinate) (fuel : Nat)
    (coordinate : Coordinate) (next : Unit → OracleComp (World Coordinate) alpha) :
    experiment state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.ensure coordinate)) :
          OracleComp (World Coordinate) Unit) >>= next) =
      experiment (state.ensure coordinate) fuel (next ()) := by
  rw [experiment, OracleComp.construct_query_bind]
  rfl

theorem experiment_probe_query_bind (state : State Coordinate) (fuel : Nat)
    (coordinate : Coordinate) (candidate : Digest)
    (next : Unit → OracleComp (World Coordinate) alpha) :
    experiment state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.probe coordinate candidate)) :
          OracleComp (World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => finalize state
      | remaining + 1 =>
          if coordinate ∈ state.revealed then
            experiment state remaining (next ())
          else
            experiment (state.addPending coordinate candidate) remaining (next ()) := by
  rw [experiment, OracleComp.construct_query_bind]
  rfl

theorem experiment_peek_query_bind (state : State Coordinate) (fuel : Nat)
    (coordinate : Coordinate)
    (next : Option HashOutput → OracleComp (World Coordinate) alpha) :
    experiment state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.peek coordinate)) :
          OracleComp (World Coordinate) (Option HashOutput)) >>= next) =
      experiment state fuel (next (state.values coordinate)) := by
  rw [experiment, OracleComp.construct_query_bind]
  rfl

theorem experiment_reveal_query_bind (state : State Coordinate) (fuel : Nat)
    (coordinate : Coordinate) (next : HashOutput → OracleComp (World Coordinate) alpha) :
    experiment state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.reveal coordinate)) :
          OracleComp (World Coordinate) HashOutput) >>= next) =
      (match state.values coordinate with
      | some output => experiment state fuel (next output)
      | none => do
          let output ← sampleHashOutput
          if state.hitAt coordinate output then
            pure true
          else
            experiment (state.install coordinate output) fuel (next output)) := by
  rw [experiment, OracleComp.construct_query_bind]
  rfl

theorem experiment_eq_runRaw_finish (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) alpha)
    (hbound : computation.IsQueryBoundP IsProbe fuel) :
    experiment state fuel computation =
      runRaw state fuel computation >>= RawResult.finish := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value => simp [experiment, runRaw, RawResult.finish]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | uniform n =>
          rw [experiment_uniform_query_bind, runRaw_uniform_query_bind, bind_assoc]
          apply bind_congr
          intro output
          exact ih output state fuel (by simpa [IsProbe] using hbound.2 output)
      | hashOutput =>
          rw [experiment_hashOutput_query_bind, runRaw_hashOutput_query_bind, bind_assoc]
          apply bind_congr
          intro output
          exact ih output state fuel (by simpa [IsProbe] using hbound.2 output)
      | ensure coordinate =>
          rw [experiment_ensure_query_bind, runRaw_ensure_query_bind]
          exact ih () (state.ensure coordinate) fuel
            (by simpa [IsProbe] using hbound.2 ())
      | probe coordinate candidate =>
          have hpositive : 0 < fuel := by
            simpa [IsProbe] using hbound.1
          cases fuel with
          | zero => omega
          | succ remaining =>
              rw [experiment_probe_query_bind, runRaw_probe_query_bind]
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () state remaining
                  (by simpa [IsProbe] using hbound.2 ())
              · simp only [hrevealed, ↓reduceIte]
                exact ih () (state.addPending coordinate candidate) remaining
                  (by simpa [IsProbe] using hbound.2 ())
      | peek coordinate =>
          rw [experiment_peek_query_bind, runRaw_peek_query_bind]
          exact ih (state.values coordinate) state fuel
            (by simpa [IsProbe] using hbound.2 (state.values coordinate))
      | reveal coordinate =>
          rw [experiment_reveal_query_bind, runRaw_reveal_query_bind]
          cases hvalue : state.values coordinate with
          | some output =>
              exact ih output state fuel
                (by simpa [IsProbe] using hbound.2 output)
          | none =>
              simp only [bind_assoc]
              apply bind_congr
              intro output
              by_cases hhit : state.hitAt coordinate output
              · simp [hhit, RawResult.finish]
              · simp only [hhit, ↓reduceIte]
                exact ih output (state.install coordinate output) fuel
                  (by simpa [IsProbe] using hbound.2 output)

theorem detailedExperiment_hit_eq_experiment (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) alpha)
    (hbound : computation.IsQueryBoundP IsProbe fuel) :
    DetailedResult.hit <$> detailedExperiment state fuel computation =
      experiment state fuel computation := by
  rw [detailedExperiment, map_bind, experiment_eq_runRaw_finish state fuel computation hbound]
  apply bind_congr
  intro result
  exact result.finishDetailed_hit

set_option maxRecDepth 100000 in
theorem experiment_probability_le (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) alpha) :
    Pr[fun hit : Bool => hit = true | experiment state fuel computation] ≤
      ((fuel + state.pending.card : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      refine (finalize_probability_le state).trans ?_
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.le_add_left state.pending.card fuel) zero_le
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [experiment_uniform_query_bind]
          exact probEvent_bind_le_of_forall_le fun output _ => ih output state fuel
      | hashOutput =>
          rw [experiment_hashOutput_query_bind]
          exact probEvent_bind_le_of_forall_le fun output _ => ih output state fuel
      | ensure coordinate =>
          rw [experiment_ensure_query_bind]
          simpa only [State.pending_card_ensure] using
            ih () (state.ensure coordinate) fuel
      | probe coordinate candidate =>
          rw [experiment_probe_query_bind]
          cases fuel with
          | zero =>
              simpa using finalize_probability_le state
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte]
                refine (ih () state remaining).trans ?_
                have hnat : remaining + state.pending.card ≤
                    remaining + 1 + state.pending.card := by omega
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) zero_le
              · simp only [hrevealed, ↓reduceIte]
                refine (ih () (state.addPending coordinate candidate) remaining).trans ?_
                have hnat : remaining +
                    (state.addPending coordinate candidate).pending.card ≤
                  remaining + 1 + state.pending.card := by
                    have := state.pending_card_addPending_le coordinate candidate
                    omega
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) zero_le
      | peek coordinate =>
          rw [experiment_peek_query_bind]
          exact ih (state.values coordinate) state fuel
      | reveal coordinate =>
          rw [experiment_reveal_query_bind]
          cases hvalue : state.values coordinate with
          | some output => exact ih output state fuel
          | none =>
              refine (probEvent_bind_le_probEvent_add
                (mx := sampleHashOutput)
                (my := fun output =>
                  if state.hitAt coordinate output then pure true
                  else experiment (state.install coordinate output) fuel (next output))
                (q := fun hit : Bool => hit = true)
                (p := state.hitAt coordinate)
                (ε := ((fuel + (state.pendingAway coordinate).card : Nat) : ℝ≥0∞) *
                  ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
              · intro output _ hmiss
                simp only [hmiss, ↓reduceIte]
                simpa only [State.pending_card_install] using
                  ih output (state.install coordinate output) fuel
              · refine add_le_add
                  (probEvent_sampleHashOutput_hitAt_le state coordinate) le_rfl |>.trans ?_
                calc
                  ((state.pendingAt coordinate).card : ℝ≥0∞) *
                        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
                      ((fuel + (state.pendingAway coordinate).card : Nat) : ℝ≥0∞) *
                        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ =
                    (((state.pendingAt coordinate).card + fuel +
                        (state.pendingAway coordinate).card : Nat) : ℝ≥0∞) *
                      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
                        push_cast
                        ring
                  _ ≤ ((fuel + state.pending.card : Nat) : ℝ≥0∞) *
                        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
                      have hsplit :=
                        state.pendingAway_card_add_pendingAt_card_le coordinate
                      have hnat : (state.pendingAt coordinate).card + fuel +
                          (state.pendingAway coordinate).card ≤
                          fuel + state.pending.card := by omega
                      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) zero_le

theorem experiment_empty_probability_le (fuel : Nat)
    (computation : OracleComp (World Coordinate) alpha) :
    Pr[fun hit : Bool => hit = true |
        experiment (State.empty : State Coordinate) fuel computation] ≤
      (fuel : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  simpa [State.empty] using
    experiment_probability_le (State.empty : State Coordinate) fuel computation

end SphincsSecurity.LazyRevealProbe
