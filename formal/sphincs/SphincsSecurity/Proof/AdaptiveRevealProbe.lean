import SphincsSecurity.Proof.SecretProbe
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Adaptive probes with selective reveals

A strategy may reveal table cells and use their values in later probes. A probe against a cell that
has already been revealed is harmless. Every probe against a still-hidden cell adds one candidate,
and revealing that cell or ending the computation tests all accumulated candidates at once. The
total hit probability is therefore at most the number of probes divided by the table range size.
-/

namespace SphincsSecurity.AdaptiveRevealProbe

open OracleComp OracleSpec ENNReal

variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

structure State (Coordinate : Type) where
  pending : Coordinate → Finset Digest
  revealed : Coordinate → Option Digest

def State.pendingCount (state : State Coordinate) : Nat :=
  ∑ coordinate, (state.pending coordinate).card

def State.addPending (state : State Coordinate) (coordinate : Coordinate)
    (candidate : Digest) : State Coordinate :=
  { state with pending := Function.update state.pending coordinate (insert candidate (state.pending coordinate)) }

def State.install (state : State Coordinate) (coordinate : Coordinate)
    (value : Digest) : State Coordinate :=
  { pending := Function.update state.pending coordinate ∅
    revealed := Function.update state.revealed coordinate (some value) }

def State.empty : State Coordinate :=
  { pending := fun _ => ∅
    revealed := fun _ => none }

theorem State.pendingCount_addPending_le (state : State Coordinate)
    (coordinate : Coordinate) (candidate : Digest) :
    (state.addPending coordinate candidate).pendingCount ≤ state.pendingCount + 1 := by
  classical
  unfold pendingCount addPending
  change (∑ other,
      (Function.update state.pending coordinate
        (insert candidate (state.pending coordinate)) other).card) ≤ _
  have hupdate :
      (fun other =>
        (Function.update state.pending coordinate
          (insert candidate (state.pending coordinate)) other).card) =
        Function.update (fun other => (state.pending other).card) coordinate
          (insert candidate (state.pending coordinate)).card := by
    funext other
    by_cases heq : other = coordinate <;> simp [heq]
  rw [hupdate, Finset.sum_update_of_mem (Finset.mem_univ coordinate)]
  have hsum := Finset.sum_erase_add Finset.univ
    (fun other => (state.pending other).card) (Finset.mem_univ coordinate)
  calc
    (insert candidate (state.pending coordinate)).card +
        ∑ other ∈ Finset.univ \ {coordinate}, (state.pending other).card ≤
      ((state.pending coordinate).card + 1) +
        ∑ other ∈ Finset.univ \ {coordinate}, (state.pending other).card := by
      gcongr
      exact Finset.card_insert_le candidate (state.pending coordinate)
    _ = (∑ other ∈ Finset.univ \ {coordinate}, (state.pending other).card) +
        (state.pending coordinate).card + 1 := by omega
    _ = (∑ other, (state.pending other).card) + 1 := by
      rw [Finset.sdiff_singleton_eq_erase, hsum]

theorem State.pendingCount_install_add (state : State Coordinate)
    (coordinate : Coordinate) (value : Digest) :
    (state.install coordinate value).pendingCount +
        (state.pending coordinate).card = state.pendingCount := by
  classical
  unfold pendingCount install
  change (∑ other,
      (Function.update state.pending coordinate ∅ other).card) +
        (state.pending coordinate).card = _
  have hupdate :
      (fun other => (Function.update state.pending coordinate ∅ other).card) =
        Function.update (fun other => (state.pending other).card) coordinate 0 := by
    funext other
    by_cases heq : other = coordinate <;> simp [heq]
  rw [hupdate, Finset.sum_update_of_mem (Finset.mem_univ coordinate), zero_add,
    Finset.sdiff_singleton_eq_erase]
  exact Finset.sum_erase_add Finset.univ
    (fun other => (state.pending other).card) (Finset.mem_univ coordinate)

omit [DecidableEq Coordinate] in
@[simp] theorem State.pendingCount_empty :
    (State.empty : State Coordinate).pendingCount = 0 := by
  simp [State.empty, State.pendingCount]

def State.Valid (state : State Coordinate) : Prop :=
  ∀ coordinate value, state.revealed coordinate = some value →
    state.pending coordinate = ∅

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem State.valid_empty : (State.empty : State Coordinate).Valid := by
  intro coordinate value hvalue
  simp [State.empty] at hvalue

omit [Fintype Coordinate] in
theorem State.Valid.addPending {state : State Coordinate} (hvalid : state.Valid)
    (coordinate : Coordinate) (candidate : Digest)
    (hhidden : state.revealed coordinate = none) :
    (state.addPending coordinate candidate).Valid := by
  intro other value hvalue
  by_cases heq : other = coordinate
  · subst other
    simp [State.addPending, hhidden] at hvalue
  · simpa [State.addPending, Function.update_of_ne heq] using
      hvalid other value hvalue

omit [Fintype Coordinate] in
theorem State.Valid.install {state : State Coordinate} (hvalid : state.Valid)
    (coordinate : Coordinate) (value : Digest) :
    (state.install coordinate value).Valid := by
  intro other otherValue hvalue
  by_cases heq : other = coordinate
  · subst other
    simp [State.install]
  · have hvalue' : state.revealed other = some otherValue := by
      simpa [State.install, Function.update_of_ne heq] using hvalue
    simpa [State.install, Function.update_of_ne heq] using
      hvalid other otherValue hvalue'

def extendTable (state : State Coordinate) (base : Coordinate → Digest) :
    Coordinate → Digest :=
  fun coordinate => (state.revealed coordinate).getD (base coordinate)

omit [Fintype Coordinate] in
theorem extendTable_update_eq_install (state : State Coordinate)
    (coordinate : Coordinate) (value : Digest) (base : Coordinate → Digest)
    (hhidden : state.revealed coordinate = none) :
    extendTable state (Function.update base coordinate value) =
      extendTable (state.install coordinate value) base := by
  funext other
  by_cases heq : other = coordinate
  · subst other
    simp [extendTable, State.install, hhidden]
  · simp [extendTable, State.install, Function.update_of_ne heq]

def tableHits (state : State Coordinate) (table : Coordinate → Digest) : Bool :=
  decide (∃ coordinate, table coordinate ∈ state.pending coordinate)

theorem tableHits_addPending_eq_false (state : State Coordinate)
    (table : Coordinate → Digest) (coordinate : Coordinate) (candidate : Digest)
    (hclean : tableHits state table = false)
    (hmiss : table coordinate ≠ candidate) :
    tableHits (state.addPending coordinate candidate) table = false := by
  classical
  unfold tableHits at hclean ⊢
  simp only [decide_eq_false_iff_not] at hclean ⊢
  rintro ⟨other, hmem⟩
  by_cases heq : other = coordinate
  · subst other
    simp only [State.addPending, Function.update_self, Finset.mem_insert] at hmem
    exact hmem.elim hmiss (fun hold => hclean ⟨coordinate, hold⟩)
  · simp only [State.addPending, Function.update_of_ne heq] at hmem
    exact hclean ⟨other, hmem⟩

theorem tableHits_addPending_eq_true (state : State Coordinate)
    (table : Coordinate → Digest) (coordinate : Coordinate) (candidate : Digest)
    (hhit : table coordinate = candidate) :
    tableHits (state.addPending coordinate candidate) table = true := by
  classical
  rw [tableHits, decide_eq_true_eq]
  exact ⟨coordinate, by simp [State.addPending, hhit]⟩

omit [DecidableEq Coordinate] in
theorem tableHits_extendTable_eq_true_iff (state : State Coordinate)
    (hvalid : state.Valid) (base : Coordinate → Digest) :
    tableHits state (extendTable state base) = true ↔
      ∃ coordinate ∈ (Finset.univ : Finset Coordinate),
        ∃ candidate ∈ state.pending coordinate, base coordinate = candidate := by
  simp only [tableHits, decide_eq_true_eq, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨coordinate, hmem⟩
    have hhidden : state.revealed coordinate = none := by
      cases hvalue : state.revealed coordinate with
      | none => rfl
      | some value =>
          have hempty := hvalid coordinate value hvalue
          rw [hempty] at hmem
          simp at hmem
    exact ⟨coordinate, extendTable state base coordinate, hmem, by
      simp [extendTable, hhidden]⟩
  · rintro ⟨coordinate, candidate, hcandidate, heq⟩
    have hhidden : state.revealed coordinate = none := by
      cases hvalue : state.revealed coordinate with
      | none => rfl
      | some value =>
          have hempty := hvalid coordinate value hvalue
          rw [hempty] at hcandidate
          simp at hcandidate
    exact ⟨coordinate, by simpa [extendTable, hhidden, heq] using hcandidate⟩

noncomputable local instance sampleableDigest : SampleableType Digest :=
  SampleableType.ofFintype Digest

noncomputable local instance sampleableTable : SampleableType (Coordinate → Digest) :=
  SampleableType.ofFintype (Coordinate → Digest)

noncomputable def sampleTable : ProbComp (Coordinate → Digest) :=
  $ᵗ (Coordinate → Digest)

theorem uniformDigest_mem_finset_le (candidates : Finset Digest) :
    Pr[fun value : Digest => value ∈ candidates | ($ᵗ Digest : ProbComp Digest)] ≤
      (candidates.card : ℝ≥0∞) *
        ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    Pr[fun value : Digest => value ∈ candidates | ($ᵗ Digest : ProbComp Digest)] =
        Pr[fun value : Digest => ∃ candidate ∈ candidates, value = candidate |
          ($ᵗ Digest : ProbComp Digest)] := by
      apply probEvent_congr' (fun value _ => by simp) rfl
    _ ≤ ∑ candidate ∈ candidates,
        Pr[fun value : Digest => value = candidate | ($ᵗ Digest : ProbComp Digest)] :=
      probEvent_exists_finset_le_sum candidates ($ᵗ Digest)
        (fun candidate value => value = candidate)
    _ = ∑ _candidate ∈ candidates,
        ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_congr rfl
      intro candidate _
      simp only [probEvent_eq_eq_probOutput, probOutput_uniformSample]
    _ = (candidates.card : ℝ≥0∞) *
        ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]

theorem finalize_probability_le [Nonempty Coordinate]
    (state : State Coordinate) (hvalid : state.Valid) :
    Pr[fun hit : Bool => hit = true |
        (fun base : Coordinate → Digest => tableHits state (extendTable state base)) <$>
          sampleTable] ≤
      (state.pendingCount : ℝ≥0∞) *
        ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹ := by
  rw [probEvent_map]
  change Pr[fun base : Coordinate → Digest =>
      tableHits state (extendTable state base) = true | sampleTable] ≤ _
  have hevent :
      (fun base : Coordinate → Digest =>
        tableHits state (extendTable state base) = true) =
      (fun base : Coordinate → Digest =>
        ∃ coordinate ∈ (Finset.univ : Finset Coordinate),
          ∃ candidate ∈ state.pending coordinate, base coordinate = candidate) := by
    funext base
    exact propext (tableHits_extendTable_eq_true_iff state hvalid base)
  rw [hevent]
  calc
    Pr[fun base : Coordinate → Digest =>
          ∃ coordinate ∈ (Finset.univ : Finset Coordinate),
            ∃ candidate ∈ state.pending coordinate, base coordinate = candidate |
        sampleTable] ≤
      ∑ coordinate ∈ (Finset.univ : Finset Coordinate),
        Pr[fun base : Coordinate → Digest =>
            ∃ candidate ∈ state.pending coordinate, base coordinate = candidate |
          sampleTable] :=
        probEvent_exists_finset_le_sum Finset.univ sampleTable
          (fun coordinate base =>
            ∃ candidate ∈ state.pending coordinate, base coordinate = candidate)
    _ ≤ ∑ coordinate ∈ (Finset.univ : Finset Coordinate),
        ((state.pending coordinate).card : ℝ≥0∞) *
          ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro coordinate _
      calc
        Pr[fun base : Coordinate → Digest =>
              ∃ candidate ∈ state.pending coordinate, base coordinate = candidate |
            sampleTable] ≤
          ∑ candidate ∈ state.pending coordinate,
            Pr[fun base : Coordinate → Digest => base coordinate = candidate |
              sampleTable] :=
            probEvent_exists_finset_le_sum (state.pending coordinate) sampleTable
              (fun candidate base => base coordinate = candidate)
        _ = ∑ _candidate ∈ state.pending coordinate,
            ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹ := by
          apply Finset.sum_congr rfl
          intro candidate _
          exact SphincsSecurity.uniform_function_coordinate_probability coordinate candidate
        _ = ((state.pending coordinate).card : ℝ≥0∞) *
            ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (state.pendingCount : ℝ≥0∞) *
        ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹ := by
      rw [← Finset.sum_mul]
      congr 1
      simp [State.pendingCount]

theorem evalDist_sampleTable_eq_bind_update (coordinate : Coordinate)
    (continuation : (Coordinate → Digest) → ProbComp alpha) :
    𝒟[sampleTable >>= continuation] =
      𝒟[do
        let value ← ($ᵗ Digest : ProbComp Digest)
        let base ← sampleTable
        continuation (Function.update base coordinate value)] := by
  unfold sampleTable
  calc
    𝒟[($ᵗ (Coordinate → Digest) : ProbComp (Coordinate → Digest)) >>= continuation] =
        𝒟[(do
          let value ← ($ᵗ Digest : ProbComp Digest)
          let base ← ($ᵗ (Coordinate → Digest) : ProbComp (Coordinate → Digest))
          pure (Function.update base coordinate value)) >>= continuation] := by
      rw [evalDist_bind, evalDist_bind, evalDist_uniformSample_bind_update coordinate]
    _ = _ := by simp [bind_assoc]

inductive Query (Coordinate : Type) where
  | uniform (n : Nat)
  | hashOutput
  | probe (coordinate : Coordinate) (candidate : Digest)
  | reveal (coordinate : Coordinate)

@[reducible] def World (Coordinate : Type) : OracleSpec (Query Coordinate) :=
  OracleSpec.ofFn fun
  | .uniform n => Fin (n + 1)
  | .hashOutput => HashOutput
  | .probe _ _ => Unit
  | .reveal _ => Digest

def IsProbe : (World Coordinate).Domain → Prop
  | .uniform _ => False
  | .hashOutput => False
  | .probe _ _ => True
  | .reveal _ => False

noncomputable instance : DecidablePred (IsProbe (Coordinate := Coordinate)) :=
  fun input => match input with
  | .uniform _ => isFalse (by simp [IsProbe])
  | .hashOutput => isFalse (by simp [IsProbe])
  | .probe _ _ => isTrue (by simp [IsProbe])
  | .reveal _ => isFalse (by simp [IsProbe])

def uniformQuery (n : Nat) : OracleComp (World Coordinate) (Fin (n + 1)) :=
  liftM ((World Coordinate).query (.uniform n))

def hashOutputQuery : OracleComp (World Coordinate) HashOutput :=
  liftM ((World Coordinate).query .hashOutput)

noncomputable def sampleHashOutput : ProbComp HashOutput :=
  uniformSampleImpl (spec := HashSpec) ([] : HashInput)

def probeQuery (coordinate : Coordinate) (candidate : Digest) :
    OracleComp (World Coordinate) Unit :=
  liftM ((World Coordinate).query (.probe coordinate candidate))

def revealQuery (coordinate : Coordinate) : OracleComp (World Coordinate) Digest :=
  liftM ((World Coordinate).query (.reveal coordinate))

def uniformForwardImpl : QueryImpl unifSpec (OracleComp (World Coordinate)) :=
  fun n => uniformQuery n

def liftProbComp (computation : ProbComp alpha) : OracleComp (World Coordinate) alpha :=
  simulateQ uniformForwardImpl computation

omit [Fintype Coordinate] [DecidableEq Coordinate] in
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

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem probeQuery_isProbeBound (coordinate : Coordinate) (candidate : Digest) :
    (probeQuery coordinate candidate).IsQueryBoundP IsProbe 1 := by
  rw [probeQuery, OracleComp.isQueryBoundP_query_iff]
  simp [IsProbe]

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem revealQuery_isProbeBound (coordinate : Coordinate) (fuel : Nat) :
    (revealQuery coordinate).IsQueryBoundP IsProbe fuel := by
  rw [revealQuery, OracleComp.isQueryBoundP_query_iff]
  simp [IsProbe]

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem hashOutputQuery_isProbeBound (fuel : Nat) :
    (hashOutputQuery (Coordinate := Coordinate)).IsQueryBoundP IsProbe fuel := by
  rw [hashOutputQuery, OracleComp.isQueryBoundP_query_iff]
  simp [IsProbe]

noncomputable def run (table : Coordinate → Digest) (state : State Coordinate)
    (fuel : Nat) (computation : OracleComp (World Coordinate) alpha) : ProbComp Bool :=
  OracleComp.construct
    (C := fun _ => State Coordinate → Nat → ProbComp Bool)
    (fun _ state _ => pure (tableHits state table))
    (fun input _next recursivelyRun state fuel =>
      match input with
      | .uniform n => do
          let output ← liftM (unifSpec.query n)
          recursivelyRun output state fuel
      | .hashOutput => do
          let output ← liftM sampleHashOutput
          recursivelyRun output state fuel
      | .probe coordinate candidate =>
          match fuel with
          | 0 => pure (tableHits state table)
          | remaining + 1 =>
              match state.revealed coordinate with
              | some _ => recursivelyRun () state remaining
              | none => recursivelyRun () (state.addPending coordinate candidate) remaining
      | .reveal coordinate =>
          match state.revealed coordinate with
          | some value => recursivelyRun value state fuel
          | none =>
              let value := table coordinate
              if value ∈ state.pending coordinate then pure true
              else recursivelyRun value (state.install coordinate value) fuel)
    computation state fuel

inductive DetailedResult (alpha : Type) where
  | stopped (hit : Bool)
  | done (hit : Bool) (value : alpha)

def DetailedResult.hit : DetailedResult alpha → Bool
  | .stopped hit => hit
  | .done hit _ => hit

def DetailedResult.value? : DetailedResult alpha → Option alpha
  | .stopped _ => none
  | .done _ value => some value

noncomputable def runDetailed (table : Coordinate → Digest) (state : State Coordinate)
    (fuel : Nat) (computation : OracleComp (World Coordinate) alpha) :
    ProbComp (DetailedResult alpha) :=
  OracleComp.construct
    (C := fun _ : OracleComp (World Coordinate) alpha =>
      State Coordinate → Nat → ProbComp (DetailedResult alpha))
    (fun result state _ => pure (.done (tableHits state table) result))
    (fun input _next recursivelyRun state fuel =>
      match input with
      | .uniform n => do
          let output ← liftM (unifSpec.query n)
          recursivelyRun output state fuel
      | .hashOutput => do
          let output ← liftM sampleHashOutput
          recursivelyRun output state fuel
      | .probe coordinate candidate =>
          match fuel with
          | 0 => pure (.stopped (tableHits state table))
          | remaining + 1 =>
              match state.revealed coordinate with
              | some _ => recursivelyRun () state remaining
              | none => recursivelyRun () (state.addPending coordinate candidate) remaining
      | .reveal coordinate =>
          match state.revealed coordinate with
          | some value => recursivelyRun value state fuel
          | none =>
              let value := table coordinate
              if value ∈ state.pending coordinate then pure (.stopped true)
              else recursivelyRun value (state.install coordinate value) fuel)
    computation state fuel

theorem runDetailed_uniform_query_bind (table : Coordinate → Digest)
    (state : State Coordinate) (fuel n : Nat)
    (next : Fin (n + 1) → OracleComp (World Coordinate) alpha) :
    runDetailed table state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.uniform n)) :
          OracleComp (World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      runDetailed table state fuel (next output)) := by
  rw [runDetailed, OracleComp.construct_query_bind]
  rfl

theorem runDetailed_hashOutput_query_bind (table : Coordinate → Digest)
    (state : State Coordinate) (fuel : Nat)
    (next : HashOutput → OracleComp (World Coordinate) alpha) :
    runDetailed table state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) .hashOutput) :
          OracleComp (World Coordinate) HashOutput) >>= next) = (do
      let output ← liftM sampleHashOutput
      runDetailed table state fuel (next output)) := by
  rw [runDetailed, OracleComp.construct_query_bind]
  rfl

theorem runDetailed_probe_query_bind (table : Coordinate → Digest)
    (state : State Coordinate) (fuel : Nat) (coordinate : Coordinate)
    (candidate : Digest) (next : Unit → OracleComp (World Coordinate) alpha) :
    runDetailed table state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.probe coordinate candidate)) :
          OracleComp (World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure (.stopped (tableHits state table))
      | remaining + 1 =>
          match state.revealed coordinate with
          | some _ => runDetailed table state remaining (next ())
          | none => runDetailed table (state.addPending coordinate candidate) remaining (next ()) := by
  rw [runDetailed, OracleComp.construct_query_bind]
  rfl

theorem runDetailed_reveal_query_bind (table : Coordinate → Digest)
    (state : State Coordinate) (fuel : Nat) (coordinate : Coordinate)
    (next : Digest → OracleComp (World Coordinate) alpha) :
    runDetailed table state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.reveal coordinate)) :
          OracleComp (World Coordinate) Digest) >>= next) =
      match state.revealed coordinate with
      | some value => runDetailed table state fuel (next value)
      | none =>
          let value := table coordinate
          if value ∈ state.pending coordinate then pure (.stopped true)
          else runDetailed table (state.install coordinate value) fuel (next value) := by
  rw [runDetailed, OracleComp.construct_query_bind]
  rfl

theorem run_uniform_query_bind (table : Coordinate → Digest) (state : State Coordinate)
    (fuel n : Nat)
    (next : Fin (n + 1) → OracleComp (World Coordinate) alpha) :
    run table state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.uniform n)) :
          OracleComp (World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      run table state fuel (next output)) := by
  rw [run, OracleComp.construct_query_bind]
  rfl

theorem run_probe_query_bind (table : Coordinate → Digest) (state : State Coordinate)
    (fuel : Nat) (coordinate : Coordinate) (candidate : Digest)
    (next : Unit → OracleComp (World Coordinate) alpha) :
    run table state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.probe coordinate candidate)) :
          OracleComp (World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure (tableHits state table)
      | remaining + 1 =>
          match state.revealed coordinate with
          | some _ => run table state remaining (next ())
          | none => run table (state.addPending coordinate candidate) remaining (next ()) := by
  rw [run, OracleComp.construct_query_bind]
  rfl

theorem run_hashOutput_query_bind (table : Coordinate → Digest) (state : State Coordinate)
    (fuel : Nat) (next : HashOutput → OracleComp (World Coordinate) alpha) :
    run table state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) .hashOutput) :
          OracleComp (World Coordinate) HashOutput) >>= next) = (do
      let output ← liftM sampleHashOutput
      run table state fuel (next output)) := by
  rw [run, OracleComp.construct_query_bind]
  rfl

theorem run_reveal_query_bind (table : Coordinate → Digest) (state : State Coordinate)
    (fuel : Nat) (coordinate : Coordinate)
    (next : Digest → OracleComp (World Coordinate) alpha) :
    run table state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.reveal coordinate)) :
          OracleComp (World Coordinate) Digest) >>= next) =
      match state.revealed coordinate with
      | some value => run table state fuel (next value)
      | none =>
          let value := table coordinate
          if value ∈ state.pending coordinate then pure true
          else run table (state.install coordinate value) fuel (next value) := by
  rw [run, OracleComp.construct_query_bind]
  rfl

theorem runDetailed_hit_eq_run (table : Coordinate → Digest)
    (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) alpha) :
    DetailedResult.hit <$> runDetailed table state fuel computation =
      run table state fuel computation := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure result =>
      simp [runDetailed, run, DetailedResult.hit]
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDetailed_uniform_query_bind, run_uniform_query_bind,
            map_bind]
          apply bind_congr
          intro output
          exact ih output _ _
      | hashOutput =>
          rw [runDetailed_hashOutput_query_bind, run_hashOutput_query_bind,
            map_bind]
          apply bind_congr
          intro output
          exact ih output _ _
      | probe coordinate candidate =>
          rw [runDetailed_probe_query_bind, run_probe_query_bind]
          cases fuel with
          | zero => simp [DetailedResult.hit]
          | succ remaining =>
              cases hrevealed : state.revealed coordinate with
              | none => exact ih () (state.addPending coordinate candidate) remaining
              | some value => exact ih () state remaining
      | reveal coordinate =>
          rw [runDetailed_reveal_query_bind, run_reveal_query_bind]
          cases hrevealed : state.revealed coordinate with
          | some value => exact ih value state fuel
          | none =>
              by_cases hhit : table coordinate ∈ state.pending coordinate
              · simp [hhit, DetailedResult.hit]
              · simp only [hhit, ↓reduceIte]
                exact ih (table coordinate) (state.install coordinate (table coordinate)) fuel

theorem stopped_false_not_mem_support_runDetailed
    (table : Coordinate → Digest) (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) alpha)
    (hbound : computation.IsQueryBoundP IsProbe fuel) :
    DetailedResult.stopped false ∉ support (runDetailed table state fuel computation) := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure result =>
      simp [runDetailed]
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | uniform n =>
          rw [runDetailed_uniform_query_bind, mem_support_bind_iff]
          rintro ⟨output, houtput, hrest⟩
          exact ih output state fuel (hbound.2 output) hrest
      | hashOutput =>
          rw [runDetailed_hashOutput_query_bind, mem_support_bind_iff]
          rintro ⟨output, houtput, hrest⟩
          exact ih output state fuel (hbound.2 output) hrest
      | probe coordinate candidate =>
          have hpositive : 0 < fuel := by
            simpa [IsProbe] using hbound.1
          cases fuel with
          | zero => omega
          | succ remaining =>
              rw [runDetailed_probe_query_bind]
              cases hrevealed : state.revealed coordinate with
              | none =>
                  exact ih () (state.addPending coordinate candidate) remaining
                    (by simpa [IsProbe] using hbound.2 ())
              | some value =>
                  exact ih () state remaining (by simpa [IsProbe] using hbound.2 ())
      | reveal coordinate =>
          rw [runDetailed_reveal_query_bind]
          cases hrevealed : state.revealed coordinate with
          | some value =>
              exact ih value state fuel (by simpa [IsProbe] using hbound.2 value)
          | none =>
              by_cases hhit : table coordinate ∈ state.pending coordinate
              · simp [hhit]
              · simp only [hhit, ↓reduceIte]
                exact ih (table coordinate) (state.install coordinate (table coordinate)) fuel
                  (by simpa [IsProbe] using hbound.2 (table coordinate))

noncomputable def experiment (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) alpha) : ProbComp Bool := do
  let base ← sampleTable
  run (extendTable state base) state fuel computation

noncomputable def detailedExperiment (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) alpha) :
    ProbComp ((Coordinate → Digest) × DetailedResult alpha) := do
  let base ← sampleTable
  let table := extendTable state base
  let result ← runDetailed table state fuel computation
  pure (table, result)

theorem detailedExperiment_hit_eq_experiment (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) alpha) :
    (fun result => result.2.hit) <$> detailedExperiment state fuel computation =
      experiment state fuel computation := by
  unfold detailedExperiment experiment
  simp only [map_bind]
  apply bind_congr
  intro base
  rw [← runDetailed_hit_eq_run]
  simp [map_eq_bind_pure_comp]

noncomputable def applyReveal (state : State Coordinate) (coordinate : Coordinate)
    (resume : Digest → State Coordinate → ProbComp Bool) : ProbComp Bool := do
  let value ← ($ᵗ Digest : ProbComp Digest)
  if value ∈ state.pending coordinate then pure true
  else resume value (state.install coordinate value)

theorem applyReveal_probability_le (state : State Coordinate) (coordinate : Coordinate)
    (resume : Digest → State Coordinate → ProbComp Bool) (fuel : Nat)
    (hresume : ∀ value,
      Pr[fun hit : Bool => hit = true | resume value (state.install coordinate value)] ≤
        ((fuel + (state.install coordinate value).pendingCount : Nat) : ℝ≥0∞) *
          ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹) :
    Pr[fun hit : Bool => hit = true | applyReveal state coordinate resume] ≤
      ((fuel + state.pendingCount : Nat) : ℝ≥0∞) *
        ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹ := by
  let installedCount := (state.install coordinate 0).pendingCount
  refine (probEvent_bind_le_probEvent_add
    (mx := ($ᵗ Digest : ProbComp Digest))
    (my := fun value =>
      if value ∈ state.pending coordinate then pure true
      else resume value (state.install coordinate value))
    (q := fun hit : Bool => hit = true)
    (p := fun value : Digest => value ∈ state.pending coordinate)
    (ε := ((fuel + installedCount : Nat) : ℝ≥0∞) *
      ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
  · intro value _ hmiss
    simp only [hmiss, ↓reduceIte]
    have hcount : (state.install coordinate value).pendingCount = installedCount := rfl
    simpa [hcount] using hresume value
  · refine add_le_add (uniformDigest_mem_finset_le (state.pending coordinate)) le_rfl |>.trans ?_
    have hconserve := state.pendingCount_install_add coordinate 0
    calc
      ((state.pending coordinate).card : ℝ≥0∞) *
            ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹ +
          ((fuel + installedCount : Nat) : ℝ≥0∞) *
            ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹ =
        (((state.pending coordinate).card + fuel + installedCount : Nat) : ℝ≥0∞) *
          ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹ := by
        push_cast
        ring
      _ = ((fuel + state.pendingCount : Nat) : ℝ≥0∞) *
          ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹ := by
        rw [show (state.pending coordinate).card + fuel + installedCount =
          fuel + state.pendingCount by omega]
      _ ≤ ((fuel + state.pendingCount : Nat) : ℝ≥0∞) *
          ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹ := le_rfl

theorem evalDist_sample_applyReveal (state : State Coordinate) (coordinate : Coordinate)
    (hhidden : state.revealed coordinate = none)
    (resume : (Coordinate → Digest) → Digest → State Coordinate → ProbComp Bool) :
    evalDist (sampleTable >>= fun base =>
      let table := extendTable state base
      let value := table coordinate
      if value ∈ state.pending coordinate then pure true
      else resume table value (state.install coordinate value)) =
    evalDist (applyReveal state coordinate (fun value nextState =>
      sampleTable >>= fun base =>
        resume (extendTable nextState base) value nextState)) := by
  let continuation := fun (base : Coordinate → Digest) =>
    let table := extendTable state base
    let value := table coordinate
    if value ∈ state.pending coordinate then pure true
    else resume table value (state.install coordinate value)
  calc
    _ = evalDist (do
          let value ← ($ᵗ Digest : ProbComp Digest)
          let base ← sampleTable
          if value ∈ state.pending coordinate then pure true
          else (resume (extendTable (state.install coordinate value) base)
            value (state.install coordinate value))) := by
      rw [evalDist_sampleTable_eq_bind_update coordinate continuation]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro value
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      simp only [continuation]
      rw [extendTable_update_eq_install state coordinate value base hhidden]
      have hinstalled :
          extendTable (state.install coordinate value) base coordinate = value := by
        simp [extendTable, State.install]
      rw [hinstalled]
    _ = _ := by
      unfold applyReveal
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro value
      by_cases hhit : value ∈ state.pending coordinate
      · simp only [hhit, ↓reduceIte]
        exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails sampleTable
          (by simp [sampleTable]) (pure true)
      · simp [hhit]

theorem experiment_uniform_query_bind (state : State Coordinate) (fuel n : Nat)
    (next : Fin (n + 1) → OracleComp (World Coordinate) alpha) :
    experiment state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.uniform n)) :
          OracleComp (World Coordinate) (Fin (n + 1))) >>= next) =
      sampleTable >>= fun base => (do
        let output ← liftM (unifSpec.query n)
        run (extendTable state base) state fuel (next output)) := by
  unfold experiment
  apply bind_congr
  intro base
  exact run_uniform_query_bind _ _ _ _ _

theorem experiment_probe_query_bind (state : State Coordinate) (fuel : Nat)
    (coordinate : Coordinate) (candidate : Digest)
    (next : Unit → OracleComp (World Coordinate) alpha) :
    experiment state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.probe coordinate candidate)) :
          OracleComp (World Coordinate) Unit) >>= next) =
      sampleTable >>= fun base =>
        match fuel with
        | 0 => pure (tableHits state (extendTable state base))
        | remaining + 1 =>
            match state.revealed coordinate with
            | some _ => run (extendTable state base) state remaining (next ())
            | none => run (extendTable state base)
                (state.addPending coordinate candidate) remaining (next ()) := by
  cases fuel with
  | zero =>
      unfold experiment
      apply bind_congr
      intro base
      exact run_probe_query_bind (Coordinate := Coordinate) (alpha := alpha)
        (extendTable state base) state 0 coordinate candidate next
  | succ remaining =>
      unfold experiment
      apply bind_congr
      intro base
      exact run_probe_query_bind (Coordinate := Coordinate) (alpha := alpha)
        (extendTable state base) state (remaining + 1) coordinate candidate next

theorem experiment_hashOutput_query_bind (state : State Coordinate) (fuel : Nat)
    (next : HashOutput → OracleComp (World Coordinate) alpha) :
    experiment state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) .hashOutput) :
          OracleComp (World Coordinate) HashOutput) >>= next) =
      sampleTable >>= fun base => (do
        let output ← liftM sampleHashOutput
        run (extendTable state base) state fuel (next output)) := by
  unfold experiment
  apply bind_congr
  intro base
  exact run_hashOutput_query_bind _ _ _ _

theorem experiment_reveal_query_bind (state : State Coordinate) (fuel : Nat)
    (coordinate : Coordinate)
    (next : Digest → OracleComp (World Coordinate) alpha) :
    experiment state fuel
        ((liftM (OracleSpec.query (spec := World Coordinate) (.reveal coordinate)) :
          OracleComp (World Coordinate) Digest) >>= next) =
      sampleTable >>= fun base =>
        match state.revealed coordinate with
        | some value => run (extendTable state base) state fuel (next value)
        | none =>
            let value := extendTable state base coordinate
            if value ∈ state.pending coordinate then pure true
            else run (extendTable state base) (state.install coordinate value)
              fuel (next value) := by
  unfold experiment
  apply bind_congr
  intro base
  exact run_reveal_query_bind _ _ _ _ _

set_option maxRecDepth 100000 in
theorem experiment_probability_le [Nonempty Coordinate]
    (state : State Coordinate) (hvalid : state.Valid)
    (fuel : Nat) (computation : OracleComp (World Coordinate) alpha)
    (hbound : computation.IsQueryBoundP IsProbe fuel) :
    Pr[fun hit : Bool => hit = true | experiment state fuel computation] ≤
      ((fuel + state.pendingCount : Nat) : ℝ≥0∞) *
        ((Fintype.card Digest : Nat) : ℝ≥0∞)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure result =>
      change Pr[fun hit : Bool => hit = true |
        (fun base : Coordinate → Digest => tableHits state (extendTable state base)) <$>
          sampleTable] ≤ _
      refine (finalize_probability_le state hvalid).trans ?_
      apply mul_le_mul_left
      exact_mod_cast Nat.le_add_left state.pendingCount fuel
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | uniform n =>
          have hdist :
              evalDist (experiment state fuel
                ((liftM (OracleSpec.query (spec := World Coordinate) (.uniform n)) :
                  OracleComp (World Coordinate) _) >>= next)) =
              evalDist ((liftM (unifSpec.query n) : ProbComp _) >>= fun output =>
                experiment state fuel (next output)) := by
            rw [experiment_uniform_query_bind]
            exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          refine (probEvent_congr' (oa' :=
            (liftM (unifSpec.query n) : ProbComp _) >>= fun output =>
              experiment state fuel (next output)) (fun _ _ => Iff.rfl) hdist).le.trans ?_
          exact probEvent_bind_le_of_forall_le fun output _ =>
            ih output state hvalid fuel (by simpa [IsProbe] using hbound.2 output)
      | hashOutput =>
          have hdist :
              evalDist (experiment state fuel
                ((liftM (OracleSpec.query (spec := World Coordinate) .hashOutput) :
                  OracleComp (World Coordinate) HashOutput) >>= next)) =
              evalDist (sampleHashOutput >>= fun output =>
                experiment state fuel (next output)) := by
            rw [experiment_hashOutput_query_bind]
            exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          refine (probEvent_congr' (oa' :=
            sampleHashOutput >>= fun output =>
              experiment state fuel (next output)) (fun _ _ => Iff.rfl) hdist).le.trans ?_
          exact probEvent_bind_le_of_forall_le fun output _ =>
            ih output state hvalid fuel (by simpa [IsProbe] using hbound.2 output)
      | probe coordinate candidate =>
          cases fuel with
          | zero => simp [IsProbe] at hbound
          | succ remaining =>
              cases hrevealed : state.revealed coordinate with
              | some value =>
                  rw [experiment_probe_query_bind]
                  simp only [hrevealed]
                  change Pr[fun hit : Bool => hit = true |
                    experiment state remaining (next ())] ≤ _
                  refine (ih () state hvalid remaining
                    (by simpa [IsProbe] using hbound.2 ())).trans ?_
                  apply mul_le_mul_left
                  have hnat : remaining + state.pendingCount ≤
                      remaining + 1 + state.pendingCount := by omega
                  exact_mod_cast hnat
              | none =>
                  rw [experiment_probe_query_bind]
                  simp only [hrevealed]
                  change Pr[fun hit : Bool => hit = true |
                    experiment (state.addPending coordinate candidate) remaining
                      (next ())] ≤ _
                  refine (ih () (state.addPending coordinate candidate)
                    (hvalid.addPending coordinate candidate hrevealed) remaining
                    (by simpa [IsProbe] using hbound.2 ())).trans ?_
                  apply mul_le_mul_left
                  exact_mod_cast (show remaining +
                      (state.addPending coordinate candidate).pendingCount ≤
                    remaining + 1 + state.pendingCount by
                      have := state.pendingCount_addPending_le coordinate candidate
                      omega)
      | reveal coordinate =>
          cases hrevealed : state.revealed coordinate with
          | some value =>
              rw [experiment_reveal_query_bind]
              simp only [hrevealed]
              change Pr[fun hit : Bool => hit = true |
                experiment state fuel (next value)] ≤ _
              exact ih value state hvalid fuel
                (by simpa [IsProbe] using hbound.2 value)
          | none =>
              let resume := fun value nextState => experiment nextState fuel (next value)
              have hdist :
                  evalDist (experiment state fuel
                    ((liftM (OracleSpec.query (spec := World Coordinate) (.reveal coordinate)) :
                      OracleComp (World Coordinate) _) >>= next)) =
                  evalDist (applyReveal state coordinate resume) := by
                rw [experiment_reveal_query_bind]
                simp only [hrevealed]
                simpa [resume, experiment] using
                  evalDist_sample_applyReveal state coordinate hrevealed
                    fun table value nextState =>
                      run table nextState fuel (next value)
              refine (probEvent_congr' (oa' := applyReveal state coordinate resume)
                (fun _ _ => Iff.rfl) hdist).le.trans ?_
              apply applyReveal_probability_le state coordinate resume fuel
              intro value
              exact ih value (state.install coordinate value)
                (hvalid.install coordinate value) fuel
                (by simpa [IsProbe] using hbound.2 value)

theorem experiment_empty_probability_le [Nonempty Coordinate] (fuel : Nat)
    (computation : OracleComp (World Coordinate) alpha)
    (hbound : computation.IsQueryBoundP IsProbe fuel) :
    Pr[fun hit : Bool => hit = true |
        experiment (State.empty : State Coordinate) fuel computation] ≤
      (fuel : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  simpa [show Fintype.card Digest = 2 ^ digestBits by simp] using
    experiment_probability_le (State.empty : State Coordinate) State.valid_empty
      fuel computation hbound

end SphincsSecurity.AdaptiveRevealProbe
