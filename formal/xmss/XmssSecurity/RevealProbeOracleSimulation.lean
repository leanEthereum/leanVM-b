import XmssSecurity.AdaptiveRevealMonitor
import XmssSecurity.IndexedHiddenValue

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.RevealProbeOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

inductive Query (Index : Type) where
  | uniform (n : Nat)
  | probe (index : Index) (target : Digest)
  | reveal (index : Index)

@[reducible]
def World (Index : Type) : OracleSpec (Query Index) :=
  OracleSpec.ofFn fun
  | .uniform n => Fin (n + 1)
  | .probe _ _ => Unit
  | .reveal _ => Digest

def probeQuery (index : Index) (target : Digest) :
    OracleComp (World Index) Unit :=
  liftM ((World Index).query (.probe index target))

def revealQuery (index : Index) : OracleComp (World Index) Digest :=
  liftM ((World Index).query (.reveal index))

def uniformQuery (n : Nat) : OracleComp (World Index) (Fin (n + 1)) :=
  liftM ((World Index).query (.uniform n))

def uniformForwardImpl : QueryImpl unifSpec (OracleComp (World Index)) :=
  fun n => uniformQuery n

def liftProbComp (computation : ProbComp α) :
    OracleComp (World Index) α :=
  simulateQ uniformForwardImpl computation

noncomputable def controller
    (computation : OracleComp (World Index) α) :
    ProbComp
      (AdaptiveRevealMonitor.ControllerAction
        (OracleComp (World Index) α) Index) :=
  OracleComp.construct
    (C := fun _ => ProbComp
      (AdaptiveRevealMonitor.ControllerAction
        (OracleComp (World Index) α) Index))
    (fun _ => pure .stop)
    (fun input next recursivelyContinue =>
      match input with
      | .uniform n => do
          let output ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
          recursivelyContinue output
      | .probe index target =>
          pure (.probe index target (fun _ => next ()))
      | .reveal index => pure (.reveal index next))
    computation

omit [Fintype Index] [DecidableEq Index] in
@[simp]
theorem controller_pure (result : α) :
    controller (pure result : OracleComp (World Index) α) = pure .stop := rfl

omit [Fintype Index] [DecidableEq Index] in
theorem controller_probe_bind
    (index : Index) (target : Digest)
    (next : Unit → OracleComp (World Index) α) :
    controller (probeQuery index target >>= next) =
      pure (.probe index target (fun _ => next ())) := by
  rw [probeQuery, controller, OracleComp.construct_query_bind]

omit [Fintype Index] [DecidableEq Index] in
theorem controller_reveal_bind
    (index : Index) (next : Digest → OracleComp (World Index) α) :
    controller (revealQuery index >>= next) = pure (.reveal index next) := by
  rw [revealQuery, controller, OracleComp.construct_query_bind]

def IsSpecialQuery : (World Index).Domain → Prop
  | .uniform _ => False
  | .probe _ _ => True
  | .reveal _ => True

def IsProbeQuery : (World Index).Domain → Prop
  | .uniform _ => False
  | .probe _ _ => True
  | .reveal _ => False

noncomputable instance : DecidablePred (IsSpecialQuery (Index := Index)) :=
  fun input => match input with
  | .uniform _ => isFalse (by simp [IsSpecialQuery])
  | .probe _ _ => isTrue (by simp [IsSpecialQuery])
  | .reveal _ => isTrue (by simp [IsSpecialQuery])

noncomputable instance : DecidablePred (IsProbeQuery (Index := Index)) :=
  fun input => match input with
  | .uniform _ => isFalse (by simp [IsProbeQuery])
  | .probe _ _ => isTrue (by simp [IsProbeQuery])
  | .reveal _ => isFalse (by simp [IsProbeQuery])

omit [Fintype Index] [DecidableEq Index] in
theorem liftProbComp_isQueryBoundP
    (computation : ProbComp α) (steps : Nat) :
    (liftProbComp (Index := Index) computation).IsQueryBoundP
      IsSpecialQuery steps := by
  induction computation using OracleComp.inductionOn with
  | pure result => trivial
  | query_bind n next ih =>
      rw [liftProbComp, simulateQ_query_bind]
      change (uniformQuery n >>= fun output =>
        liftProbComp (next output)).IsQueryBoundP IsSpecialQuery steps
      rw [uniformQuery, OracleComp.isQueryBoundP_query_bind_iff]
      constructor
      · simp [IsSpecialQuery]
      · intro output
        simpa [IsSpecialQuery] using ih output

omit [Fintype Index] [DecidableEq Index] in
theorem liftProbComp_isProbeQueryBoundP
    (computation : ProbComp α) (probes : Nat) :
    (liftProbComp (Index := Index) computation).IsQueryBoundP
      IsProbeQuery probes := by
  induction computation using OracleComp.inductionOn with
  | pure result => trivial
  | query_bind n next ih =>
      rw [liftProbComp, simulateQ_query_bind]
      change (uniformQuery n >>= fun output =>
        liftProbComp (next output)).IsQueryBoundP IsProbeQuery probes
      rw [uniformQuery, OracleComp.isQueryBoundP_query_bind_iff]
      constructor
      · simp [IsProbeQuery]
      · intro output
        simpa [IsProbeQuery] using ih output

omit [Fintype Index] [DecidableEq Index] in
theorem probeQuery_isProbeQueryBoundP
    (index : Index) (target : Digest) :
    (probeQuery index target).IsQueryBoundP IsProbeQuery 1 := by
  rw [probeQuery, OracleComp.isQueryBoundP_query_iff]
  simp [IsProbeQuery]

omit [Fintype Index] [DecidableEq Index] in
theorem revealQuery_isProbeQueryBoundP (index : Index) (probes : Nat) :
    (revealQuery index).IsQueryBoundP IsProbeQuery probes := by
  rw [revealQuery, OracleComp.isQueryBoundP_query_iff]
  simp [IsProbeQuery]

inductive ObservedAction (Index : Type) where
  | probe (index : Index) (target : Digest)
  | reveal (index : Index) (value : Digest)
deriving DecidableEq

abbrev ActionTrace (Index : Type) := List (ObservedAction Index)

noncomputable def eagerImpl (table : Index → Digest) :
    QueryImpl (World Index) ProbComp := fun input =>
  match input with
  | .uniform n => liftM (unifSpec.query n)
  | .probe _ _ => pure ()
  | .reveal index => pure (table index)

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_eagerImpl_liftProbComp
    (table : Index → Digest) (computation : ProbComp α) :
    simulateQ (eagerImpl table)
      (liftProbComp (Index := Index) computation) = computation := by
  induction computation using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind n next ih =>
      rw [liftProbComp, simulateQ_query_bind, simulateQ_bind]
      simp only [uniformForwardImpl, uniformQuery]
      apply bind_congr
      exact ih

omit [Fintype Index] [DecidableEq Index] in
@[simp]
theorem simulate_eagerImpl_revealQuery
    (table : Index → Digest) (index : Index) :
    simulateQ (eagerImpl table) (revealQuery index) = pure (table index) := by
  simp [revealQuery, eagerImpl]

def traceFragment
    (input : (World Index).Domain) (output : (World Index).Range input) :
    ActionTrace Index :=
  match input with
  | .uniform _ => []
  | .probe index target => [.probe index target]
  | .reveal index => [.reveal index output]

noncomputable def eagerTraceImpl (table : Index → Digest) :
    QueryImpl (World Index) (WriterT (ActionTrace Index) ProbComp) :=
  (eagerImpl table).withTraceAppend traceFragment

omit [Fintype Index] [DecidableEq Index] in
theorem eagerTrace_projection
    (table : Index → Digest)
    (computation : OracleComp (World Index) α) :
    Prod.fst <$> (simulateQ (eagerTraceImpl table) computation).run =
      simulateQ (eagerImpl table) computation := by
  exact QueryImpl.fst_map_run_withTraceAppend
    (eagerImpl table) traceFragment computation

omit [Fintype Index] [DecidableEq Index] in
@[simp]
theorem simulate_eagerTrace_revealQuery
    (table : Index → Digest) (index : Index) :
    (simulateQ (eagerTraceImpl table) (revealQuery index)).run =
      pure (table index, [.reveal index (table index)]) := by
  simp [revealQuery, eagerTraceImpl, eagerImpl, traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell]

def traceHitsAux (table : Index → Digest) (revealed : Finset Index) :
    ActionTrace Index → Bool
  | [] => false
  | .probe index target :: rest =>
      if index ∈ revealed then traceHitsAux table revealed rest
      else decide (table index = target) || traceHitsAux table revealed rest
  | .reveal index _ :: rest => traceHitsAux table (insert index revealed) rest

def traceHits (table : Index → Digest) (trace : ActionTrace Index) : Bool :=
  traceHitsAux table ∅ trace

inductive HasHit (table : Index → Digest) :
    Finset Index → ActionTrace Index → Prop where
  | probe_here {revealed index target rest}
      (hhidden : index ∉ revealed) (hhit : table index = target) :
      HasHit table revealed (.probe index target :: rest)
  | probe_later {revealed index target rest}
      (hlater : HasHit table revealed rest) :
      HasHit table revealed (.probe index target :: rest)
  | reveal_later {revealed index value rest}
      (hlater : HasHit table (insert index revealed) rest) :
      HasHit table revealed (.reveal index value :: rest)

omit [Fintype Index] in
theorem traceHitsAux_eq_true_iff_hasHit
    (table : Index → Digest) (revealed : Finset Index)
    (trace : ActionTrace Index) :
    traceHitsAux table revealed trace = true ↔ HasHit table revealed trace := by
  induction trace generalizing revealed with
  | nil =>
      constructor
      · simp [traceHitsAux]
      · intro hhit
        cases hhit
  | cons action rest ih =>
      cases action with
      | probe index target =>
          by_cases hrevealed : index ∈ revealed
          · simp only [traceHitsAux, hrevealed, ↓reduceIte, ih]
            constructor
            · exact HasHit.probe_later
            · intro hhit
              cases hhit with
              | probe_here hhidden _ => exact False.elim (hhidden hrevealed)
              | probe_later hlater => exact hlater
          · simp only [traceHitsAux, hrevealed, ↓reduceIte, Bool.or_eq_true,
              decide_eq_true_eq, ih]
            constructor
            · rintro (hhit | hlater)
              · exact HasHit.probe_here hrevealed hhit
              · exact HasHit.probe_later hlater
            · intro hhit
              cases hhit with
              | probe_here _ hvalue => exact Or.inl hvalue
              | probe_later hlater => exact Or.inr hlater
      | reveal index value =>
          simp only [traceHitsAux, ih]
          constructor
          · exact HasHit.reveal_later
          · intro hhit
            cases hhit with
            | reveal_later hlater => exact hlater

omit [Fintype Index] in
theorem traceHits_eq_true_iff_hasHit
    (table : Index → Digest) (trace : ActionTrace Index) :
    traceHits table trace = true ↔ HasHit table ∅ trace := by
  exact traceHitsAux_eq_true_iff_hasHit table ∅ trace

omit [Fintype Index] in
theorem HasHit.of_mem_probe_of_no_reveal
    (table : Index → Digest) (trace : ActionTrace Index)
    (index : Index) (target : Digest)
    (hprobe : ObservedAction.probe index target ∈ trace)
    (hnoReveal : ∀ value, ObservedAction.reveal index value ∉ trace)
    (hhit : table index = target) :
    HasHit table ∅ trace := by
  have hgeneral : ∀ (revealed : Finset Index), index ∉ revealed →
      HasHit table revealed trace := by
    intro revealed hhidden
    induction trace generalizing revealed with
    | nil => simp at hprobe
    | cons action rest ih =>
        cases action with
        | probe candidate candidateTarget =>
            rw [List.mem_cons] at hprobe
            rcases hprobe with heq | hlater
            · cases heq
              exact HasHit.probe_here hhidden hhit
            · apply HasHit.probe_later
              apply ih hlater
              · intro value hvalue
                exact hnoReveal value (by simp [hvalue])
              · exact hhidden
        | reveal candidate value =>
            have hlater : ObservedAction.probe index target ∈ rest := by
              simpa using hprobe
            have hne : candidate ≠ index := by
              intro heq
              subst candidate
              exact hnoReveal value (by simp)
            apply HasHit.reveal_later
            apply ih hlater
            · intro candidateValue hvalue
              exact hnoReveal candidateValue (by simp [hvalue])
            · intro hmem
              rw [Finset.mem_insert] at hmem
              exact hmem.elim (fun heq => hne heq.symm) hhidden
  exact hgeneral ∅ (by simp)

noncomputable local instance sampleableTable :
    SampleableType (Index → Digest) :=
  SampleableType.ofFintype (Index → Digest)

noncomputable def eagerTableSample : ProbComp (Index → Digest) :=
  $ᵗ (Index → Digest)

noncomputable def eagerExperiment
    (computation : OracleComp (World Index) α) :
    ProbComp ((Index → Digest) × (α × ActionTrace Index)) := do
  let table ← eagerTableSample
  let result ← (simulateQ (eagerTraceImpl table) computation).run
  return (table, result)

def EagerHit (result : (Index → Digest) × (α × ActionTrace Index)) : Prop :=
  traceHits result.1 result.2.2 = true

def StateValid
    (state : AdaptiveRevealMonitor.State Index) : Prop :=
  ∀ index value, state.revealed index = some value → state.pending index = ∅

def StateAgrees
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index) : Prop :=
  ∀ index value, state.revealed index = some value → table index = value

omit [Fintype Index] [DecidableEq Index] in
theorem stateValid_empty :
    StateValid (AdaptiveRevealMonitor.State.empty :
      AdaptiveRevealMonitor.State Index) := by
  intro index value hvalue
  simp [AdaptiveRevealMonitor.State.empty] at hvalue

omit [Fintype Index] [DecidableEq Index] in
theorem stateAgrees_empty (table : Index → Digest) :
    StateAgrees table (AdaptiveRevealMonitor.State.empty :
      AdaptiveRevealMonitor.State Index) := by
  intro index value hvalue
  simp [AdaptiveRevealMonitor.State.empty] at hvalue

omit [Fintype Index] in
theorem StateValid.addPending
    {state : AdaptiveRevealMonitor.State Index} (hvalid : StateValid state)
    (index : Index) (target : Digest)
    (hhidden : state.revealed index = none) :
    StateValid (state.addPending index target) := by
  intro candidate value hvalue
  by_cases heq : candidate = index
  · subst candidate
    simp [AdaptiveRevealMonitor.State.addPending, hhidden] at hvalue
  · simpa [AdaptiveRevealMonitor.State.addPending,
      Function.update_of_ne heq] using hvalid candidate value hvalue

omit [Fintype Index] in
theorem StateAgrees.addPending
    {table : Index → Digest} {state : AdaptiveRevealMonitor.State Index}
    (hagrees : StateAgrees table state) (index : Index) (target : Digest) :
    StateAgrees table (state.addPending index target) := by
  exact hagrees

omit [Fintype Index] in
theorem StateValid.install
    {state : AdaptiveRevealMonitor.State Index} (hvalid : StateValid state)
    (index : Index) (value : Digest) :
    StateValid (state.install index value) := by
  intro candidate candidateValue hvalue
  by_cases heq : candidate = index
  · subst candidate
    simp [AdaptiveRevealMonitor.State.install]
  · have hvalue' : state.revealed candidate = some candidateValue := by
      simpa [AdaptiveRevealMonitor.State.install,
        Function.update_of_ne heq] using hvalue
    have hpending := hvalid candidate candidateValue hvalue'
    simpa [AdaptiveRevealMonitor.State.install,
      Function.update_of_ne heq] using hpending

omit [Fintype Index] in
theorem StateAgrees.install
    {table : Index → Digest} {state : AdaptiveRevealMonitor.State Index}
    (hagrees : StateAgrees table state) (index : Index) :
    StateAgrees table (state.install index (table index)) := by
  intro candidate value hvalue
  by_cases heq : candidate = index
  · subst candidate
    simpa [AdaptiveRevealMonitor.State.install] using hvalue
  · have hvalue' : state.revealed candidate = some value := by
      simpa [AdaptiveRevealMonitor.State.install,
        Function.update_of_ne heq] using hvalue
    exact hagrees candidate value hvalue'

def extendTable
    (state : AdaptiveRevealMonitor.State Index)
    (base : Index → Digest) : Index → Digest :=
  fun index => (state.revealed index).getD (base index)

omit [Fintype Index] [DecidableEq Index] in
@[simp]
theorem extendTable_empty (base : Index → Digest) :
    extendTable (AdaptiveRevealMonitor.State.empty :
      AdaptiveRevealMonitor.State Index) base = base := by
  funext index
  rfl

omit [Fintype Index] in
theorem extendTable_addPending
    (state : AdaptiveRevealMonitor.State Index)
    (index : Index) (target : Digest) (base : Index → Digest) :
    extendTable (state.addPending index target) base = extendTable state base := rfl

omit [Fintype Index] in
theorem extendTable_update_eq_install
    (state : AdaptiveRevealMonitor.State Index)
    (index : Index) (value : Digest) (base : Index → Digest)
    (hhidden : state.revealed index = none) :
    extendTable state (Function.update base index value) =
      extendTable (state.install index value) base := by
  funext candidate
  by_cases heq : candidate = index
  · subst candidate
    simp [extendTable, AdaptiveRevealMonitor.State.install, hhidden]
  · simp [extendTable, AdaptiveRevealMonitor.State.install,
      Function.update_of_ne heq]

def tableHits
    (state : AdaptiveRevealMonitor.State Index)
    (table : Index → Digest) : Bool :=
  decide (∃ index, table index ∈ state.pending index)

def runObserved
    (table : Index → Digest) :
    AdaptiveRevealMonitor.State Index → ActionTrace Index → Bool
  | state, [] => tableHits state table
  | state, .probe index target :: rest =>
      match state.revealed index with
      | some _ => runObserved table state rest
      | none => runObserved table (state.addPending index target) rest
  | state, .reveal index _ :: rest =>
      match state.revealed index with
      | some _ => runObserved table state rest
      | none =>
          let value := table index
          if value ∈ state.pending index then true
          else runObserved table (state.install index value) rest

def ObservedHit
    (result : (Index → Digest) × (α × ActionTrace Index)) : Prop :=
  runObserved result.1 AdaptiveRevealMonitor.State.empty result.2.2 = true

noncomputable def runStructural
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (fuel : Nat) (computation : OracleComp (World Index) α) : ProbComp Bool :=
  OracleComp.construct
    (C := fun _ => AdaptiveRevealMonitor.State Index → Nat → ProbComp Bool)
    (fun _ state _fuel => pure (tableHits state table))
    (fun input _next recursivelyRun state fuel =>
      match input with
      | .uniform n => do
          let output ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
          recursivelyRun output state fuel
      | .probe index target =>
          match fuel with
          | 0 => pure (tableHits state table)
          | remaining + 1 =>
              match state.revealed index with
              | some _ => recursivelyRun () state remaining
              | none => recursivelyRun () (state.addPending index target) remaining
      | .reveal index =>
          match state.revealed index with
          | some value => recursivelyRun value state fuel
          | none =>
              let value := table index
              if value ∈ state.pending index then pure true
              else recursivelyRun value (state.install index value) fuel)
    computation state fuel

noncomputable def structuralExperiment
    (state : AdaptiveRevealMonitor.State Index)
    (fuel : Nat) (computation : OracleComp (World Index) α) : ProbComp Bool := do
  let base ← $ᵗ (Index → Digest)
  runStructural (extendTable state base) state fuel computation

noncomputable def runEager {Control : Type}
    (controller : Control → ProbComp
      (AdaptiveRevealMonitor.ControllerAction Control Index))
    (table : Index → Digest)
    (state : AdaptiveRevealMonitor.State Index)
    (steps fuel : Nat) (control : Control) : ProbComp Bool :=
  match steps with
  | 0 => pure (tableHits state table)
  | steps + 1 => do
      let action ← controller control
      match action with
      | .stop => pure (tableHits state table)
      | .skip next => runEager controller table state steps fuel next
      | .probe index target next =>
          match fuel with
          | 0 => pure (tableHits state table)
          | remaining + 1 =>
              match state.revealed index with
              | some _ => runEager controller table state steps remaining (next false)
              | none =>
                  runEager controller table (state.addPending index target) steps remaining
                    (next false)
      | .reveal index next =>
          match state.revealed index with
          | some value => runEager controller table state steps fuel (next value)
          | none =>
              let value := table index
              if value ∈ state.pending index then pure true
              else
                runEager controller table (state.install index value) steps fuel (next value)

noncomputable def eagerControllerExperiment {Control : Type}
    (controller : Control → ProbComp
      (AdaptiveRevealMonitor.ControllerAction Control Index))
    (state : AdaptiveRevealMonitor.State Index)
    (steps fuel : Nat) (control : Control) : ProbComp Bool := do
  let base ← $ᵗ (Index → Digest)
  runEager controller (extendTable state base) state steps fuel control

omit [DecidableEq Index] in
theorem tableHits_extendTable_eq_true_iff
    (state : AdaptiveRevealMonitor.State Index) (hvalid : StateValid state)
    (base : Index → Digest) :
    tableHits state (extendTable state base) = true ↔
      ∃ index ∈ (Finset.univ : Finset Index),
        ∃ target ∈ state.pending index, base index = target := by
  simp only [tableHits, decide_eq_true_eq, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨index, hmem⟩
    have hhidden : state.revealed index = none := by
      cases hvalue : state.revealed index with
      | none => rfl
      | some value =>
          have hempty := hvalid index value hvalue
          rw [hempty] at hmem
          simp at hmem
    refine ⟨index, ⟨extendTable state base index, hmem, ?_⟩⟩
    simp [extendTable, hhidden]
  · rintro ⟨index, target, htarget, heq⟩
    have hhidden : state.revealed index = none := by
      cases hvalue : state.revealed index with
      | none => rfl
      | some value =>
          have hempty := hvalid index value hvalue
          rw [hempty] at htarget
          simp at htarget
    exact ⟨index, by simpa [extendTable, hhidden, heq] using htarget⟩

theorem eagerFinalize_true_probability_le
    (state : AdaptiveRevealMonitor.State Index) (hvalid : StateValid state) :
    Pr[(fun hit : Bool => hit = true) |
      (fun base : Index → Digest => tableHits state (extendTable state base)) <$>
        ($ᵗ (Index → Digest))] ≤
      (state.pendingCount : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [probEvent_map]
  change Pr[(fun base : Index → Digest =>
    tableHits state (extendTable state base) = true) |
      $ᵗ (Index → Digest)] ≤ _
  have hevent :
      (fun base : Index → Digest =>
        tableHits state (extendTable state base) = true) =
      (fun base : Index → Digest =>
        ∃ index ∈ (Finset.univ : Finset Index),
          ∃ target ∈ state.pending index, base index = target) := by
    funext base
    exact propext (tableHits_extendTable_eq_true_iff state hvalid base)
  rw [hevent]
  calc
    Pr[fun base : Index → Digest =>
          ∃ index ∈ (Finset.univ : Finset Index),
            ∃ target ∈ state.pending index, base index = target |
        $ᵗ (Index → Digest)] ≤
      ∑ index ∈ (Finset.univ : Finset Index),
        Pr[fun base : Index → Digest =>
            ∃ target ∈ state.pending index, base index = target |
          $ᵗ (Index → Digest)] :=
        probEvent_exists_finset_le_sum Finset.univ ($ᵗ (Index → Digest))
          (fun index base =>
            ∃ target ∈ state.pending index, base index = target)
    _ ≤ ∑ index ∈ (Finset.univ : Finset Index),
        ((state.pending index).card : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro index _hindex
      calc
        Pr[fun base : Index → Digest =>
              ∃ target ∈ state.pending index, base index = target |
            $ᵗ (Index → Digest)] ≤
          ∑ target ∈ state.pending index,
            Pr[fun base : Index → Digest => base index = target |
              $ᵗ (Index → Digest)] :=
            probEvent_exists_finset_le_sum (state.pending index)
              ($ᵗ (Index → Digest))
              (fun target base => base index = target)
        _ = ∑ _target ∈ state.pending index,
            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
          apply Finset.sum_congr rfl
          intro target _htarget
          exact IndexedHiddenValue.uniform_table_coordinate_probability index target
        _ = ((state.pending index).card : ℝ≥0∞) *
            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (state.pendingCount : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [← Finset.sum_mul]
      congr 1
      simp [AdaptiveRevealMonitor.State.pendingCount]

theorem uniformDigest_mem_finset_le (targets : Finset Digest) :
    Pr[(fun value : Digest => value ∈ targets) | $ᵗ Digest] ≤
      (targets.card : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    Pr[(fun value : Digest => value ∈ targets) | $ᵗ Digest] =
      Pr[(fun value : Digest => ∃ target ∈ targets, value = target) |
        $ᵗ Digest] := by
      apply probEvent_congr' (fun value _ => by simp) rfl
    _ ≤ ∑ target ∈ targets,
        Pr[(fun value : Digest => value = target) | $ᵗ Digest] :=
      probEvent_exists_finset_le_sum targets ($ᵗ Digest)
        (fun target value => value = target)
    _ = ∑ _target ∈ targets,
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_congr rfl
      intro target _htarget
      rw [probEvent_uniformSample]
      have hfilter :
          (Finset.univ.filter (fun value : Digest => value = target)) =
            {target} := by
        ext value
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
      rw [hfilter, Finset.card_singleton, HiddenValue.card_digest]
      simp only [Nat.cast_one, one_div]
    _ = (targets.card : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]

theorem evalDist_uniformTable_eq_bind_update
    (index : Index) (continuation : (Index → Digest) → ProbComp α) :
    𝒟[($ᵗ (Index → Digest)) >>= continuation] =
      𝒟[do
        let value ← $ᵗ Digest
        let base ← $ᵗ (Index → Digest)
        continuation (Function.update base index value)] := by
  calc
    𝒟[($ᵗ (Index → Digest)) >>= continuation] =
        𝒟[(do
          let value ← $ᵗ Digest
          let base ← $ᵗ (Index → Digest)
          pure (Function.update base index value)) >>= continuation] := by
      rw [evalDist_bind, evalDist_bind, evalDist_uniformSample_bind_update index]
    _ = _ := by simp [bind_assoc]

/-- A revealed coordinate of a uniform table can be sampled first and installed into an otherwise
uniform base table. This continuation form supports adaptive computations after the reveal. -/
theorem evalDist_uniformTable_bind_coordinate_continuation
    (index : Index)
    (continuation : (Index → Digest) → Digest → ProbComp α) :
    𝒟[do
      let table ← $ᵗ (Index → Digest)
      continuation table (table index)] =
    𝒟[do
      let value ← $ᵗ Digest
      let base ← $ᵗ (Index → Digest)
      continuation (Function.update base index value) value] := by
  calc
    𝒟[do
      let table ← $ᵗ (Index → Digest)
      continuation table (table index)] =
        𝒟[do
          let value ← $ᵗ Digest
          let base ← $ᵗ (Index → Digest)
          let table := Function.update base index value
          continuation table (table index)] :=
      evalDist_uniformTable_eq_bind_update index fun table =>
        continuation table (table index)
    _ = _ := by simp only [Function.update_self]

/-- Revealing one coordinate of a uniform table and programming a hash output with that digest is
equivalent to drawing an ordinary uniform hash output and installing its truncation at that
coordinate. The continuation sees the updated table, its revealed coordinate, and the hash output. -/
theorem evalDist_uniformTable_bind_programmedCoordinate_continuation
    (index : Index)
    (continuation : (Index → Digest) → Digest → HashOutput → ProbComp α) :
    𝒟[do
      let table ← $ᵗ (Index → Digest)
      let output ← Rom.sampleHashOutputWithDigest (table index)
      continuation table (table index) output] =
    𝒟[do
      let output ← $ᵗ HashOutput
      let base ← $ᵗ (Index → Digest)
      let table := Function.update base index (truncateHash output)
      continuation table (truncateHash output) output] := by
  calc
    𝒟[do
      let table ← $ᵗ (Index → Digest)
      let output ← Rom.sampleHashOutputWithDigest (table index)
      continuation table (table index) output] =
        𝒟[do
          let value ← $ᵗ Digest
          let base ← $ᵗ (Index → Digest)
          let table := Function.update base index value
          let output ← Rom.sampleHashOutputWithDigest (table index)
          continuation table (table index) output] :=
      evalDist_uniformTable_eq_bind_update index fun table => do
        let output ← Rom.sampleHashOutputWithDigest (table index)
        continuation table (table index) output
    _ = 𝒟[do
          let value ← $ᵗ Digest
          let output ← Rom.sampleHashOutputWithDigest value
          let base ← $ᵗ (Index → Digest)
          continuation (Function.update base index value) value output] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro value
      calc
        𝒟[do
          let base ← $ᵗ (Index → Digest)
          let table := Function.update base index value
          let output ← Rom.sampleHashOutputWithDigest (table index)
          continuation table (table index) output] =
            𝒟[do
              let base ← $ᵗ (Index → Digest)
              let output ← Rom.sampleHashOutputWithDigest value
              continuation (Function.update base index value) value output] := by
                simp only [Function.update_self]
        _ = _ := OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[Rom.sampledHashOutputWithDigest >>= fun programmed =>
          $ᵗ (Index → Digest) >>= fun base =>
            continuation (Function.update base index programmed.1)
              programmed.1 programmed.2] := by
      simp [Rom.sampledHashOutputWithDigest, bind_assoc]
    _ = _ := Rom.evalDist_sampledHashOutputWithDigest_bind_eq_uniform_bind
      (fun programmed =>
        $ᵗ (Index → Digest) >>= fun base =>
          continuation (Function.update base index programmed.1)
            programmed.1 programmed.2)

theorem evalDist_uniformTable_bind_programmedCoordinate
    (index : Index)
    (finish : (Index → Digest) → Digest → HashOutput → α) :
    𝒟[do
      let table ← $ᵗ (Index → Digest)
      let output ← Rom.sampleHashOutputWithDigest (table index)
      pure (finish table (table index) output)] =
    𝒟[do
      let output ← $ᵗ HashOutput
      let base ← $ᵗ (Index → Digest)
      let table := Function.update base index (truncateHash output)
      pure (finish table (truncateHash output) output)] := by
  exact evalDist_uniformTable_bind_programmedCoordinate_continuation index
    (fun table value output => pure (finish table value output))

set_option maxRecDepth 100000 in
theorem eagerController_true_probability_le {Control : Type}
    (controller : Control → ProbComp
      (AdaptiveRevealMonitor.ControllerAction Control Index))
    (state : AdaptiveRevealMonitor.State Index) (hvalid : StateValid state)
    (steps fuel : Nat) (control : Control) :
    Pr[(fun hit : Bool => hit = true) |
      eagerControllerExperiment controller state steps fuel control] ≤
      ((fuel + state.pendingCount : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction steps generalizing state fuel control with
  | zero =>
      change Pr[(fun hit : Bool => hit = true) |
        (fun base : Index → Digest =>
          tableHits state (extendTable state base)) <$>
            ($ᵗ (Index → Digest))] ≤ _
      refine (eagerFinalize_true_probability_le state hvalid).trans ?_
      gcongr
      omega
  | succ steps ih =>
      let resume : (Index → Digest) →
          AdaptiveRevealMonitor.ControllerAction Control Index → ProbComp Bool :=
        fun base action =>
        match action with
        | .stop => pure (tableHits state (extendTable state base))
        | .skip next =>
            runEager controller (extendTable state base) state steps fuel next
        | .probe index target next =>
            match fuel with
            | 0 => pure (tableHits state (extendTable state base))
            | remaining + 1 =>
                match state.revealed index with
                | some _ => runEager controller (extendTable state base) state
                    steps remaining (next false)
                | none => runEager controller (extendTable state base)
                    (state.addPending index target) steps remaining (next false)
        | .reveal index next =>
            match state.revealed index with
            | some value => runEager controller (extendTable state base) state
                steps fuel (next value)
            | none =>
                let value := extendTable state base index
                if value ∈ state.pending index then pure true
                else runEager controller (extendTable state base)
                  (state.install index value) steps fuel (next value)
      have hswap :
          𝒟[eagerControllerExperiment controller state (steps + 1) fuel control] =
            𝒟[controller control >>= fun action =>
              ($ᵗ (Index → Digest)) >>= fun base => resume base action] := by
        change 𝒟[($ᵗ (Index → Digest)) >>= fun base =>
            controller control >>= fun action => resume base action] = _
        exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
      refine (probEvent_congr' (fun _ _ => Iff.rfl) hswap).le.trans ?_
      refine probEvent_bind_le_of_forall_le fun action _haction => ?_
      cases action with
      | stop =>
          change Pr[(fun hit : Bool => hit = true) |
            (fun base : Index → Digest =>
              tableHits state (extendTable state base)) <$>
                ($ᵗ (Index → Digest))] ≤ _
          refine (eagerFinalize_true_probability_le state hvalid).trans ?_
          gcongr
          omega
      | skip next =>
          change Pr[(fun hit : Bool => hit = true) |
            eagerControllerExperiment controller state steps fuel next] ≤ _
          exact ih state hvalid fuel next
      | probe index target next =>
          cases fuel with
          | zero =>
              simp only [resume]
              change Pr[(fun hit : Bool => hit = true) |
                (fun base : Index → Digest =>
                  tableHits state (extendTable state base)) <$>
                    ($ᵗ (Index → Digest))] ≤ _
              simpa using eagerFinalize_true_probability_le state hvalid
          | succ remaining =>
              cases hrevealed : state.revealed index with
              | some value =>
                  simp only [resume, hrevealed]
                  change Pr[(fun hit : Bool => hit = true) |
                    eagerControllerExperiment controller state steps remaining
                      (next false)] ≤ _
                  refine (ih state hvalid remaining (next false)).trans ?_
                  gcongr
                  omega
              | none =>
                  simp only [resume, hrevealed]
                  change Pr[(fun hit : Bool => hit = true) |
                    eagerControllerExperiment controller
                      (state.addPending index target) steps remaining
                      (next false)] ≤ _
                  refine (ih (state.addPending index target)
                    (hvalid.addPending index target hrevealed) remaining
                    (next false)).trans ?_
                  have hadd := state.pendingCount_addPending_le index target
                  have hnat :
                      remaining + (state.addPending index target).pendingCount ≤
                        remaining + 1 + state.pendingCount := by omega
                  exact mul_le_mul_left (by exact_mod_cast hnat)
                    (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
      | reveal index next =>
          cases hrevealed : state.revealed index with
          | some value =>
              simp only [resume, hrevealed]
              change Pr[(fun hit : Bool => hit = true) |
                eagerControllerExperiment controller state steps fuel
                  (next value)] ≤ _
              exact ih state hvalid fuel (next value)
          | none =>
              simp only [resume, hrevealed]
              let continuation := fun (base : Index → Digest) =>
                let table := extendTable state base
                let value := table index
                if value ∈ state.pending index then pure true
                else runEager controller table (state.install index value)
                  steps fuel (next value)
              have hrevealDist :
                  𝒟[($ᵗ (Index → Digest)) >>= continuation] =
                    𝒟[do
                      let value ← $ᵗ Digest
                      let base ← $ᵗ (Index → Digest)
                      if value ∈ state.pending index then pure true
                      else
                        runEager controller (extendTable (state.install index value) base)
                          (state.install index value) steps fuel (next value)] := by
                rw [evalDist_uniformTable_eq_bind_update index continuation]
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro value
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro base
                simp only [continuation]
                have htable := extendTable_update_eq_install state index value base hrevealed
                rw [htable]
                have hinstalled :
                    extendTable (state.install index value) base index = value := by
                  simp [extendTable, AdaptiveRevealMonitor.State.install]
                rw [hinstalled]
              change Pr[(fun hit : Bool => hit = true) |
                ($ᵗ (Index → Digest)) >>= continuation] ≤ _
              refine (probEvent_congr' (fun _ _ => Iff.rfl) hrevealDist).le.trans ?_
              refine (probEvent_bind_le_probEvent_add
                (mx := ($ᵗ Digest))
                (my := fun value => do
                  let base ← $ᵗ (Index → Digest)
                  if value ∈ state.pending index then pure true
                  else
                    runEager controller (extendTable (state.install index value) base)
                      (state.install index value) steps fuel (next value))
                (q := fun hit : Bool => hit = true)
                (p := fun value : Digest => value ∈ state.pending index)
                (ε := ((fuel + (state.install index 0).pendingCount : Nat) :
                    ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
                ?_).trans ?_
              · intro value _hvalue hmiss
                simp only [hmiss, ↓reduceIte]
                have hcount :
                    (state.install index value).pendingCount =
                      (state.install index 0).pendingCount := rfl
                change Pr[(fun hit : Bool => hit = true) |
                  eagerControllerExperiment controller (state.install index value)
                    steps fuel (next value)] ≤ _
                simpa [hcount] using ih (state.install index value)
                  (hvalid.install index value) fuel (next value)
              · refine add_le_add (uniformDigest_mem_finset_le
                    (state.pending index)) le_rfl |>.trans ?_
                have hconserve := state.pendingCount_install_add index 0
                rw [← add_mul]
                gcongr
                rw [← Nat.cast_add]
                exact Nat.cast_le.mpr (by omega)

theorem eagerController_empty_true_probability_le {Control : Type}
    (controller : Control → ProbComp
      (AdaptiveRevealMonitor.ControllerAction Control Index))
    (steps fuel : Nat) (control : Control) :
    Pr[(fun hit : Bool => hit = true) |
      eagerControllerExperiment controller AdaptiveRevealMonitor.State.empty
        steps fuel control] ≤
      (fuel : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  simpa [div_eq_mul_inv] using eagerController_true_probability_le controller
    (AdaptiveRevealMonitor.State.empty : AdaptiveRevealMonitor.State Index)
    stateValid_empty steps fuel control

noncomputable def eagerProgramExperiment
    (steps probes : Nat) (computation : OracleComp (World Index) α) :
    ProbComp Bool :=
  eagerControllerExperiment controller AdaptiveRevealMonitor.State.empty
    steps probes computation

theorem eagerProgram_true_probability_le
    (steps probes : Nat) (computation : OracleComp (World Index) α) :
    Pr[(fun hit : Bool => hit = true) |
      eagerProgramExperiment steps probes computation] ≤
      (probes : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  exact eagerController_empty_true_probability_le controller
    steps probes computation

set_option maxRecDepth 100000 in
theorem structuralExperiment_true_probability_le
    (state : AdaptiveRevealMonitor.State Index) (hvalid : StateValid state)
    (fuel : Nat) (computation : OracleComp (World Index) α)
    (hbound : computation.IsQueryBoundP IsProbeQuery fuel) :
    Pr[(fun hit : Bool => hit = true) |
      structuralExperiment state fuel computation] ≤
      ((fuel + state.pendingCount : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure result =>
      change Pr[(fun hit : Bool => hit = true) |
        (fun base : Index → Digest =>
          tableHits state (extendTable state base)) <$>
            ($ᵗ (Index → Digest))] ≤ _
      refine (eagerFinalize_true_probability_le state hvalid).trans ?_
      gcongr
      omega
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | uniform n =>
          let resume := fun (base : Index → Digest) (output : Fin (n + 1)) =>
            runStructural (extendTable state base) state fuel (next output)
          have hswap :
              𝒟[structuralExperiment state fuel
                  (liftM ((World Index).query (.uniform n)) >>= next)] =
                𝒟[(liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>=
                  fun output => ($ᵗ (Index → Digest)) >>= fun base =>
                    resume base output] := by
            change 𝒟[($ᵗ (Index → Digest)) >>= fun base =>
                (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>=
                  fun output => resume base output] = _
            exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          refine (probEvent_congr' (fun _ _ => Iff.rfl) hswap).le.trans ?_
          refine probEvent_bind_le_of_forall_le fun output _houtput => ?_
          change Pr[(fun hit : Bool => hit = true) |
            structuralExperiment state fuel (next output)] ≤ _
          exact ih output state hvalid fuel
            (by simpa [IsProbeQuery] using hbound.2 output)
      | probe index target =>
          simp only [structuralExperiment, runStructural,
            OracleComp.construct_query_bind]
          cases fuel with
          | zero => simp [IsProbeQuery] at hbound
          | succ remaining =>
              cases hrevealed : state.revealed index with
              | some value =>
                  change Pr[(fun hit : Bool => hit = true) |
                    structuralExperiment state remaining (next ())] ≤ _
                  refine (ih () state hvalid remaining
                    (by simpa [IsProbeQuery] using hbound.2 ())).trans ?_
                  gcongr
                  omega
              | none =>
                  change Pr[(fun hit : Bool => hit = true) |
                    structuralExperiment (state.addPending index target)
                      remaining (next ())] ≤ _
                  refine (ih () (state.addPending index target)
                    (hvalid.addPending index target hrevealed) remaining
                    (by simpa [IsProbeQuery] using hbound.2 ())).trans ?_
                  have hadd := state.pendingCount_addPending_le index target
                  have hnat :
                      remaining + (state.addPending index target).pendingCount ≤
                        remaining + 1 + state.pendingCount := by omega
                  exact mul_le_mul_left (by exact_mod_cast hnat)
                    (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
      | reveal index =>
          simp only [structuralExperiment, runStructural,
            OracleComp.construct_query_bind]
          cases hrevealed : state.revealed index with
          | some value =>
              change Pr[(fun hit : Bool => hit = true) |
                structuralExperiment state fuel (next value)] ≤ _
              exact ih value state hvalid fuel
                (by simpa [IsProbeQuery] using hbound.2 value)
          | none =>
              let continuation := fun (base : Index → Digest) =>
                let table := extendTable state base
                let value := table index
                if value ∈ state.pending index then pure true
                else runStructural table (state.install index value) fuel (next value)
              have hrevealDist :
                  𝒟[($ᵗ (Index → Digest)) >>= continuation] =
                    𝒟[do
                      let value ← $ᵗ Digest
                      let base ← $ᵗ (Index → Digest)
                      if value ∈ state.pending index then pure true
                      else
                        runStructural (extendTable (state.install index value) base)
                          (state.install index value) fuel (next value)] := by
                rw [evalDist_uniformTable_eq_bind_update index continuation]
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro value
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro base
                simp only [continuation]
                have htable := extendTable_update_eq_install state index value base hrevealed
                rw [htable]
                have hinstalled :
                    extendTable (state.install index value) base index = value := by
                  simp [extendTable, AdaptiveRevealMonitor.State.install]
                rw [hinstalled]
              change Pr[(fun hit : Bool => hit = true) |
                ($ᵗ (Index → Digest)) >>= continuation] ≤ _
              refine (probEvent_congr' (fun _ _ => Iff.rfl) hrevealDist).le.trans ?_
              refine (probEvent_bind_le_probEvent_add
                (mx := ($ᵗ Digest))
                (my := fun value => do
                  let base ← $ᵗ (Index → Digest)
                  if value ∈ state.pending index then pure true
                  else
                    runStructural (extendTable (state.install index value) base)
                      (state.install index value) fuel (next value))
                (q := fun hit : Bool => hit = true)
                (p := fun value : Digest => value ∈ state.pending index)
                (ε := ((fuel + (state.install index 0).pendingCount : Nat) :
                    ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
                ?_).trans ?_
              · intro value _hvalue hmiss
                simp only [hmiss, ↓reduceIte]
                have hcount :
                    (state.install index value).pendingCount =
                      (state.install index 0).pendingCount := rfl
                change Pr[(fun hit : Bool => hit = true) |
                  structuralExperiment (state.install index value) fuel
                    (next value)] ≤ _
                simpa [hcount] using ih value (state.install index value)
                  (hvalid.install index value) fuel
                  (by simpa [IsProbeQuery] using hbound.2 value)
              · refine add_le_add (uniformDigest_mem_finset_le
                    (state.pending index)) le_rfl |>.trans ?_
                have hconserve := state.pendingCount_install_add index 0
                rw [← add_mul]
                gcongr
                rw [← Nat.cast_add]
                exact Nat.cast_le.mpr (by omega)

theorem structuralExperiment_empty_true_probability_le
    (fuel : Nat) (computation : OracleComp (World Index) α)
    (hbound : computation.IsQueryBoundP IsProbeQuery fuel) :
    Pr[(fun hit : Bool => hit = true) |
      structuralExperiment AdaptiveRevealMonitor.State.empty fuel computation] ≤
      (fuel : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  simpa [div_eq_mul_inv] using structuralExperiment_true_probability_le
    (AdaptiveRevealMonitor.State.empty : AdaptiveRevealMonitor.State Index)
    stateValid_empty fuel computation hbound

noncomputable def runTracedObserved
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (computation : OracleComp (World Index) α) : ProbComp Bool :=
  (fun result => runObserved table state result.2) <$>
    (simulateQ (eagerTraceImpl table) computation).run

noncomputable def applyObservedAction
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (action : ObservedAction Index)
    (resume : AdaptiveRevealMonitor.State Index → ProbComp Bool) : ProbComp Bool :=
  match action with
  | .probe index target =>
      match state.revealed index with
      | some _ => resume state
      | none => resume (state.addPending index target)
  | .reveal index _ =>
      match state.revealed index with
      | some _ => resume state
      | none =>
          let value := table index
          if value ∈ state.pending index then pure true
          else resume (state.install index value)

theorem runTracedObserved_cons_probability_le
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (hagrees : StateAgrees table state)
    (action : ObservedAction Index)
    (computation : OracleComp (World Index) α)
    (resume : AdaptiveRevealMonitor.State Index → ProbComp Bool)
    (hresume : ∀ nextState, StateAgrees table nextState →
      Pr[(fun hit : Bool => hit = true) |
        runTracedObserved table nextState computation] ≤
      Pr[(fun hit : Bool => hit = true) | resume nextState]) :
    Pr[(fun hit : Bool => hit = true) |
      (fun result => runObserved table state (action :: result.2)) <$>
        (simulateQ (eagerTraceImpl table) computation).run] ≤
    Pr[(fun hit : Bool => hit = true) |
      applyObservedAction table state action resume] := by
  cases action with
  | probe index target =>
      cases hrevealed : state.revealed index with
      | some value =>
          simpa [runObserved, applyObservedAction, hrevealed,
            runTracedObserved] using hresume state hagrees
      | none =>
          simpa [runObserved, applyObservedAction, hrevealed,
            runTracedObserved] using hresume (state.addPending index target)
              (hagrees.addPending index target)
  | reveal index observedValue =>
      cases hrevealed : state.revealed index with
      | some value =>
          simpa [runObserved, applyObservedAction, hrevealed,
            runTracedObserved] using hresume state hagrees
      | none =>
          by_cases hhit : table index ∈ state.pending index
          · simp [runObserved, applyObservedAction, hrevealed, hhit]
          · simpa [runObserved, applyObservedAction, hrevealed, hhit,
              runTracedObserved] using
                hresume (state.install index (table index)) (hagrees.install index)

theorem runTracedObserved_probability_le_structural
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (hagrees : StateAgrees table state)
    (fuel : Nat) (computation : OracleComp (World Index) α)
    (hbound : computation.IsQueryBoundP IsProbeQuery fuel) :
    Pr[(fun hit : Bool => hit = true) |
      runTracedObserved table state computation] ≤
    Pr[(fun hit : Bool => hit = true) |
      runStructural table state fuel computation] := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure result =>
      simp [runTracedObserved, runStructural, eagerTraceImpl, runObserved]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      simp only [runTracedObserved, simulateQ_query_bind, WriterT.run_bind',
        runStructural, OracleComp.construct_query_bind]
      cases input with
      | uniform n =>
          simp only [OracleQuery.input_query, monadLift_self, eagerTraceImpl,
            QueryImpl.withTraceAppend_apply, eagerImpl, traceFragment,
            WriterT.run_bind', WriterT.run_monadLift', WriterT.run_tell,
            WriterT.run_pure', map_eq_bind_pure_comp, bind_assoc, pure_bind,
            List.nil_append, Prod.map_apply, id_eq, Function.comp_apply]
          apply probEvent_bind_mono
          intro output _houtput
          change Pr[(fun hit : Bool => hit = true) |
              runTracedObserved table state (next output)] ≤
            Pr[(fun hit : Bool => hit = true) |
              runStructural table state fuel (next output)]
          exact ih output state hagrees fuel
            (by simpa [IsProbeQuery] using hbound.2 output)
      | probe index target =>
          cases fuel with
          | zero => simp [IsProbeQuery] at hbound
          | succ remaining =>
              simp only [OracleQuery.input_query, monadLift_self, eagerTraceImpl,
                QueryImpl.withTraceAppend_apply, eagerImpl, traceFragment,
                WriterT.run_bind', WriterT.run_monadLift', WriterT.run_tell,
                WriterT.run_pure', map_eq_bind_pure_comp, bind_assoc, pure_bind,
                Prod.map_apply, id_eq, Function.comp_apply]
              exact runTracedObserved_cons_probability_le table state hagrees
                (.probe index target) (next ())
                (fun nextState => runStructural table nextState remaining (next ()))
                (fun nextState hnextAgrees => ih () nextState hnextAgrees remaining
                  (by simpa [IsProbeQuery] using hbound.2 ()))
      | reveal index =>
          simp only [OracleQuery.input_query, monadLift_self, eagerTraceImpl,
            QueryImpl.withTraceAppend_apply, eagerImpl, traceFragment,
            WriterT.run_bind', WriterT.run_monadLift', WriterT.run_tell,
            WriterT.run_pure', map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Prod.map_apply, id_eq, Function.comp_apply]
          cases hrevealed : state.revealed index with
          | some value =>
              have hvalue := hagrees index value hrevealed
              subst value
              convert
                (runTracedObserved_cons_probability_le table state hagrees
                  (.reveal index (table index)) (next (table index))
                  (fun nextState =>
                    runStructural table nextState fuel (next (table index)))
                  (fun nextState hnextAgrees =>
                    ih (table index) nextState hnextAgrees fuel
                      (by simpa [IsProbeQuery] using hbound.2 (table index)))) using 1 <;>
                simp [hrevealed, applyObservedAction,
                  runStructural, eagerTraceImpl]
          | none =>
              convert
                (runTracedObserved_cons_probability_le table state hagrees
                  (.reveal index (table index)) (next (table index))
                  (fun nextState =>
                    runStructural table nextState fuel (next (table index)))
                  (fun nextState hnextAgrees =>
                    ih (table index) nextState hnextAgrees fuel
                      (by simpa [IsProbeQuery] using hbound.2 (table index)))) using 1 <;>
                simp [hrevealed, applyObservedAction,
                  runStructural, eagerTraceImpl]

noncomputable def tracedTableExperiment
    (computation : OracleComp (World Index) α) : ProbComp Bool := do
  let table ← eagerTableSample
  runTracedObserved table AdaptiveRevealMonitor.State.empty computation

theorem map_eagerExperiment_observed_eq_tracedTableExperiment
    (computation : OracleComp (World Index) α) :
    (fun result =>
      runObserved result.1 AdaptiveRevealMonitor.State.empty result.2.2) <$>
        eagerExperiment computation =
      tracedTableExperiment computation := by
  unfold eagerExperiment tracedTableExperiment runTracedObserved
  simp [map_bind, Functor.map_map]

theorem eagerExperiment_observedHit_probability_le
    (fuel : Nat) (computation : OracleComp (World Index) α)
    (hbound : computation.IsQueryBoundP IsProbeQuery fuel) :
    Pr[ObservedHit | eagerExperiment computation] ≤
      (fuel : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  change Pr[(fun result =>
    runObserved result.1 AdaptiveRevealMonitor.State.empty result.2.2 = true) |
      eagerExperiment computation] ≤ _
  change Pr[((fun hit : Bool => hit = true) ∘ fun result =>
    runObserved result.1 AdaptiveRevealMonitor.State.empty result.2.2) |
      eagerExperiment computation] ≤ _
  rw [← probEvent_map,
    map_eagerExperiment_observed_eq_tracedTableExperiment]
  refine (show Pr[(fun hit : Bool => hit = true) |
      tracedTableExperiment computation] ≤
        Pr[(fun hit : Bool => hit = true) |
          structuralExperiment AdaptiveRevealMonitor.State.empty fuel computation] by
    unfold tracedTableExperiment structuralExperiment
    apply probEvent_bind_mono
    intro table _htable
    exact runTracedObserved_probability_le_structural table
      AdaptiveRevealMonitor.State.empty (stateAgrees_empty table)
      fuel computation hbound).trans
        (structuralExperiment_empty_true_probability_le fuel computation hbound)

def emitProbes : List (Index × Digest) → OracleComp (World Index) Unit
  | [] => pure ()
  | probe :: probes => do
      probeQuery probe.1 probe.2
      emitProbes probes

def emitReveals : List Index → OracleComp (World Index) Unit
  | [] => pure ()
  | index :: indices => do
      let _value ← revealQuery index
      emitReveals indices

def emitTranscript
    (probes : List (Index × Digest)) (reveals : List Index) :
    OracleComp (World Index) Unit := do
  emitProbes probes
  emitReveals reveals

def observedProbeCount : ActionTrace Index → Nat
  | [] => 0
  | .probe _ _ :: rest => (observedProbeCount rest).succ
  | .reveal _ _ :: rest => observedProbeCount rest

omit [Fintype Index] [DecidableEq Index] in
theorem observedProbeCount_append
    (left right : ActionTrace Index) :
    observedProbeCount (left ++ right) =
      observedProbeCount left + observedProbeCount right := by
  induction left with
  | nil => simp [observedProbeCount]
  | cons action rest ih =>
      cases action with
      | probe index target =>
          simp only [List.cons_append, observedProbeCount, ih]
          omega
      | reveal index value =>
          simp only [List.cons_append, observedProbeCount, ih]

def emitObservedTrace : ActionTrace Index → OracleComp (World Index) Unit
  | [] => pure ()
  | .probe index target :: rest => do
      probeQuery index target
      emitObservedTrace rest
  | .reveal index _value :: rest => do
      let _actualValue ← revealQuery index
      emitObservedTrace rest

omit [Fintype Index] [DecidableEq Index] in
theorem emitObservedTrace_isProbeQueryBoundP
    (trace : ActionTrace Index) :
    (emitObservedTrace trace).IsQueryBoundP IsProbeQuery
      (observedProbeCount trace) := by
  induction trace with
  | nil => trivial
  | cons action rest ih =>
      cases action with
      | probe index target =>
          rw [emitObservedTrace, probeQuery,
            OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simp [IsProbeQuery, observedProbeCount]
          · intro output
            simpa [IsProbeQuery, observedProbeCount] using ih
      | reveal index value =>
          rw [emitObservedTrace, revealQuery,
            OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simp [IsProbeQuery, observedProbeCount]
          · intro output
            simpa [IsProbeQuery, observedProbeCount] using ih

def TraceAgrees (table : Index → Digest) : ActionTrace Index → Prop
  | [] => True
  | .probe _ _ :: rest => TraceAgrees table rest
  | .reveal index value :: rest => table index = value ∧ TraceAgrees table rest

omit [Fintype Index] [DecidableEq Index] in
theorem traceAgrees_append
    (table : Index → Digest) (left right : ActionTrace Index) :
    TraceAgrees table (left ++ right) ↔
      TraceAgrees table left ∧ TraceAgrees table right := by
  induction left with
  | nil => simp [TraceAgrees]
  | cons action rest ih =>
      cases action <;> simp [TraceAgrees, ih, and_assoc]

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_eagerTrace_emitObservedTrace
    (table : Index → Digest) (trace : ActionTrace Index)
    (hagrees : TraceAgrees table trace) :
    (simulateQ (eagerTraceImpl table) (emitObservedTrace trace)).run =
      pure ((), trace) := by
  induction trace with
  | nil => simp [emitObservedTrace]
  | cons action rest ih =>
      cases action with
      | probe index target =>
          simp only [TraceAgrees] at hagrees
          simp [emitObservedTrace, probeQuery, simulateQ_bind,
            eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell]
          change (fun x => (x.1, .probe index target :: x.2)) <$>
              (simulateQ (eagerTraceImpl table) (emitObservedTrace rest)).run = _
          rw [ih hagrees]
          simp
      | reveal index value =>
          obtain ⟨hvalue, hrest⟩ := hagrees
          simp [emitObservedTrace, revealQuery, simulateQ_bind,
            eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell, hvalue]
          change (fun x => (x.1, .reveal index value :: x.2)) <$>
              (simulateQ (eagerTraceImpl table) (emitObservedTrace rest)).run = _
          rw [ih hrest]
          simp

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_eagerTrace_liftProbComp
    (table : Index → Digest) (computation : ProbComp α) :
    (simulateQ (eagerTraceImpl table)
      (liftProbComp (Index := Index) computation)).run =
        (fun result => (result, ([] : ActionTrace Index))) <$> computation := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp [liftProbComp]
  | query_bind n next ih =>
      rw [liftProbComp, simulateQ_query_bind, simulateQ_bind]
      simp only [uniformForwardImpl, uniformQuery]
      simp [eagerTraceImpl, eagerImpl, traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell]
      apply bind_congr
      intro output
      change (simulateQ (eagerTraceImpl table)
        (liftProbComp (next output))).run = _
      exact ih output

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_eagerTrace_reveal_then_liftProbComp
    (table : Index → Digest) (index : Index)
    (computation : Digest → ProbComp α) (finish : Digest → α → β) :
    (simulateQ (eagerTraceImpl table) (do
      let value ← revealQuery index
      let output ← liftProbComp (computation value)
      pure (finish value output))).run =
      (fun output =>
        (finish (table index) output, [.reveal index (table index)])) <$>
          computation (table index) := by
  rw [simulateQ_bind, WriterT.run_bind', simulate_eagerTrace_revealQuery]
  simp only [pure_bind]
  rw [simulateQ_bind, WriterT.run_bind',
    simulate_eagerTrace_liftProbComp]
  simp [map_eq_bind_pure_comp, bind_assoc]

theorem evalDist_uniformTable_simulate_eagerTrace_reveal_continuation
    (index : Index)
    (continuation : (Index → Digest) →
      (Digest × ActionTrace Index) → ProbComp α) :
    𝒟[do
      let table ← $ᵗ (Index → Digest)
      let result ← (simulateQ (eagerTraceImpl table) (revealQuery index)).run
      continuation table result] =
    𝒟[do
      let value ← $ᵗ Digest
      let base ← $ᵗ (Index → Digest)
      let table := Function.update base index value
      continuation table (value, [.reveal index value])] := by
  calc
    𝒟[do
      let table ← $ᵗ (Index → Digest)
      let result ← (simulateQ (eagerTraceImpl table) (revealQuery index)).run
      continuation table result] =
        𝒟[do
          let table ← $ᵗ (Index → Digest)
          continuation table (table index, [.reveal index (table index)])] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      rw [simulate_eagerTrace_revealQuery]
      simp
    _ = _ := evalDist_uniformTable_bind_coordinate_continuation index
      (fun table value => continuation table (value, [.reveal index value]))

theorem evalDist_bind_congr_of_support
    (head : ProbComp α) (left right : α → ProbComp β)
    (heq : ∀ result ∈ support head, 𝒟[left result] = 𝒟[right result]) :
    𝒟[head >>= left] = 𝒟[head >>= right] := by
  refine evalDist_ext fun output => ?_
  refine probOutput_bind_congr fun result hresult => ?_
  rw [probOutput_def, probOutput_def, heq result hresult]

theorem eagerExperiment_emitObservedTrace_eq
    (traceGenerator : ProbComp (ActionTrace Index))
    (hagrees : ∀ table trace,
      (table, trace) ∈ support
        (Prod.mk <$> ($ᵗ (Index → Digest)) <*> traceGenerator) →
      TraceAgrees table trace) :
    𝒟[eagerExperiment
      (do
        let trace ← liftProbComp (Index := Index) traceGenerator
        emitObservedTrace trace)] =
      𝒟[do
        let table ← $ᵗ (Index → Digest)
        let trace ← traceGenerator
        pure (table, ((), trace))] := by
  unfold eagerExperiment
  simp only [simulateQ_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro table
  rw [WriterT.run_bind']
  rw [simulate_eagerTrace_liftProbComp table traceGenerator]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  change 𝒟[traceGenerator >>= fun trace =>
      (simulateQ (eagerTraceImpl table) (emitObservedTrace trace)).run >>= fun result =>
        pure (table, result)] =
    𝒟[traceGenerator >>= fun trace => pure (table, ((), trace))]
  apply evalDist_bind_congr_of_support
  intro trace htrace
  rw [simulate_eagerTrace_emitObservedTrace table trace]
  · simp
  · apply hagrees table trace
    rw [support_seq_map_prod_mk]
    exact ⟨by simp, htrace⟩

omit [Fintype Index] [DecidableEq Index] in
theorem emitProbes_isProbeQueryBoundP
    (probes : List (Index × Digest)) :
    (emitProbes probes).IsQueryBoundP IsProbeQuery probes.length := by
  induction probes with
  | nil => trivial
  | cons probe probes ih =>
      rw [emitProbes, probeQuery, OracleComp.isQueryBoundP_query_bind_iff]
      constructor
      · simp [IsProbeQuery]
      · intro output
        simpa [IsProbeQuery] using ih

omit [Fintype Index] [DecidableEq Index] in
theorem emitReveals_isProbeQueryBoundP
    (reveals : List Index) (fuel : Nat) :
    (emitReveals reveals).IsQueryBoundP IsProbeQuery fuel := by
  induction reveals with
  | nil => trivial
  | cons index reveals ih =>
      rw [emitReveals, revealQuery, OracleComp.isQueryBoundP_query_bind_iff]
      constructor
      · simp [IsProbeQuery]
      · intro value
        simpa [IsProbeQuery] using ih

omit [Fintype Index] [DecidableEq Index] in
theorem emitTranscript_isProbeQueryBoundP
    (probes : List (Index × Digest)) (reveals : List Index) :
    (emitTranscript probes reveals).IsQueryBoundP IsProbeQuery probes.length := by
  unfold emitTranscript
  simpa using OracleComp.isQueryBoundP_bind (m := 0)
    (emitProbes_isProbeQueryBoundP probes)
    (fun _result _hresult => emitReveals_isProbeQueryBoundP reveals 0)

def installProbe
    (state : AdaptiveRevealMonitor.State Index)
    (probe : Index × Digest) : AdaptiveRevealMonitor.State Index :=
  state.addPending probe.1 probe.2

def installProbes
    (state : AdaptiveRevealMonitor.State Index)
    (probes : List (Index × Digest)) : AdaptiveRevealMonitor.State Index :=
  probes.foldl installProbe state

omit [Fintype Index] in
theorem installProbes_revealed
    (state : AdaptiveRevealMonitor.State Index)
    (probes : List (Index × Digest)) :
    (installProbes state probes).revealed = state.revealed := by
  induction probes generalizing state with
  | nil => rfl
  | cons probe probes ih =>
      simpa [installProbes, List.foldl_cons, installProbe,
        AdaptiveRevealMonitor.State.addPending] using
        ih (state.addPending probe.1 probe.2)

omit [Fintype Index] in
theorem pending_installProbes_mono
    (state : AdaptiveRevealMonitor.State Index)
    (probes : List (Index × Digest)) (index : Index) :
    state.pending index ⊆ (installProbes state probes).pending index := by
  induction probes generalizing state with
  | nil => exact fun _value hvalue => hvalue
  | cons probe probes ih =>
      apply Finset.Subset.trans _ (ih (installProbe state probe))
      intro value hvalue
      by_cases heq : probe.1 = index
      · subst index
        simpa [installProbe, AdaptiveRevealMonitor.State.addPending] using
          Finset.mem_insert_of_mem hvalue
      · simpa [installProbe, AdaptiveRevealMonitor.State.addPending,
          Function.update_of_ne (Ne.symm heq)] using hvalue

omit [Fintype Index] in
theorem mem_pending_installProbes_of_mem
    (state : AdaptiveRevealMonitor.State Index)
    (probes : List (Index × Digest)) (probe : Index × Digest)
    (hprobe : probe ∈ probes) :
    probe.2 ∈ (installProbes state probes).pending probe.1 := by
  induction probes generalizing state with
  | nil => simp at hprobe
  | cons first probes ih =>
      rw [List.mem_cons] at hprobe
      rcases hprobe with heq | htail
      · subst first
        apply pending_installProbes_mono (installProbe state probe) probes
        simp [installProbe, AdaptiveRevealMonitor.State.addPending]
      · simpa [installProbes, List.foldl_cons] using
          ih (installProbe state first) htail

theorem runObserved_probeTrace
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (probes : List (Index × Digest))
    (hhidden : ∀ probe ∈ probes, state.revealed probe.1 = none) :
    runObserved table state (probes.map fun probe =>
      ObservedAction.probe probe.1 probe.2) =
      tableHits (installProbes state probes) table := by
  induction probes generalizing state with
  | nil => rfl
  | cons probe probes ih =>
      simp only [List.map_cons, runObserved]
      rw [hhidden probe (by simp)]
      apply ih (state.addPending probe.1 probe.2)
      intro candidate hcandidate
      have hcandidateHidden := hhidden candidate (by simp [hcandidate])
      simpa [AdaptiveRevealMonitor.State.addPending] using hcandidateHidden

theorem runObserved_probeTrace_eq_true_of_mem
    (table : Index → Digest) (probes : List (Index × Digest))
    (probe : Index × Digest) (hprobe : probe ∈ probes)
    (hhit : table probe.1 = probe.2) :
    runObserved table AdaptiveRevealMonitor.State.empty
      (probes.map fun candidate =>
        ObservedAction.probe candidate.1 candidate.2) = true := by
  rw [runObserved_probeTrace table AdaptiveRevealMonitor.State.empty probes
    (by simp [AdaptiveRevealMonitor.State.empty])]
  simp only [tableHits, decide_eq_true_eq]
  refine ⟨probe.1, ?_⟩
  rw [hhit]
  exact mem_pending_installProbes_of_mem AdaptiveRevealMonitor.State.empty
    probes probe hprobe

def strategyProbes
    (queries : Nat) (strategy : List Bool → Index × Digest) :
    List (Index × Digest) :=
  (List.range queries).map fun round =>
    strategy (List.replicate round false)

omit [Fintype Index] [DecidableEq Index] in
@[simp]
theorem strategyProbes_length
    (queries : Nat) (strategy : List Bool → Index × Digest) :
    (strategyProbes queries strategy).length = queries := by
  simp [strategyProbes]

theorem runObserved_strategyProbes_eq_true_of_readMany
    (table : Index → Digest) (queries : Nat)
    (strategy : List Bool → Index × Digest)
    (hhit : IndexedHiddenValue.readMany table queries strategy = true) :
    runObserved table AdaptiveRevealMonitor.State.empty
      ((strategyProbes queries strategy).map fun probe =>
        ObservedAction.probe probe.1 probe.2) = true := by
  rw [IndexedHiddenValue.readMany_true_iff] at hhit
  obtain ⟨round, hround, hhit⟩ := hhit
  apply runObserved_probeTrace_eq_true_of_mem table
    (strategyProbes queries strategy)
    (strategy (List.replicate round false))
  · exact List.mem_map.mpr ⟨round, List.mem_range.mpr hround, rfl⟩
  · exact hhit

def compileStrategyProbes
    (queries : Nat)
    (transcriptProgram : OracleComp (World Index)
      (List Bool → Index × Digest)) :
    OracleComp (World Index) (List Bool → Index × Digest) := do
  let strategy ← transcriptProgram
  emitProbes (strategyProbes queries strategy)
  pure strategy

omit [Fintype Index] [DecidableEq Index] in
theorem compileStrategyProbes_isProbeQueryBoundP
    (queries : Nat)
    (transcriptProgram : OracleComp (World Index)
      (List Bool → Index × Digest))
    (htranscript : transcriptProgram.IsQueryBoundP IsProbeQuery 0) :
    (compileStrategyProbes queries transcriptProgram).IsQueryBoundP
      IsProbeQuery queries := by
  unfold compileStrategyProbes
  have hcontinuation (strategy : List Bool → Index × Digest) :
      (do
        emitProbes (strategyProbes queries strategy)
        pure strategy).IsQueryBoundP IsProbeQuery queries := by
    have hemit := emitProbes_isProbeQueryBoundP
      (strategyProbes queries strategy)
    rw [strategyProbes_length] at hemit
    simpa using OracleComp.isQueryBoundP_bind (m := 0) hemit
      (fun _unit _hunit => OracleComp.isQueryBoundP_pure
        (p := IsProbeQuery) strategy 0)
  simpa using OracleComp.isQueryBoundP_bind (n := 0) (m := queries)
    htranscript (fun strategy _hstrategy => hcontinuation strategy)

omit [Fintype Index] [DecidableEq Index] in
theorem probeQuery_isQueryBoundP
    (index : Index) (target : Digest) :
    (probeQuery index target).IsQueryBoundP IsSpecialQuery 1 := by
  rw [probeQuery, OracleComp.isQueryBoundP_query_iff]
  simp [IsSpecialQuery]

omit [Fintype Index] [DecidableEq Index] in
theorem revealQuery_isQueryBoundP (index : Index) :
    (revealQuery index).IsQueryBoundP IsSpecialQuery 1 := by
  rw [revealQuery, OracleComp.isQueryBoundP_query_iff]
  simp [IsSpecialQuery]

omit [Fintype Index] [DecidableEq Index] in
theorem uniformQuery_isQueryBoundP (n steps : Nat) :
    (uniformQuery (Index := Index) n).IsQueryBoundP IsSpecialQuery steps := by
  rw [uniformQuery, OracleComp.isQueryBoundP_query_iff]
  simp [IsSpecialQuery]

def ContinuationBound (steps : Nat) :
    AdaptiveRevealMonitor.ControllerAction
      (OracleComp (World Index) α) Index → Prop
  | .stop => True
  | .skip next => next.IsQueryBoundP IsSpecialQuery steps
  | .probe _ _ next =>
      ∀ answer, (next answer).IsQueryBoundP IsSpecialQuery steps
  | .reveal _ next =>
      ∀ value, (next value).IsQueryBoundP IsSpecialQuery steps

omit [Fintype Index] [DecidableEq Index] in
theorem controller_continuationBound
    (computation : OracleComp (World Index) α) (steps : Nat)
    (hbound : computation.IsQueryBoundP IsSpecialQuery steps.succ)
    (action : AdaptiveRevealMonitor.ControllerAction
      (OracleComp (World Index) α) Index)
    (hmem : action ∈ support (controller computation)) :
    ContinuationBound steps action := by
  induction computation using OracleComp.inductionOn with
  | pure result =>
      simp [controller] at hmem
      subst action
      trivial
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      simp only [controller, OracleComp.construct_query_bind] at hmem
      cases input with
      | uniform n =>
          rw [mem_support_bind_iff] at hmem
          obtain ⟨output, _houtput, hcontinue⟩ := hmem
          exact ih output (by simpa [IsSpecialQuery] using hbound.2 output) hcontinue
      | probe index target =>
          simp only [support_pure, Set.mem_singleton_iff] at hmem
          subst action
          intro answer
          simpa [ContinuationBound, IsSpecialQuery] using hbound.2 ()
      | reveal index =>
          simp only [support_pure, Set.mem_singleton_iff] at hmem
          subst action
          intro value
          simpa [ContinuationBound, IsSpecialQuery] using hbound.2 value

omit [Fintype Index] [DecidableEq Index] in
theorem controller_eq_stop_of_zero_bound
    (computation : OracleComp (World Index) α)
    (hbound : computation.IsQueryBoundP IsSpecialQuery 0)
    (action : AdaptiveRevealMonitor.ControllerAction
      (OracleComp (World Index) α) Index)
    (hmem : action ∈ support (controller computation)) :
    action = .stop := by
  induction computation using OracleComp.inductionOn with
  | pure result =>
      simpa [controller] using hmem
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      simp only [controller, OracleComp.construct_query_bind] at hmem
      cases input with
      | uniform n =>
          rw [mem_support_bind_iff] at hmem
          obtain ⟨output, _houtput, hcontinue⟩ := hmem
          exact ih output (by simpa [IsSpecialQuery] using hbound.2 output) hcontinue
      | probe index target =>
          exfalso
          simpa [IsSpecialQuery] using hbound.1
      | reveal index =>
          exfalso
          simpa [IsSpecialQuery] using hbound.1

noncomputable def run
    (steps probes : Nat) (computation : OracleComp (World Index) α) :
    ProbComp Bool :=
  AdaptiveRevealMonitor.run controller AdaptiveRevealMonitor.State.empty
    steps probes computation

theorem run_true_probability_le
    (steps probes : Nat) (computation : OracleComp (World Index) α) :
    Pr[(fun hit : Bool => hit = true) | run steps probes computation] ≤
      (probes : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  exact AdaptiveRevealMonitor.run_empty_true_probability_le controller
    steps probes computation

end XmssSecurity.RevealProbeOracleSimulation
