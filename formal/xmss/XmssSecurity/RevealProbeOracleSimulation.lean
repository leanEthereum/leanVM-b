import XmssSecurity.AdaptiveRevealMonitor

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

noncomputable instance : DecidablePred (IsSpecialQuery (Index := Index)) :=
  fun input => match input with
  | .uniform _ => isFalse (by simp [IsSpecialQuery])
  | .probe _ _ => isTrue (by simp [IsSpecialQuery])
  | .reveal _ => isTrue (by simp [IsSpecialQuery])

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

noncomputable local instance sampleableTable :
    SampleableType (Index → Digest) :=
  SampleableType.ofFintype (Index → Digest)

noncomputable def eagerExperiment
    (computation : OracleComp (World Index) α) :
    ProbComp ((Index → Digest) × (α × ActionTrace Index)) := do
  let table ← $ᵗ (Index → Digest)
  let result ← (simulateQ (eagerTraceImpl table) computation).run
  return (table, result)

def EagerHit (result : (Index → Digest) × (α × ActionTrace Index)) : Prop :=
  traceHits result.1 result.2.2 = true

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
