import SphincsSecurity.Proof.RetainedObservation

namespace SphincsSecurity.Concrete.AdaptiveHiddenLabels

open _root_.OracleComp OracleSpec UniformTableCompletion HiddenLabelObservation RetainedObservation
set_option backward.isDefEq.respectTransparency false

structure ObservationState (Coordinate Memory : Type) where
  allowed : Coordinate → Finset Digest
  memory : Memory

def HiddenSpec (Coordinate : Type) : OracleSpec (Probe Coordinate ⊕ Coordinate)
  | .inl _ => HashOutput
  | .inr _ => Digest

variable {Coordinate Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}

abbrev World (auxSpec : OracleSpec AuxIndex) (Coordinate : Type) := auxSpec + HiddenSpec Coordinate

structure Environment (auxSpec : OracleSpec AuxIndex) (Coordinate Memory : Type) where
  auxiliary : ObservationState Coordinate Memory → (input : auxSpec.Domain) → PMF (auxSpec.Range input × Memory)
  probeAnswer : Memory → Probe Coordinate → HashOutput → Memory
  probeStop : Memory → Probe Coordinate → Memory
  disclosure : Memory → Coordinate → Digest → Memory

variable [Fintype Coordinate] [DecidableEq Coordinate]

def probeState (environment : Environment auxSpec Coordinate Memory) (state : ObservationState Coordinate Memory)
    (probe : Probe Coordinate) (answer : HashOutput) : ObservationState Coordinate Memory :=
  ⟨probe.restrict state.allowed answer, environment.probeAnswer state.memory probe answer⟩

def stoppedState (environment : Environment auxSpec Coordinate Memory) (state : ObservationState Coordinate Memory)
    (probe : Probe Coordinate) : ObservationState Coordinate Memory :=
  ⟨state.allowed, environment.probeStop state.memory probe⟩

def disclosedState (environment : Environment auxSpec Coordinate Memory) (state : ObservationState Coordinate Memory)
    (coordinate : Coordinate) (value : Digest) : ObservationState Coordinate Memory :=
  ⟨discloseTableValue state.allowed coordinate value, environment.disclosure state.memory coordinate value⟩

noncomputable def observedImpl (environment : Environment auxSpec Coordinate Memory) (labels : Coordinate → Digest) :
    QueryImpl (World auxSpec Coordinate) (OptionT (StateT (ObservationState Coordinate Memory) SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun state =>
      (liftM (environment.auxiliary state input) : SPMF _) >>= fun result =>
        pure (some result.1, ⟨state.allowed, result.2⟩)
  | .inr (.inl probe) => OptionT.mk <| StateT.mk fun state =>
      observe (response labels probe) (pure (none, stoppedState environment state probe))
        (fun answer => pure (some answer, probeState environment state probe answer))
  | .inr (.inr coordinate) => OptionT.mk <| StateT.mk fun state =>
      pure (some (labels coordinate), disclosedState environment state coordinate (labels coordinate))

noncomputable def lazyImpl (environment : Environment auxSpec Coordinate Memory) :
    QueryImpl (World auxSpec Coordinate) (OptionT (StateT (ObservationState Coordinate Memory) SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun state =>
      (liftM (environment.auxiliary state input) : SPMF _) >>= fun result =>
        pure (some result.1, ⟨state.allowed, result.2⟩)
  | .inr (.inl probe) => OptionT.mk <| StateT.mk fun state =>
      observe (lazyResponse state.allowed probe) (pure (none, stoppedState environment state probe))
        (fun answer => pure (some answer, probeState environment state probe answer))
  | .inr (.inr coordinate) => OptionT.mk <| StateT.mk fun state =>
      cell (state.allowed coordinate) >>= fun value =>
        pure (some value, disclosedState environment state coordinate value)

noncomputable def runWith {Result : Type}
    (implementation : QueryImpl (World auxSpec Coordinate) (OptionT (StateT (ObservationState Coordinate Memory) SPMF)))
    (computation : OracleComp (World auxSpec Coordinate) Result) (state : ObservationState Coordinate Memory) :
    SPMF (Option Result × ObservationState Coordinate Memory) :=
  (OptionT.run (simulateQ implementation computation)).run state

noncomputable def observedRun {Result : Type} (environment : Environment auxSpec Coordinate Memory)
    (labels : Coordinate → Digest) (computation : OracleComp (World auxSpec Coordinate) Result)
    (state : ObservationState Coordinate Memory) := runWith (observedImpl environment labels) computation state

noncomputable def lazyRun {Result : Type} (environment : Environment auxSpec Coordinate Memory)
    (computation : OracleComp (World auxSpec Coordinate) Result) (state : ObservationState Coordinate Memory) :=
  runWith (lazyImpl environment) computation state

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem runWith_pure {Result : Type}
    (implementation : QueryImpl (World auxSpec Coordinate) (OptionT (StateT (ObservationState Coordinate Memory) SPMF)))
    (result : Result) (state : ObservationState Coordinate Memory) :
    runWith implementation (pure result) state = pure (some result, state) := by
  simp only [runWith, simulateQ_pure, OptionT.run_pure, StateT.run_pure]

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem runWith_query_bind {Result : Type}
    (implementation : QueryImpl (World auxSpec Coordinate) (OptionT (StateT (ObservationState Coordinate Memory) SPMF)))
    (input : (World auxSpec Coordinate).Domain)
    (next : (World auxSpec Coordinate).Range input → OracleComp (World auxSpec Coordinate) Result)
    (state : ObservationState Coordinate Memory) :
    runWith implementation (liftM ((World auxSpec Coordinate).query input) >>= next) state =
      ((implementation input).run.run state >>= fun result =>
        match result.1 with
        | none => pure (none, result.2)
        | some answer => runWith implementation (next answer) result.2) := by
  simp only [runWith, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (fun continuation => (implementation input).run.run state >>= continuation)
  funext result
  rcases result with ⟨answer, state⟩
  cases answer <;> rfl

def retain {Result : Type} (labels : Coordinate → Digest)
    (result : Option Result × ObservationState Coordinate Memory) :
    Option ((Coordinate → Digest) × Result) × ObservationState Coordinate Memory :=
  (result.1.map (fun value => (labels, value)), result.2)

noncomputable def finish {Result : Type} (result : Option Result × ObservationState Coordinate Memory) :
    SPMF (Option ((Coordinate → Digest) × Result) × ObservationState Coordinate Memory) :=
  match result.1 with
  | none => pure (none, result.2)
  | some value => complete result.2.allowed >>= fun labels => pure (some (labels, value), result.2)

theorem run_posterior {Result : Type} (environment : Environment auxSpec Coordinate Memory)
    (computation : OracleComp (World auxSpec Coordinate) Result) (state : ObservationState Coordinate Memory)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) :
    (complete state.allowed >>= fun labels => retain labels <$> observedRun environment labels computation state) =
      (lazyRun environment computation state >>= finish) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result =>
      simp only [observedRun, lazyRun, runWith_pure, map_pure, pure_bind, retain, Option.map_some, finish]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
            StateT.run_mk, bind_assoc, pure_bind, map_bind]
          rw [RetainedObservation.bind_comm]
          apply congrArg (fun continuation => (liftM (environment.auxiliary state input) : SPMF _) >>= continuation)
          funext answer
          exact ih answer.1 ⟨state.allowed, answer.2⟩ ha
      | inr input =>
          cases input with
          | inl probe =>
              simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                StateT.run_mk, observe_bind, pure_bind, map_observe, map_pure, retain, Option.map_none, finish]
              rw [bind_response_stopped state.allowed ha]
              apply observe_congr
              intro answer hanswer
              exact ih answer (probeState environment state probe answer)
                (lazyResponse_nonempty state.allowed probe answer hanswer)
          | inr coordinate =>
              simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                StateT.run_mk, pure_bind, bind_assoc]
              rw [bind_disclose state.allowed coordinate (fun value labels =>
                retain labels <$> runWith (observedImpl environment labels) (next value)
                  (disclosedState environment state coordinate value))]
              apply congrArg (fun continuation => cell (state.allowed coordinate) >>= continuation)
              funext value
              exact ih value (disclosedState environment state coordinate value)
                (discloseTableValue_nonempty state.allowed ha coordinate value)

theorem lazyRun_nonempty {Result : Type} (environment : Environment auxSpec Coordinate Memory)
    (computation : OracleComp (World auxSpec Coordinate) Result) (state : ObservationState Coordinate Memory)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty)
    (result : Option Result × ObservationState Coordinate Memory)
    (h : lazyRun environment computation state result ≠ 0) :
    ∀ coordinate, (result.2.allowed coordinate).Nonempty := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [lazyRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at h
      subst result
      exact ha
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [lazyRun, runWith_query_bind, lazyImpl, OptionT.run_mk, StateT.run_mk,
            bind_assoc, pure_bind] at h
          obtain ⟨answer, _, hnext⟩ := (bind_nonzero _ _ _).mp h
          exact ih answer.1 ⟨state.allowed, answer.2⟩ ha result hnext
      | inr input =>
          cases input with
          | inl probe =>
              simp only [lazyRun, runWith_query_bind, lazyImpl, OptionT.run_mk, StateT.run_mk,
                observe_bind, pure_bind] at h
              rcases (observe_nonzero _ _ _ _).mp h with ⟨_, hstop⟩ | ⟨answer, hanswer, hnext⟩
              · simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hstop
                subst result
                exact ha
              · exact ih answer (probeState environment state probe answer)
                  (lazyResponse_nonempty state.allowed probe answer hanswer) result hnext
          | inr coordinate =>
              simp only [lazyRun, runWith_query_bind, lazyImpl, OptionT.run_mk, StateT.run_mk,
                bind_assoc, pure_bind] at h
              obtain ⟨value, _, hnext⟩ := (bind_nonzero _ _ _).mp h
              exact ih value (disclosedState environment state coordinate value)
                (discloseTableValue_nonempty state.allowed ha coordinate value) result hnext

theorem lazyRun_preserves {Result : Type} (environment : Environment auxSpec Coordinate Memory)
    (invariant : ObservationState Coordinate Memory → Prop)
    (hstep : ∀ state, invariant state → ∀ input result,
      (lazyImpl environment input).run.run state result ≠ 0 → invariant result.2)
    (computation : OracleComp (World auxSpec Coordinate) Result) (state : ObservationState Coordinate Memory)
    (hinvariant : invariant state) (result : Option Result × ObservationState Coordinate Memory)
    (h : lazyRun environment computation state result ≠ 0) : invariant result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [lazyRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at h
      subst result
      exact hinvariant
  | query_bind input next ih =>
      simp only [lazyRun, runWith_query_bind] at h
      obtain ⟨⟨answer, updated⟩, hanswer, hnext⟩ := (bind_nonzero _ _ _).mp h
      have hupdated := hstep state hinvariant input (answer, updated) hanswer
      cases answer with
      | none =>
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hnext
          subst result
          exact hupdated
      | some answer => exact ih answer updated hupdated result hnext

def erase {Result : Type} (result : Option ((Coordinate → Digest) × Result) × ObservationState Coordinate Memory) :
    Option Result × ObservationState Coordinate Memory := (result.1.map Prod.snd, result.2)

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem erase_retain {Result : Type} (labels : Coordinate → Digest)
    (result : Option Result × ObservationState Coordinate Memory) : erase (retain labels result) = result := by
  rcases result with ⟨value, state⟩
  cases value <;> rfl

theorem erase_finish {Result : Type} (result : Option Result × ObservationState Coordinate Memory)
    (ha : ∀ coordinate, (result.2.allowed coordinate).Nonempty) : erase <$> finish result = pure result := by
  rcases result with ⟨value, state⟩
  cases value with
  | none => simp only [finish, map_pure, erase, Option.map_none]
  | some value =>
      simp only [finish, map_bind, map_pure, erase, Option.map_some]
      rw [complete_of_nonempty state.allowed ha, lift_bind_const]

theorem run_erasure {Result : Type} (environment : Environment auxSpec Coordinate Memory)
    (computation : OracleComp (World auxSpec Coordinate) Result) (state : ObservationState Coordinate Memory)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) :
    (complete state.allowed >>= fun labels => observedRun environment labels computation state) =
      lazyRun environment computation state := by
  have h := congrArg (fun law => erase <$> law) (run_posterior environment computation state ha)
  simp only [map_bind, ← comp_map, Function.comp_def, erase_retain, id_map'] at h
  calc
    _ = lazyRun environment computation state >>= fun result => erase <$> finish result := h
    _ = lazyRun environment computation state >>= pure := by
      apply RetainedObservation.bind_congr
      intro result hresult
      exact erase_finish result (lazyRun_nonempty environment computation state ha result hresult)
    _ = _ := bind_pure _

omit [Fintype Coordinate] in
theorem observedRun_bind_const {Result Other : Type} (environment : Environment auxSpec Coordinate Memory)
    (labels : Coordinate → Digest) (computation : OracleComp (World auxSpec Coordinate) Result)
    (state : ObservationState Coordinate Memory) (after : SPMF Other) :
    (observedRun environment labels computation state >>= fun _ => after) = after := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result => simp only [observedRun, runWith_pure, pure_bind]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [observedRun, runWith_query_bind, observedImpl, OptionT.run_mk, StateT.run_mk,
            bind_assoc, pure_bind]
          change ((liftM (environment.auxiliary state input) : SPMF _) >>= fun answer =>
            observedRun environment labels (next answer.1) ⟨state.allowed, answer.2⟩ >>= fun _ => after) = after
          simp only [ih, lift_bind_const]
      | inr input =>
          cases input with
          | inl probe =>
              simp only [observedRun, runWith_query_bind, observedImpl, OptionT.run_mk, StateT.run_mk,
                observe_bind, pure_bind]
              change observe (response labels probe) after (fun answer =>
                observedRun environment labels (next answer) (probeState environment state probe answer) >>= fun _ => after) = after
              simp only [ih, observe_const]
          | inr coordinate =>
              simp only [observedRun, runWith_query_bind, observedImpl, OptionT.run_mk, StateT.run_mk, pure_bind]
              exact ih (labels coordinate) (disclosedState environment state coordinate (labels coordinate))

theorem lazyRun_bind_const {Result Other : Type} (environment : Environment auxSpec Coordinate Memory)
    (computation : OracleComp (World auxSpec Coordinate) Result) (state : ObservationState Coordinate Memory)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) (after : SPMF Other) :
    (lazyRun environment computation state >>= fun _ => after) = after := by
  rw [← run_erasure environment computation state ha, bind_assoc]
  simp only [observedRun_bind_const, complete_of_nonempty state.allowed ha, lift_bind_const]

end SphincsSecurity.Concrete.AdaptiveHiddenLabels
