import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveSigner

/-!
# Private structural sample deferral

Private structural samples are moved to their first observable use. The base case below proves
that resolving one ensured position before a completed run is neutral when the run returns
immediately. Later lemmas lift the same invariant through queries and recursive resolution.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem finishResolvedRunIsNone_some_eq_finalize
    (result : ResolvedRunResult α)
    (hcompletable : DeferredCompletable result.table result.context) :
    finishResolvedRunIsNone (some result) =
      Option.isNone <$>
        finalizeResolvedCoordinates result.context.state.coordinates.toList
          result.context result.table := by
  simp only [finishResolvedRunIsNone, finishResolvedRun, hcompletable, ↓reduceIte,
    map_bind]
  apply bind_congr
  intro finalized
  cases finalized <;> rfl

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_then_finish_isNone
    (position : Position) (context : DeferredContext)
    (table : OtsSecretIndex → HashOutput) (fuel : Nat) (value : α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : Coordinate.position position ∈ context.state.ensured) :
    evalDist (do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => pure true
      | some resolved =>
          finishResolvedRunIsNone
            (some ⟨resolved.toDeferredContext, fuel, value, table⟩)) =
      evalDist (finishResolvedRunIsNone
        (some ⟨context, fuel, value, table⟩)) := by
  let coordinates := context.state.coordinates.toList
  have hmem : Coordinate.position position ∈ coordinates := by
    simp only [coordinates, Finset.mem_toList, LazyRevealProbe.State.coordinates,
      Finset.mem_union]
    exact Or.inl hensured
  have hbase := evalDist_resolveDeferredPositionValue_then_finalize position coordinates
    context table hmem (fun output hvalue =>
      ⟨hvalid.1 position output hvalue,
        hvalid.2 (.position position) output hvalue⟩)
  calc
    _ = evalDist (Option.isNone <$> (do
        let resolved ← resolveDeferredPositionValue position context
        match resolved with
        | none => (pure none : ProbComp (Option DeferredContext))
        | some resolved =>
            finalizeResolvedCoordinates coordinates resolved.toDeferredContext table)) := by
      rw [map_bind]
      apply evalDist_bind_congr
      intro resolved hsupport
      cases resolved with
      | none => rfl
      | some resolved =>
          have hresolvedCompletable := hcompletable.of_resolveDeferredPositionValue hvalid
            position resolved hsupport
          let result : ResolvedRunResult α :=
            ⟨resolved.toDeferredContext, fuel, value, table⟩
          have hfinish := finishResolvedRunIsNone_some_eq_finalize result
            hresolvedCompletable
          simp only
          rw [hfinish]
          have hstate := resolveDeferredPositionValue_state_eq_clearPending position context
            resolved hsupport
          have hcoordinates : resolved.state.coordinates = context.state.coordinates := by
            rw [hstate]
            exact coordinates_clearPending_of_mem_ensured context.state (.position position)
              hensured
          congr 3
          exact congrArg Finset.toList hcoordinates
    _ = evalDist (Option.isNone <$>
        finalizeResolvedCoordinates coordinates context table) := by
      rw [evalDist_map, evalDist_map]
      exact congrArg (Functor.map Option.isNone) hbase
    _ = _ := by
      rw [finishResolvedRunIsNone_some_eq_finalize _ hcompletable]

noncomputable def runResolvedFinishIsNone
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) : ProbComp Bool :=
  runResolvedFromTable context fuel table computation >>= finishResolvedRunIsNone

def DeferredResolution.ensure (result : DeferredResolution) (coordinate : Coordinate) :
    DeferredResolution :=
  ⟨{ result.toDeferredContext with state := result.state.ensure coordinate }, result.output⟩

def DeferredResolution.publish (result : DeferredResolution) (coordinate : Coordinate) :
    DeferredResolution :=
  ⟨{ result.toDeferredContext with state := result.state.publish coordinate }, result.output⟩

def DeferredResolution.addPending (result : DeferredResolution) (coordinate : Coordinate)
    (candidate : Digest) : DeferredResolution :=
  ⟨{ result.toDeferredContext with
      state := result.state.addPending coordinate candidate }, result.output⟩

@[simp] theorem values_ensure
    (state : LazyRevealProbe.State Coordinate) (ensured coordinate : Coordinate) :
    (state.ensure ensured).values coordinate = state.values coordinate := rfl

@[simp] theorem hitAt_ensure
    (state : LazyRevealProbe.State Coordinate) (ensured coordinate : Coordinate)
    (output : HashOutput) :
    (state.ensure ensured).hitAt coordinate output = state.hitAt coordinate output := rfl

@[simp] theorem values_publish
    (state : LazyRevealProbe.State Coordinate) (published coordinate : Coordinate) :
    (state.publish published).values coordinate = state.values coordinate := rfl

@[simp] theorem hitAt_publish
    (state : LazyRevealProbe.State Coordinate) (published coordinate : Coordinate)
    (output : HashOutput) :
    (state.publish published).hitAt coordinate output = state.hitAt coordinate output := rfl

@[simp] theorem values_addPending
    (state : LazyRevealProbe.State Coordinate) (added coordinate : Coordinate)
    (candidate : Digest) :
    (state.addPending added candidate).values coordinate = state.values coordinate := rfl

theorem hitAt_addPending_of_ne
    (state : LazyRevealProbe.State Coordinate) (added coordinate : Coordinate)
    (candidate : Digest) (output : HashOutput) (hne : added ≠ coordinate) :
    (state.addPending added candidate).hitAt coordinate output =
      state.hitAt coordinate output := by
  have hne' : coordinate ≠ added := Ne.symm hne
  simp [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt,
    LazyRevealProbe.State.addPending, hne']

theorem resolveDeferredPositionValue_ensure
    (position : Position) (context : DeferredContext) (coordinate : Coordinate) :
    resolveDeferredPositionValue position
        { context with state := context.state.ensure coordinate } =
      (fun result => result.map fun resolved => resolved.ensure coordinate) <$>
        resolveDeferredPositionValue position context := by
  unfold resolveDeferredPositionValue
  cases hstate : context.state.values (.position position) with
  | some output =>
      by_cases hhit : context.state.hitAt (.position position) output
      · simp [hstate, hhit]
      · simp [hstate, hhit, DeferredResolution.ensure, clearPending_ensure_comm]
  | none =>
      cases hvalue : context.values position with
      | some output =>
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hstate, hhit]
          · simp [hstate, hhit, DeferredResolution.ensure,
              clearPending_ensure_comm]
      | none =>
          simp only [values_ensure, hstate]
          rw [map_bind]
          apply bind_congr
          intro output
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit]
          · simp [hhit, DeferredResolution.ensure, clearPending_ensure_comm]

theorem resolveDeferredPositionValue_publish
    (position : Position) (context : DeferredContext) (coordinate : Coordinate) :
    resolveDeferredPositionValue position
        { context with state := context.state.publish coordinate } =
      (fun result => result.map fun resolved => resolved.publish coordinate) <$>
        resolveDeferredPositionValue position context := by
  unfold resolveDeferredPositionValue
  cases hstate : context.state.values (.position position) with
  | some output =>
      by_cases hhit : context.state.hitAt (.position position) output
      · simp [hstate, hhit]
      · simp [hstate, hhit, DeferredResolution.publish, clearPending_publish_comm]
  | none =>
      cases hvalue : context.values position with
      | some output =>
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hstate, hhit]
          · simp [hstate, hhit, DeferredResolution.publish, clearPending_publish_comm]
      | none =>
          simp only [values_publish, hstate]
          rw [map_bind]
          apply bind_congr
          intro output
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit]
          · simp [hhit, DeferredResolution.publish, clearPending_publish_comm]

theorem resolveDeferredPositionValue_addPending_of_ne
    (position : Position) (context : DeferredContext) (coordinate : Coordinate)
    (candidate : Digest) (hne : coordinate ≠ .position position) :
    resolveDeferredPositionValue position
        { context with state := context.state.addPending coordinate candidate } =
      (fun result => result.map fun resolved => resolved.addPending coordinate candidate) <$>
        resolveDeferredPositionValue position context := by
  unfold resolveDeferredPositionValue
  cases hstate : context.state.values (.position position) with
  | some output =>
      by_cases hhit : context.state.hitAt (.position position) output
      · simp [hstate, hhit, hitAt_addPending_of_ne _ _ _ _ _ hne]
      · simp [hstate, hhit, hitAt_addPending_of_ne _ _ _ _ _ hne,
          DeferredResolution.addPending, clearPending_addPending_comm_of_ne _ _ _ _ hne]
  | none =>
      cases hvalue : context.values position with
      | some output =>
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hstate, hhit, hitAt_addPending_of_ne _ _ _ _ _ hne]
          · simp [hstate, hhit, hitAt_addPending_of_ne _ _ _ _ _ hne,
              DeferredResolution.addPending, clearPending_addPending_comm_of_ne _ _ _ _ hne]
      | none =>
          simp only [values_addPending, hstate]
          rw [map_bind]
          apply bind_congr
          intro output
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit, hitAt_addPending_of_ne _ _ _ _ _ hne]
          · simp [hhit, hitAt_addPending_of_ne _ _ _ _ _ hne,
              DeferredResolution.addPending, clearPending_addPending_comm_of_ne _ _ _ _ hne]

theorem DeferredContext.Valid.addPending_of_completable
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hvalid : context.Valid) (coordinate : Coordinate) (candidate : Digest)
    (hcompletable : DeferredCompletable table
      { context with state := context.state.addPending coordinate candidate }) :
    ({ context with state := context.state.addPending coordinate candidate } :
      DeferredContext).Valid := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  constructor
  · exact hvalid.1
  · intro other output hvalue hhit
    have hvalueOriginal : context.state.values other = some output := hvalue
    have hcompletionValue : completion other = output :=
      hcompletion.1 other output hvalueOriginal
    have hmember : (other, truncateHash output) ∈
        (context.state.addPending coordinate candidate).pending :=
      (LazyRevealProbe.State.mem_pendingAt_iff
        (context.state.addPending coordinate candidate) other (truncateHash output)).1 hhit
    exact hcompletion.2.2.1 other (truncateHash output) hmember (by
      rw [hcompletionValue])

theorem startTableAgrees_of_deferredCompletable
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) :
    StartTableAgrees context.state table := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  intro index output hvalue
  exact (hcompletion.1 index.coordinate output hvalue).symm.trans
    (hcompletion.2.2.2 index)

theorem evalDist_runResolvedFinishIsNone_eq_true_of_not_completable
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (runResolvedFromTable context fuel table computation >>=
        finishResolvedRunIsNone) = evalDist (pure true : ProbComp Bool) := by
  calc
    _ = evalDist (runResolvedFromTable context fuel table computation >>= fun _ =>
          pure true) := by
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => simp [finishResolvedRunIsNone, finishResolvedRun]
      | some result =>
          have hcore := resolvedCore_of_mem_runResolvedFromTable computation context fuel
            table result hconsistent hstarts hresult
          have hstillDoomed := not_deferredCompletable_of_mem_runResolvedFromTable
            computation context fuel table result hconsistent hstarts hresult hdoomed
          simp [finishResolvedRunIsNone, finishResolvedRun, hcore.1, hstillDoomed]
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (runResolvedFromTable context fuel table computation) (by simp [runResolvedFromTable])
      (pure true)

theorem clearPending_addPending_clearPending_self
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate)
    (candidate : Digest) :
    ((state.clearPending coordinate).addPending coordinate candidate).clearPending coordinate =
      (state.addPending coordinate candidate).clearPending coordinate := by
  rcases state with ⟨pending, values, revealed, ensured⟩
  simp only [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.addPending]
  congr 1
  apply Finset.ext
  intro entry
  by_cases haway : entry.1 ≠ coordinate
  · have hpair : entry ≠ (coordinate, candidate) := by
      intro heq
      subst entry
      exact haway rfl
    simp [LazyRevealProbe.State.pendingAway, haway, hpair]
  · simp [LazyRevealProbe.State.pendingAway, haway]

theorem resolveDeferredPositionValue_then_addPending_self_resolve
    (position : Position) (context : DeferredContext) (candidate : Digest) :
    (do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => (pure none : ProbComp (Option DeferredResolution))
      | some resolved =>
          resolveDeferredPositionValue position
            { resolved.toDeferredContext with
              state := resolved.state.addPending (.position position) candidate }) =
    resolveDeferredPositionValue position
      { context with
        state := context.state.addPending (.position position) candidate } := by
  unfold resolveDeferredPositionValue
  cases hstate : context.state.values (.position position) with
  | some output =>
      by_cases holdHit : context.state.hitAt (.position position) output
      · have hnewHit :
            (context.state.addPending (.position position) candidate).hitAt
              (.position position) output :=
          (hitAt_addPending_self_iff context.state (.position position) candidate output).2
            (Or.inl holdHit)
        simp [hstate, holdHit, hnewHit]
      · by_cases hcandidate : truncateHash output = candidate
        · have hnewHit :
              (context.state.addPending (.position position) candidate).hitAt
                (.position position) output :=
            (hitAt_addPending_self_iff context.state (.position position) candidate output).2
              (Or.inr hcandidate)
          simp [hstate, holdHit, hnewHit, hitAt_addPending_self_iff, hcandidate]
        · have hnewHit :
              ¬(context.state.addPending (.position position) candidate).hitAt
                (.position position) output := by
            rw [hitAt_addPending_self_iff]
            exact not_or_intro holdHit hcandidate
          simp [hstate, holdHit, hnewHit, hitAt_addPending_self_iff, hcandidate,
            clearPending_addPending_clearPending_self,
            DeferredStructuralValues.install, not_hitAt_clearPending_self]
  | none =>
      cases hvalue : context.values position with
      | some output =>
          by_cases holdHit : context.state.hitAt (.position position) output
          · have hnewHit :
                (context.state.addPending (.position position) candidate).hitAt
                  (.position position) output :=
              (hitAt_addPending_self_iff context.state (.position position) candidate output).2
                (Or.inl holdHit)
            simp [hstate, holdHit, hnewHit]
          · by_cases hcandidate : truncateHash output = candidate
            · have hnewHit :
                  (context.state.addPending (.position position) candidate).hitAt
                    (.position position) output :=
                (hitAt_addPending_self_iff context.state (.position position) candidate output).2
                  (Or.inr hcandidate)
              simp [hstate, hvalue, holdHit, hnewHit, hitAt_addPending_self_iff,
                hcandidate]
            · have hnewHit :
                  ¬(context.state.addPending (.position position) candidate).hitAt
                    (.position position) output := by
                rw [hitAt_addPending_self_iff]
                exact not_or_intro holdHit hcandidate
              simp [hstate, hvalue, holdHit, hnewHit, hitAt_addPending_self_iff,
                hcandidate, clearPending_addPending_clearPending_self,
                not_hitAt_clearPending_self]
      | none =>
          simp only [values_addPending, hstate, bind_assoc]
          apply bind_congr
          intro output
          by_cases holdHit : context.state.hitAt (.position position) output
          · have hnewHit :
                (context.state.addPending (.position position) candidate).hitAt
                  (.position position) output :=
              (hitAt_addPending_self_iff context.state (.position position) candidate output).2
                (Or.inl holdHit)
            simp [holdHit, hnewHit]
          · by_cases hcandidate : truncateHash output = candidate
            · have hnewHit :
                  (context.state.addPending (.position position) candidate).hitAt
                    (.position position) output :=
                (hitAt_addPending_self_iff context.state (.position position) candidate output).2
                  (Or.inr hcandidate)
              simp [hstate, holdHit, hnewHit, hitAt_addPending_self_iff,
                hcandidate, DeferredStructuralValues.install,
                not_hitAt_clearPending_self]
            · have hnewHit :
                  ¬(context.state.addPending (.position position) candidate).hitAt
                    (.position position) output := by
                rw [hitAt_addPending_self_iff]
                exact not_or_intro holdHit hcandidate
              simp [hstate, holdHit, hnewHit, hitAt_addPending_self_iff, hcandidate,
                clearPending_addPending_clearPending_self,
                DeferredStructuralValues.install, not_hitAt_clearPending_self]

theorem evalDist_resolveDeferredPositionValue_then_run_eq_true_of_not_completable
    (position : Position) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedFromTable resolved.toDeferredContext fuel table computation >>=
            finishResolvedRunIsNone) = evalDist (pure true : ProbComp Bool) := by
  calc
    _ = evalDist (resolveDeferredPositionValue position context >>= fun _ => pure true) := by
      apply evalDist_bind_congr
      intro resolved hresolved
      cases resolved with
      | none => rfl
      | some resolved =>
          have hresolvedNotCompletable :
              ¬DeferredCompletable table resolved.toDeferredContext := by
            intro hresolvedCompletable
            obtain ⟨completion, hcompletion⟩ := hresolvedCompletable
            have hback :=
              (deferredCompletion_resolveDeferredPositionValue_iff position resolved
                hconsistent hresolved completion).mp hcompletion
            exact hdoomed ⟨completion, hback.1⟩
          exact evalDist_runResolvedFinishIsNone_eq_true_of_not_completable
            resolved.toDeferredContext fuel table computation
            (hconsistent.of_resolveDeferredPositionValue position resolved hresolved)
            (hstarts.of_state_values_eq
              (resolveDeferredPositionValue_preserves_state_values position context resolved
                hresolved))
            hresolvedNotCompletable
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (resolveDeferredPositionValue position context) (by
        simp [resolveDeferredPositionValue, LazyRevealProbe.sampleHashOutput])
      (pure true)

end SphincsSecurity.Concrete.OtsProbeSimulation
