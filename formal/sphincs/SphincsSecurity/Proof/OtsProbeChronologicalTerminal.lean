import SphincsSecurity.Proof.OtsProbeResolvedSampling

/-!
# Chronological one-time terminal argument

Private chronological resolution may materialize a chain value without publishing it. The old `ChainState.ValidFor` invariant deliberately identifies materialization with publication, so it is not the right invariant for this game. This file tracks publication separately and uses deferred completions only for the one exact verifier probe supplied by terminal extraction.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def IsPublishQuery : (LazyRevealProbe.World Coordinate).Domain → Prop
  | .publish _ => True
  | _ => False

noncomputable instance : DecidablePred IsPublishQuery := fun query => by
  exact Classical.propDecidable _

def ResolvedNoPublish
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha) : Prop :=
  computation.IsQueryBoundP IsPublishQuery 0

theorem resolvedNoPublish_pure (value : alpha) :
    ResolvedNoPublish
      (pure value : OracleComp (LazyRevealProbe.World Coordinate) alpha) := by
  simp [ResolvedNoPublish]

theorem ResolvedNoPublish.bind
    {left : OracleComp (LazyRevealProbe.World Coordinate) alpha}
    {next : alpha → OracleComp (LazyRevealProbe.World Coordinate) beta}
    (hleft : ResolvedNoPublish left)
    (hnext : ∀ value ∈ support left, ResolvedNoPublish (next value)) :
    ResolvedNoPublish (left >>= next) := by
  simpa [ResolvedNoPublish] using
    OracleComp.isQueryBoundP_bind (n := 0) (m := 0) hleft hnext

theorem ResolvedNoPublish.bind_all
    {left : OracleComp (LazyRevealProbe.World Coordinate) alpha}
    {next : alpha → OracleComp (LazyRevealProbe.World Coordinate) beta}
    (hleft : ResolvedNoPublish left)
    (hnext : ∀ value, ResolvedNoPublish (next value)) :
    ResolvedNoPublish (left >>= next) :=
  hleft.bind fun value _ => hnext value

theorem resolvedNoPublish_simulateQ
    (impl : QueryImpl spec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))))
    (himpl : ∀ query cache, ResolvedNoPublish ((impl query).run cache))
    (computation : OracleComp spec alpha) (cache : SplitHashCache) :
    ResolvedNoPublish ((simulateQ impl computation).run cache) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp [simulateQ_pure, resolvedNoPublish_pure]
  | query_bind query next ih =>
      rw [simulateQ_query_bind, StateT.run_bind]
      exact (himpl query cache).bind_all fun result =>
        ih result.1 result.2

theorem resolvedNoPublish_sequenceFin {n : Nat}
    (computation : Fin n →
      OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (hcomponent : ∀ index, ResolvedNoPublish (computation index)) :
    ResolvedNoPublish (sequenceFin computation) := by
  induction n with
  | zero =>
      simpa [sequenceFin] using resolvedNoPublish_pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind_all fun head =>
        (ih (fun index : Fin n => computation index.succ)
          (fun index => hcomponent index.succ)).bind_all fun tail =>
            resolvedNoPublish_pure (Fin.cases head tail : Fin (n + 1) → alpha)

def NoPublish
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ cache, ResolvedNoPublish (computation.run cache)

theorem NoPublish.pure (value : alpha) :
    NoPublish (pure value : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro cache
  simpa using resolvedNoPublish_pure (value, cache)

theorem NoPublish.bind
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : NoPublish left) (hnext : ∀ value, NoPublish (next value)) :
    NoPublish (left >>= next) := by
  intro cache
  rw [StateT.run_bind]
  exact (hleft cache).bind_all fun result => hnext result.1 result.2

theorem noPublish_sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomponent : ∀ index, NoPublish (computation index)) :
    NoPublish (sequenceFin computation) := by
  induction n with
  | zero =>
      simpa [sequenceFin] using NoPublish.pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun head =>
        (ih (fun index : Fin n => computation index.succ)
          (fun index => hcomponent index.succ)).bind fun tail =>
            NoPublish.pure (Fin.cases head tail : Fin (n + 1) → alpha)

theorem noPublish_simulateQ
    (impl : QueryImpl spec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))))
    (himpl : ∀ query, NoPublish (impl query))
    (computation : OracleComp spec alpha) :
    NoPublish (simulateQ impl computation) := by
  intro cache
  exact resolvedNoPublish_simulateQ impl (fun query cache => himpl query cache)
    computation cache

theorem revealed_eq_of_mem_runResolvedFromTable_of_noPublish
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult alpha)
    (hnoPublish : ResolvedNoPublish computation)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table computation)) :
    result.context.state.revealed = context.state.revealed := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runResolvedFromTable] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      rfl
  | query_bind query next ih =>
      rw [ResolvedNoPublish, OracleComp.isQueryBoundP_query_bind_iff] at hnoPublish
      cases query with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel (by
            simpa [ResolvedNoPublish, IsPublishQuery] using hnoPublish.2 output) hrest
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel (by
            simpa [ResolvedNoPublish, IsPublishQuery] using hnoPublish.2 output) hrest
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind] at hresult
          exact (ih () { context with state := context.state.ensure coordinate } fuel
            (by simpa [ResolvedNoPublish, IsPublishQuery] using hnoPublish.2 ()) hresult).trans (by
              rfl)
      | probe coordinate candidate =>
          rw [runResolvedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              simp only at hresult
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · rw [if_pos hrevealed] at hresult
                exact ih () context remaining (by
                  simpa [ResolvedNoPublish, IsPublishQuery] using hnoPublish.2 ()) hresult
              · rw [if_neg hrevealed] at hresult
                exact (ih ()
                  { context with state := context.state.addPending coordinate candidate }
                  remaining (by
                    simpa [ResolvedNoPublish, IsPublishQuery] using hnoPublish.2 ())
                  hresult).trans (by rfl)
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel
            (by simpa [ResolvedNoPublish, IsPublishQuery] using
              hnoPublish.2 (context.state.values coordinate)) hresult
      | publish coordinate =>
          simp [IsPublishQuery] at hnoPublish
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind] at hresult
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [pure_bind] at hresult
              cases hresolved : resolveDeferredChainStart table
                  ⟨lay, tree, leafIdx, chainIdx⟩ context with
              | none => simp [hresolved] at hresult
              | some resolved =>
                  simp only [hresolved] at hresult
                  have hfinal := ih resolved.output
                    { state := context.state.materialize
                        (.chainStart lay tree leafIdx chainIdx) resolved.output
                      values := resolved.values }
                    fuel (by
                      simpa [ResolvedNoPublish, IsPublishQuery] using
                        hnoPublish.2 resolved.output) hresult
                  exact hfinal.trans (by rfl)

          | position position =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨resolved, _hresolved, hrest⟩ := hresult
              cases resolved with
              | none => simp at hrest
              | some resolved =>
                  have hfinal := ih resolved.output
                    { state := context.state.materialize (.position position) resolved.output
                      values := resolved.values }
                    fuel (by
                      simpa [ResolvedNoPublish, IsPublishQuery] using
                        hnoPublish.2 resolved.output) hrest
                  exact hfinal.trans (by rfl)

def RevealedChainAllowed (allowed : Coordinate → Prop)
    (state : LazyRevealProbe.State Coordinate) : Prop :=
  ∀ coordinate, IsChainCoordinate coordinate →
    coordinate ∈ state.revealed → allowed coordinate

theorem RevealedChainAllowed.mono
    {initial final : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate}
    (hallowed : RevealedChainAllowed initial state)
    (hle : ∀ coordinate, initial coordinate → final coordinate) :
    RevealedChainAllowed final state := by
  intro coordinate hchain hrevealed
  exact hle coordinate (hallowed coordinate hchain hrevealed)

def ResolvedPreservesChainPublication (allowed : Coordinate → Prop)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ context cache fuel table result completion,
    context.ValuesConsistent →
    StartTableAgrees context.state table →
    RevealedChainAllowed allowed context.state →
    some result ∈ support
      (runResolvedFromTable context fuel table (computation.run cache)) →
    DeferredCompletion table result.context completion →
    RevealedChainAllowed allowed result.context.state

theorem ResolvedPreservesChainPublication.pure
    (allowed : Coordinate → Prop) (value : alpha) :
    ResolvedPreservesChainPublication allowed
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro context cache fuel table result completion _ _ hallowed hresult _
  simp [runResolvedFromTable] at hresult
  subst result
  exact hallowed

theorem ResolvedPreservesChainPublication.bind
    {allowed : Coordinate → Prop}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : ResolvedPreservesChainPublication allowed left)
    (hnext : ∀ value, ResolvedPreservesChainPublication allowed (next value)) :
    ResolvedPreservesChainPublication allowed (left >>= next) := by
  intro context cache fuel table result completion hconsistent hstarts hallowed hresult
    hcompletion
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨middle, hmiddle, hrest⟩ := hresult
  cases middle with
  | none => simp at hrest
  | some middle =>
      have hcore := resolvedCore_of_mem_runResolvedFromTable (left.run cache) context fuel table
        middle hconsistent hstarts hmiddle
      simp only at hrest
      rw [hcore.1] at hrest
      have hmiddleCompletion : DeferredCompletion table middle.context completion :=
        hcompletion.of_mem_runResolvedFromTable ((next middle.value.1).run middle.value.2)
          middle.context middle.remaining table result completion hcore.2.1 hcore.2.2 hrest
      have hmiddleAllowed := hleft context cache fuel table middle completion hconsistent hstarts
        hallowed hmiddle hmiddleCompletion
      exact hnext middle.value.1 middle.context middle.value.2 middle.remaining table result
        completion hcore.2.1 hcore.2.2 hmiddleAllowed hrest hcompletion

theorem ResolvedPreservesChainPublication.of_noPublish
    (allowed : Coordinate → Prop)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hnoPublish : ∀ cache, ResolvedNoPublish (computation.run cache)) :
    ResolvedPreservesChainPublication allowed computation := by
  intro context cache fuel table result completion _ _ hallowed hresult _
  have hreveal := revealed_eq_of_mem_runResolvedFromTable_of_noPublish
    (computation.run cache) context fuel table result (hnoPublish cache) hresult
  intro coordinate hchain hrevealed
  apply hallowed coordinate hchain
  rw [← hreveal]
  exact hrevealed

theorem resolvedPreservesChainPublication_sequenceFin
    {allowed : Coordinate → Prop} {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomponent : ∀ index,
      ResolvedPreservesChainPublication allowed (computation index)) :
    ResolvedPreservesChainPublication allowed (sequenceFin computation) := by
  induction n with
  | zero =>
      simpa [sequenceFin] using
        ResolvedPreservesChainPublication.pure allowed Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun head =>
        (ih (fun index : Fin n => computation index.succ)
          (fun index => hcomponent index.succ)).bind fun tail =>
            ResolvedPreservesChainPublication.pure allowed
              (Fin.cases head tail : Fin (n + 1) → alpha)

theorem resolvedPreservesChainPublication_simulateQ
    {spec : OracleSpec ι} (allowed : Coordinate → Prop)
    (impl : QueryImpl spec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))))
    (himpl : ∀ query, ResolvedPreservesChainPublication allowed (impl query))
    (computation : OracleComp spec alpha) :
    ResolvedPreservesChainPublication allowed (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact ResolvedPreservesChainPublication.pure allowed value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (himpl query).bind fun output => ih output

theorem resolvedPreservesChainPublication_publishCoordinate
    (allowed : Coordinate → Prop) (coordinate : Coordinate)
    (hcoordinate : IsChainCoordinate coordinate → allowed coordinate) :
    ResolvedPreservesChainPublication allowed (publishCoordinate coordinate) := by
  intro context cache fuel table result completion _ _ hallowed hresult _
  unfold publishCoordinate at hresult
  rw [StateT.run_liftM, LazyRevealProbe.publishQuery,
    runResolvedFromTable_publish_query_bind] at hresult
  simp [runResolvedFromTable] at hresult
  subst result
  intro other hchain hrevealed
  simp only [LazyRevealProbe.State.publish, Finset.mem_insert] at hrevealed
  rcases hrevealed with rfl | hrevealed
  · exact hcoordinate hchain
  · exact hallowed other hchain hrevealed

theorem resolvedNoPublish_splitHashQuery (key : SplitHashKey) (cache : SplitHashCache) :
    ResolvedNoPublish ((splitHashQuery key).run cache) := by
  unfold splitHashQuery
  cases hlookup : cache key <;>
    simp [hlookup, ResolvedNoPublish, IsPublishQuery, StateT.run_bind, StateT.run_get,
      StateT.run_set, LazyRevealProbe.hashOutputQuery]

theorem resolvedNoPublish_ensureCoordinate (coordinate : Coordinate)
    (cache : SplitHashCache) :
    ResolvedNoPublish ((ensureCoordinate coordinate).run cache) := by
  simp [ensureCoordinate, ResolvedNoPublish, LazyRevealProbe.ensureQuery, IsPublishQuery]

theorem resolvedNoPublish_revealCoordinate (coordinate : Coordinate)
    (cache : SplitHashCache) :
    ResolvedNoPublish ((revealCoordinate coordinate).run cache) := by
  rw [revealCoordinate_run]
  simp [ResolvedNoPublish, LazyRevealProbe.revealQuery, IsPublishQuery]

theorem resolvedNoPublish_revealCoordinateOutput (coordinate : Coordinate)
    (cache : SplitHashCache) :
    ResolvedNoPublish ((revealCoordinateOutput coordinate).run cache) := by
  unfold revealCoordinateOutput
  simp [ResolvedNoPublish, IsPublishQuery, StateT.run_bind,
    StateT.run_modify, LazyRevealProbe.revealQuery]

theorem resolvedPreservesChainPublication_revealPublishedCoordinate
    (allowed : Coordinate → Prop) (coordinate : Coordinate)
    (hcoordinate : IsChainCoordinate coordinate → allowed coordinate) :
    ResolvedPreservesChainPublication allowed (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (ResolvedPreservesChainPublication.of_noPublish allowed (revealCoordinate coordinate)
    fun cache => resolvedNoPublish_revealCoordinate coordinate cache).bind fun _ =>
      (resolvedPreservesChainPublication_publishCoordinate allowed coordinate hcoordinate).bind
        fun _ => ResolvedPreservesChainPublication.pure allowed _

theorem resolvedPreservesChainPublication_revealLayerValues
    (allowed : Coordinate → Prop) (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit)
    (hallowed : ∀ chainIdx,
      allowed (chainValueCoordinate lay (treeIndexAt index lay)
        (leafIndexAt index lay) chainIdx (encoding chainIdx))) :
    ResolvedPreservesChainPublication allowed
      (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  apply (resolvedPreservesChainPublication_sequenceFin _ fun chainIdx =>
    resolvedPreservesChainPublication_revealPublishedCoordinate allowed _ fun _ =>
      hallowed chainIdx).bind
  intro values
  let pathComputation : Fin maxLayerHeight → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Digest := fun level =>
    if level.val < layerHeight lay then
      match level.val with
      | 0 => revealPublishedCoordinate (.position (.leaf lay (treeIndexAt index lay)
          (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
      | current + 1 =>
          if hlevel : current < maxLayerHeight then
            revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
              ⟨current, hlevel⟩
              (leafOfNat (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
          else pure 0
    else pure 0
  change ResolvedPreservesChainPublication allowed
    (sequenceFin pathComputation >>= fun path => pure (values, path))
  have hpath : ResolvedPreservesChainPublication allowed
      (sequenceFin pathComputation) :=
    resolvedPreservesChainPublication_sequenceFin pathComputation fun level => by
    dsimp only [pathComputation]
    by_cases hinLayer : level.val < layerHeight lay
    · simp only [hinLayer, if_pos]
      cases hlevel : level.val with
      | zero =>
          exact resolvedPreservesChainPublication_revealPublishedCoordinate allowed _
            (by simp [IsChainCoordinate])
      | succ current =>
          by_cases hcurrent : current < maxLayerHeight
          · simp only [hcurrent, dite_true]
            exact resolvedPreservesChainPublication_revealPublishedCoordinate allowed _
              (by simp [IsChainCoordinate])
          · simp only [hcurrent, dite_false]
            exact ResolvedPreservesChainPublication.pure allowed 0
    · simp only [hinLayer, if_false]
      exact ResolvedPreservesChainPublication.pure allowed 0
  exact ResolvedPreservesChainPublication.bind
    (allowed := allowed) (left := sequenceFin pathComputation)
    (next := fun path => pure (values, path)) hpath fun path =>
      ResolvedPreservesChainPublication.pure allowed (values, path)

theorem resolvedNoPublish_peekCoordinate (coordinate : Coordinate)
    (cache : SplitHashCache) :
    ResolvedNoPublish ((peekCoordinate coordinate).run cache) := by
  unfold peekCoordinate
  rw [StateT.run_bind]
  change ResolvedNoPublish
    (LazyRevealProbe.peekQuery coordinate >>= fun output => pure (_, cache))
  simp [ResolvedNoPublish, LazyRevealProbe.peekQuery, IsPublishQuery]

theorem resolvedNoPublish_peekPositionValues (positions : List Position)
    (cache : SplitHashCache) :
    ResolvedNoPublish ((peekPositionValues positions).run cache) := by
  induction positions generalizing cache with
  | nil => simp [peekPositionValues, resolvedNoPublish_pure]
  | cons position remaining ih =>
      rw [peekPositionValues, StateT.run_bind]
      exact (resolvedNoPublish_peekCoordinate (.position position) cache).bind_all fun result =>
        match result.1 with
        | none => resolvedNoPublish_pure (none, result.2)
        | some value => by
            rw [StateT.run_bind]
            exact (ih result.2).bind_all fun rest =>
              match rest.1 with
              | none => resolvedNoPublish_pure (none, rest.2)
              | some values => resolvedNoPublish_pure (some (value :: values), rest.2)

theorem resolvedNoPublish_peekTableInput (parameter : PublicParameter)
    (coordinate : Coordinate) (cache : SplitHashCache) :
    ResolvedNoPublish ((peekTableInput parameter coordinate).run cache) := by
  have hchildren (position : Position) : ResolvedNoPublish ((do
      match ← peekPositionValues position.children with
      | none => pure none
      | some values =>
          pure (some (tweakableHashInput parameter position.domain
            (values.flatMap digestBytes)))).run cache) := by
    rw [StateT.run_bind]
    exact (resolvedNoPublish_peekPositionValues position.children cache).bind_all fun result =>
      match result.1 with
      | none => resolvedNoPublish_pure (none, result.2)
      | some values => resolvedNoPublish_pure (some
          (tweakableHashInput parameter position.domain
            (values.flatMap digestBytes)), result.2)
  cases coordinate with
  | chainStart => simp [peekTableInput, resolvedNoPublish_pure]
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero, StateT.run_bind]
            exact (resolvedNoPublish_peekCoordinate
              (.chainStart lay tree leafIdx chainIdx) cache).bind_all fun result =>
                match result.1 with
                | none => resolvedNoPublish_pure (none, result.2)
                | some value => resolvedNoPublish_pure (some
                    (tweakableHashInput parameter
                      (.chain lay tree leafIdx chainIdx step) (digestBytes value)), result.2)
          · rw [if_neg hzero, StateT.run_bind]
            exact (resolvedNoPublish_peekPositionValues
              (Position.chain lay tree leafIdx chainIdx step).children cache).bind_all fun result =>
                match result.1 with
                | none => resolvedNoPublish_pure (none, result.2)
                | some values => resolvedNoPublish_pure (some
                    (tweakableHashInput parameter
                      (.chain lay tree leafIdx chainIdx step)
                        (values.flatMap digestBytes)), result.2)
      | leaf lay tree leafIdx =>
          rw [peekTableInput]
          · exact hchildren (.leaf lay tree leafIdx)
          · simp
      | node lay tree level nodeIdx =>
          rw [peekTableInput]
          · exact hchildren (.node lay tree level nodeIdx)
          · simp
      | ftsLeaf index tree leafIdx =>
          rw [peekTableInput]
          · exact hchildren (.ftsLeaf index tree leafIdx)
          · simp
      | ftsNode index tree level nodeIdx =>
          rw [peekTableInput]
          · exact hchildren (.ftsNode index tree level nodeIdx)
          · simp
      | ftsRoots index =>
          rw [peekTableInput]
          · exact hchildren (.ftsRoots index)
          · simp

theorem resolvedNoPublish_modify
    (update : SplitHashCache → SplitHashCache) (cache : SplitHashCache) :
    ResolvedNoPublish
      ((modify update : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) Unit).run cache) := by
  simp [StateT.run_modify, resolvedNoPublish_pure]

theorem resolvedPreservesChainPublication_resolveKnownInput
    (allowed : Coordinate → Prop) (parameter : PublicParameter)
    (coordinate : Coordinate) (input : HashInput)
    (hcoordinate : IsChainCoordinate coordinate → allowed coordinate) :
    ResolvedPreservesChainPublication allowed
      (resolveKnownInput parameter coordinate input) := by
  unfold resolveKnownInput
  apply (ResolvedPreservesChainPublication.of_noPublish allowed
    (peekTableInput parameter coordinate)
      fun cache => resolvedNoPublish_peekTableInput parameter coordinate cache).bind
  intro known
  cases known with
  | none =>
      exact ResolvedPreservesChainPublication.of_noPublish allowed
        (splitHashQuery (.ordinary input)) fun cache =>
          resolvedNoPublish_splitHashQuery (.ordinary input) cache
  | some knownInput =>
      simp only
      by_cases heq : knownInput = input
      · rw [if_pos heq]
        apply (ResolvedPreservesChainPublication.of_noPublish allowed
          (revealCoordinateOutput coordinate)
            fun cache => resolvedNoPublish_revealCoordinateOutput coordinate cache).bind
        intro output
        apply (resolvedPreservesChainPublication_publishCoordinate allowed coordinate
          hcoordinate).bind
        intro _
        apply (ResolvedPreservesChainPublication.of_noPublish allowed
          (modify fun cache : SplitHashCache =>
            Function.update cache (.ordinary input) (some output)) fun cache =>
              resolvedNoPublish_modify _ cache).bind
        intro _
        exact ResolvedPreservesChainPublication.pure allowed output
      · rw [if_neg heq]
        exact ResolvedPreservesChainPublication.of_noPublish allowed
          (splitHashQuery (.ordinary input)) fun cache =>
            resolvedNoPublish_splitHashQuery (.ordinary input) cache

theorem revealed_eq_of_mem_runResolvedFromTable_resolveKnownInput_completionOrdinary
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {coordinate : Coordinate} {input : HashInput}
    {context : DeferredContext} {fuel : Nat} {cache : SplitHashCache}
    {result : ResolvedRunResult (HashOutput × SplitHashCache)}
    {completion : Coordinate → HashOutput}
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hots : ∀ position, coordinate = .position position → IsOtsPosition position)
    (hordinary : CompletionOrdinaryInput parameter table context input)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((resolveKnownInput parameter coordinate input).run cache)))
    (hcompletion : DeferredCompletion table result.context completion) :
    result.context.state.revealed = context.state.revealed := by
  have hcompletionStart : DeferredCompletion table context completion :=
    hcompletion.of_mem_runResolvedFromTable
      ((resolveKnownInput parameter coordinate input).run cache) context fuel table result
        completion hconsistent hstarts hresult
  unfold resolveKnownInput at hresult
  rw [StateT.run_bind, runResolvedFromTable_bind] at hresult
  by_cases havailable : TableInputAvailable completion context.state coordinate
  · rw [runResolvedFromTable_peekTableInput_of_available parameter completion context fuel table
      cache coordinate havailable] at hresult
    simp only [pure_bind] at hresult
    have hne : tableInput parameter completion coordinate ≠ input := by
      intro heq
      cases coordinate with
      | chainStart => simp [TableInputAvailable] at havailable
      | position position =>
          exact hordinary completion hcompletionStart position (hots position rfl) heq.symm
    rw [if_neg hne] at hresult
    exact revealed_eq_of_mem_runResolvedFromTable_of_noPublish
      ((splitHashQuery (.ordinary input)).run cache) context fuel table result
        (resolvedNoPublish_splitHashQuery (.ordinary input) cache) hresult
  · rw [runResolvedFromTable_peekTableInput_of_unavailable parameter completion context fuel table
      cache coordinate hcompletionStart hots havailable] at hresult
    simp only [pure_bind] at hresult
    exact revealed_eq_of_mem_runResolvedFromTable_of_noPublish
      ((splitHashQuery (.ordinary input)).run cache) context fuel table result
        (resolvedNoPublish_splitHashQuery (.ordinary input) cache) hresult

theorem resolvedNoPublish_probe (candidate : Probe) (cache : SplitHashCache) :
    ResolvedNoPublish ((probe candidate).run cache) := by
  unfold probe
  rw [StateT.run_liftM]
  simp [ResolvedNoPublish, LazyRevealProbe.probeQuery, IsPublishQuery]

theorem resolvedNoPublish_probeFirstMissingInputCoordinate
    (input : HashInput) (slot : Nat) (coordinates : List Coordinate)
    (cache : SplitHashCache) :
    ResolvedNoPublish
      ((probeFirstMissingInputCoordinate input slot coordinates).run cache) := by
  induction coordinates generalizing slot cache with
  | nil => simp [probeFirstMissingInputCoordinate, resolvedNoPublish_pure]
  | cons coordinate remaining ih =>
      rw [probeFirstMissingInputCoordinate, StateT.run_bind]
      exact (resolvedNoPublish_peekCoordinate coordinate cache).bind_all fun result =>
        match result.1 with
        | none => resolvedNoPublish_probe ⟨coordinate, slotDigest slot input⟩ result.2
        | some _ => ih (slot + 1) result.2

theorem resolvedNoPublish_prepareLeafInputProbe
    (input : HashInput) (candidate : Probe) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (cache : SplitHashCache) :
    ResolvedNoPublish
      ((prepareLeafInputProbe input candidate lay tree leafIdx).run cache) := by
  unfold prepareLeafInputProbe
  rw [StateT.run_bind]
  exact (resolvedNoPublish_peekCoordinate candidate.coordinate cache).bind_all fun result =>
    match result.1 with
    | none => resolvedNoPublish_probe candidate result.2
    | some _ => resolvedNoPublish_probeFirstMissingInputCoordinate input 0
        ((Position.leaf lay tree leafIdx).children.map Coordinate.position) result.2

theorem resolvedPreservesChainPublication_probingHashQuery_chain
    (allowed : Coordinate → Prop) (parameter : PublicParameter)
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep)
    (hprobe : decodeProbe? parameter input = some candidate)
    (hposition : decodePosition? parameter input =
      some (.chain lay tree leafIdx chainIdx step))
    (hforward : ChainForwardClosed allowed) :
    ResolvedPreservesChainPublication allowed (probingHashQuery parameter input) := by
  have hmatches := (decodeProbe?_eq_some_iff parameter input candidate).1 hprobe
  have hsourceChain := candidate.isChainCoordinate_of_matchesInput hmatches
  have houtput := decodeProbe?_outputCoordinate_eq_position parameter input candidate
    (.chain lay tree leafIdx chainIdx step) hprobe hposition
  intro context cache fuel table result completion hconsistent hstarts hallowed hresult
    hcompletion
  unfold probingHashQuery at hresult
  rw [hprobe, hposition] at hresult
  simp only at hresult
  rw [houtput, StateT.run_bind, runResolvedFromTable_bind] at hresult
  unfold probe at hresult
  rw [StateT.run_liftM, LazyRevealProbe.probeQuery,
    runResolvedFromTable_probe_query_bind] at hresult
  cases fuel with
  | zero => simp at hresult
  | succ remaining =>
      rw [show remaining + 1 = Nat.succ remaining by omega] at hresult
      simp only at hresult
      by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
      · rw [if_pos hrevealed] at hresult
        have houtputAllowed : IsChainCoordinate
            (.position (.chain lay tree leafIdx chainIdx step)) →
            allowed (.position (.chain lay tree leafIdx chainIdx step)) := by
          intro houtputChain
          rw [← houtput]
          exact hforward candidate (hallowed candidate.coordinate hsourceChain hrevealed)
            (houtput ▸ houtputChain)
        exact resolvedPreservesChainPublication_resolveKnownInput allowed parameter
          (.position (.chain lay tree leafIdx chainIdx step)) input houtputAllowed context cache
            remaining table result completion hconsistent hstarts hallowed hresult hcompletion
      · rw [if_neg hrevealed] at hresult
        simp only [runResolvedFromTable, pure_bind] at hresult
        let probeContext : DeferredContext :=
          { context with state :=
              context.state.addPending candidate.coordinate candidate.candidate }
        change some result ∈ support
          (runResolvedFromTable probeContext remaining table
            ((resolveKnownInput parameter
              (.position (.chain lay tree leafIdx chainIdx step)) input).run cache)) at hresult
        have hpending : (candidate.coordinate, candidate.candidate) ∈
            probeContext.state.pending := by
          simp [probeContext, LazyRevealProbe.State.addPending]
        have hordinary : CompletionOrdinaryInput parameter table probeContext input :=
          completionOrdinaryInput_of_pending_decodedProbe hprobe hpending
        have hreveal :=
          revealed_eq_of_mem_runResolvedFromTable_resolveKnownInput_completionOrdinary
            (parameter := parameter) (table := table)
            (coordinate := .position (.chain lay tree leafIdx chainIdx step))
            (context := probeContext) (fuel := remaining) (cache := cache)
            (result := result) (completion := completion)
            (hconsistent.addPending candidate.coordinate candidate.candidate)
            (hstarts.addPending candidate.coordinate candidate.candidate)
            (fun position heq => by cases heq; simp [IsOtsPosition]) hordinary
            hresult hcompletion
        intro coordinate hchain hcoordinateRevealed
        apply hallowed coordinate hchain
        have hprobeRevealed : coordinate ∈ probeContext.state.revealed := by
          rw [← hreveal]
          exact hcoordinateRevealed
        simpa [probeContext, LazyRevealProbe.State.addPending] using hprobeRevealed

theorem resolvedPreservesChainPublication_probingHashQuery
    (allowed : Coordinate → Prop) (parameter : PublicParameter)
    (input : HashInput) (hforward : ChainForwardClosed allowed) :
    ResolvedPreservesChainPublication allowed (probingHashQuery parameter input) := by
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      rcases decodePosition?_chain_or_leaf_of_decodeProbe? parameter input candidate hprobe with
        ⟨lay, tree, leafIdx, chainIdx, step, hposition⟩ |
          ⟨lay, tree, leafIdx, hposition⟩
      · exact resolvedPreservesChainPublication_probingHashQuery_chain allowed parameter input
          candidate lay tree leafIdx chainIdx step hprobe hposition hforward
      · have houtput := decodeProbe?_outputCoordinate_eq_position parameter input candidate
          (.leaf lay tree leafIdx) hprobe hposition
        unfold probingHashQuery
        rw [hprobe, hposition]
        simp only
        apply (ResolvedPreservesChainPublication.of_noPublish allowed
          (prepareLeafInputProbe input candidate lay tree leafIdx) fun cache =>
            resolvedNoPublish_prepareLeafInputProbe input candidate lay tree leafIdx cache).bind
        intro _
        rw [houtput]
        exact resolvedPreservesChainPublication_resolveKnownInput allowed parameter
          (.position (.leaf lay tree leafIdx)) input (by simp [IsChainCoordinate])
  | none =>
      cases hposition : decodePosition? parameter input with
      | none =>
          exact ResolvedPreservesChainPublication.of_noPublish allowed
            (probingHashQuery parameter input) fun cache => by
              unfold probingHashQuery
              rw [hprobe, hposition]
              exact resolvedNoPublish_splitHashQuery (.ordinary input) cache
      | some position =>
          cases position with
          | chain lay tree leafIdx chainIdx step =>
              intro context cache fuel table result completion hconsistent hstarts hallowed
                hresult hcompletion
              have hordinary := completionOrdinaryInput_of_decodeProbe_none_chain
                (table := table) (context := context) hprobe hposition
              unfold probingHashQuery at hresult
              rw [hprobe, hposition] at hresult
              have hreveal :=
                revealed_eq_of_mem_runResolvedFromTable_resolveKnownInput_completionOrdinary
                  (parameter := parameter) (table := table)
                  (coordinate := .position (.chain lay tree leafIdx chainIdx step))
                  (context := context) (fuel := fuel) (cache := cache) (result := result)
                  (completion := completion) hconsistent hstarts
                  (fun other heq => by cases heq; simp [IsOtsPosition]) hordinary hresult
                    hcompletion
              intro coordinate hchain hrevealed
              apply hallowed coordinate hchain
              rw [← hreveal]
              exact hrevealed
          | leaf lay tree leafIdx =>
              intro context cache fuel table result completion hconsistent hstarts hallowed
                hresult hcompletion
              have hordinary := completionOrdinaryInput_of_decodeProbe_none_leaf
                (table := table) (context := context) hprobe hposition
              unfold probingHashQuery at hresult
              rw [hprobe, hposition] at hresult
              have hreveal :=
                revealed_eq_of_mem_runResolvedFromTable_resolveKnownInput_completionOrdinary
                  (parameter := parameter) (table := table)
                  (coordinate := .position (.leaf lay tree leafIdx))
                  (context := context) (fuel := fuel) (cache := cache) (result := result)
                  (completion := completion) hconsistent hstarts
                  (fun other heq => by cases heq; simp [IsOtsPosition]) hordinary hresult
                    hcompletion
              intro coordinate hchain hrevealed
              apply hallowed coordinate hchain
              rw [← hreveal]
              exact hrevealed
          | node lay tree level nodeIdx =>
              unfold probingHashQuery
              rw [hprobe, hposition]
              simp only
              apply (ResolvedPreservesChainPublication.of_noPublish allowed
                (probeFirstMissingInputCoordinate input 0
                  ((Position.node lay tree level nodeIdx).children.map Coordinate.position))
                    fun cache => resolvedNoPublish_probeFirstMissingInputCoordinate input 0
                      ((Position.node lay tree level nodeIdx).children.map Coordinate.position)
                        cache).bind
              intro _
              exact resolvedPreservesChainPublication_resolveKnownInput allowed parameter
                (.position (.node lay tree level nodeIdx)) input (by simp [IsChainCoordinate])
          | ftsLeaf index tree leafIdx =>
              exact ResolvedPreservesChainPublication.of_noPublish allowed
                (probingHashQuery parameter input) fun cache => by
                  unfold probingHashQuery
                  rw [hprobe, hposition]
                  exact resolvedNoPublish_splitHashQuery (.ordinary input) cache

          | ftsNode index tree level nodeIdx =>
              exact ResolvedPreservesChainPublication.of_noPublish allowed
                (probingHashQuery parameter input) fun cache => by
                  unfold probingHashQuery
                  rw [hprobe, hposition]
                  exact resolvedNoPublish_splitHashQuery (.ordinary input) cache
          | ftsRoots index =>
              exact ResolvedPreservesChainPublication.of_noPublish allowed
                (probingHashQuery parameter input) fun cache => by
                  unfold probingHashQuery
                  rw [hprobe, hposition]
                  exact resolvedNoPublish_splitHashQuery (.ordinary input) cache

theorem resolvedNoPublish_splitUniformImpl (query : Nat) (cache : SplitHashCache) :
    ResolvedNoPublish ((splitUniformImpl query).run cache) := by
  simp [splitUniformImpl, ResolvedNoPublish, LazyRevealProbe.uniformQuery, IsPublishQuery]

theorem resolvedNoPublish_ordinaryHashImpl (input : HashInput) (cache : SplitHashCache) :
    ResolvedNoPublish ((ordinaryHashImpl input).run cache) :=
  resolvedNoPublish_splitHashQuery (.ordinary input) cache

theorem resolvedNoPublish_ordinaryRomImpl (query : OracleWorld.Domain)
    (cache : SplitHashCache) :
    ResolvedNoPublish ((ordinaryRomImpl query).run cache) := by
  cases query with
  | inl query => exact resolvedNoPublish_splitUniformImpl query cache
  | inr input => exact resolvedNoPublish_ordinaryHashImpl input cache

theorem noPublish_ensureCoordinate (coordinate : Coordinate) :
    NoPublish (ensureCoordinate coordinate) :=
  resolvedNoPublish_ensureCoordinate coordinate

theorem noPublish_revealCoordinate (coordinate : Coordinate) :
    NoPublish (revealCoordinate coordinate) :=
  resolvedNoPublish_revealCoordinate coordinate

theorem noPublish_revealPosition (position : Position) :
    NoPublish (revealPosition position) :=
  noPublish_revealCoordinate (.position position)

theorem noPublish_simulateQ_ordinaryHashImpl
    (computation : OracleComp HashSpec alpha) :
    NoPublish (simulateQ ordinaryHashImpl computation) :=
  noPublish_simulateQ ordinaryHashImpl
    (fun input cache => resolvedNoPublish_ordinaryHashImpl input cache) computation

theorem noPublish_simulateQ_ordinaryRomImpl
    (computation : OracleComp OracleWorld alpha) :
    NoPublish (simulateQ ordinaryRomImpl computation) :=
  noPublish_simulateQ ordinaryRomImpl
    (fun input cache => resolvedNoPublish_ordinaryRomImpl input cache) computation

theorem noPublish_ensureFullChain (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    NoPublish (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (noPublish_sequenceFin _ fun step =>
    noPublish_ensureCoordinate (.position (.chain lay tree leafIdx chainIdx step))).bind
      fun _ => NoPublish.pure ()

theorem noPublish_ensureChainPrefix (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    NoPublish (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (noPublish_sequenceFin _ fun step => by
    split
    · exact noPublish_ensureCoordinate (.position (.chain lay tree leafIdx chainIdx step))
    · exact NoPublish.pure ()).bind fun _ => NoPublish.pure ()

theorem noPublish_ensureOtsLeaf (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) : NoPublish (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (noPublish_sequenceFin _ fun chainIdx =>
    noPublish_ensureFullChain lay tree leafIdx chainIdx).bind fun _ =>
      noPublish_ensureCoordinate (.position (.leaf lay tree leafIdx))

theorem noPublish_ensureTreeNode (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx, NoPublish (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => noPublish_ensureOtsLeaf lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (noPublish_ensureTreeNode lay tree level (2 * nodeIdx)).bind fun _ =>
        (noPublish_ensureTreeNode lay tree level (2 * nodeIdx + 1)).bind fun _ => by
          split
          · exact noPublish_ensureCoordinate (.position
              (.node lay tree ⟨level, by assumption⟩ (leafOfNat nodeIdx)))
          · exact NoPublish.pure ()

theorem noPublish_maskedTreeNode (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) : NoPublish (maskedTreeNode lay tree level nodeIdx) := by
  cases level with
  | zero =>
      rw [maskedTreeNode]
      exact (noPublish_ensureTreeNode lay tree 0 nodeIdx).bind fun _ =>
        noPublish_revealPosition (.leaf lay tree (leafOfNat nodeIdx))
  | succ current =>
      rw [maskedTreeNode]
      exact (noPublish_ensureTreeNode lay tree (current + 1) nodeIdx).bind fun _ => by
        split
        · exact noPublish_revealPosition
            (.node lay tree ⟨current, by assumption⟩ (leafOfNat nodeIdx))
        · exact NoPublish.pure 0

theorem noPublish_maskedTreeRoot (lay : Layer) (tree : TreeIndex) :
    NoPublish (maskedTreeRoot lay tree) :=
  noPublish_maskedTreeNode lay tree (layerHeight lay) 0

theorem noPublish_ensureTreePath (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) : NoPublish (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (noPublish_sequenceFin _ fun level => by
    split
    · exact noPublish_ensureTreeNode lay tree level.val
        (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
    · exact NoPublish.pure ()).bind fun _ => NoPublish.pure ()

theorem noPublish_maskedOtsSignFrom (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter,
      NoPublish (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, _ => NoPublish.pure none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      exact (noPublish_simulateQ_ordinaryHashImpl
        (encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))).bind fun encoded => by
            cases encoded with
            | none =>
                exact noPublish_maskedOtsSignFrom parameter lay tree leafIdx message attempts
                  (counter + 1)
            | some encoding =>
                exact (noPublish_sequenceFin _ fun chainIdx =>
                  noPublish_ensureChainPrefix lay tree leafIdx chainIdx
                    (encoding chainIdx)).bind fun _ => NoPublish.pure _

theorem noPublish_maskedOtsSign (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    NoPublish (maskedOtsSign parameter lay tree leafIdx message) :=
  noPublish_maskedOtsSignFrom parameter lay tree leafIdx message encodingAttemptLimit 0

theorem noPublish_maskedLayerMessage (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    NoPublish (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split
  · exact noPublish_maskedTreeRoot _ _
  · exact noPublish_simulateQ_ordinaryHashImpl _

theorem noPublish_maskedSignLayer (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    NoPublish (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (noPublish_maskedLayerMessage parameter ftsSecret index lay).bind fun message =>
    (noPublish_maskedOtsSign parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) message).bind fun signed => by
        cases signed with
        | none => exact NoPublish.pure none
        | some part =>
            exact (noPublish_ensureTreePath lay (treeIndexAt index lay)
              (leafIndexAt index lay)).bind fun _ => NoPublish.pure (some part)

theorem noPublish_revealPrivateLayerValues (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) :
    NoPublish (revealPrivateLayerValues index lay encoding) := by
  unfold revealPrivateLayerValues
  apply (noPublish_sequenceFin _ fun chainIdx =>
    noPublish_revealCoordinate
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
        (encoding chainIdx))).bind
  intro values
  apply (noPublish_sequenceFin _ fun level => by
    by_cases hinLayer : level.val < layerHeight lay
    · simp only [hinLayer, if_pos]
      cases hvalue : level.val with
      | zero => exact noPublish_revealPosition _
      | succ current =>
          by_cases hcurrent : current < maxLayerHeight
          · simp only [hcurrent, dite_true]
            exact noPublish_revealPosition _
          · simp only [hcurrent, dite_false]
            exact NoPublish.pure 0
    · simp only [hinLayer, if_false]
      exact NoPublish.pure 0).bind
  intro path
  exact NoPublish.pure (values, path)

theorem noPublish_maskedChronologicalSignLayer
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) :
    NoPublish (maskedChronologicalSignLayer parameter ftsSecret index lay) := by
  unfold maskedChronologicalSignLayer
  exact (noPublish_maskedSignLayer parameter ftsSecret index lay).bind fun selected => by
    cases selected with
    | none => exact NoPublish.pure none
    | some selected =>
        rcases selected with ⟨counter, encoding⟩
        exact (noPublish_revealPrivateLayerValues index lay encoding).bind fun values =>
          NoPublish.pure (some (show ChronologicalLayerPart from
            ⟨counter, encoding, values.1, values.2⟩))

theorem noPublish_maskedChronologicalSignLayers
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) :
    NoPublish (maskedChronologicalSignLayers parameter ftsSecret index) := by
  unfold maskedChronologicalSignLayers
  exact noPublish_sequenceFin _ fun lay =>
    noPublish_maskedChronologicalSignLayer parameter ftsSecret index lay

theorem resolvedPreservesChainPublication_publishChronologicalSignature
    (allowed : Coordinate → Prop)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (layers : Layer → Option ChronologicalLayerPart)
    (hallowed : ∀ parts, traverseOption layers = some parts → ∀ lay chainIdx,
      allowed (chainValueCoordinate lay (treeIndexAt index lay)
        (leafIndexAt index lay) chainIdx ((parts lay).encoding chainIdx))) :
    ResolvedPreservesChainPublication allowed
      (publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers) := by
  unfold publishChronologicalSignature
  cases hparts : traverseOption layers with
  | none => exact ResolvedPreservesChainPublication.pure allowed none
  | some parts =>
      apply (resolvedPreservesChainPublication_sequenceFin _ fun lay =>
        resolvedPreservesChainPublication_revealLayerValues allowed index lay
          (parts lay).encoding (hallowed parts hparts lay)).bind
      intro published
      exact ResolvedPreservesChainPublication.pure allowed (some (show Signature from
        { randomness := randomness
          ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := ftsPath
          counter := fun lay => (parts lay).counter
          chainValue := fun lay => (published lay).1
          authPath := flattenPaths fun lay => (published lay).2 }))

theorem resolvedPreservesChainPublication_maskedPublishedChronologicalSignAfterDigest
    (allowed : Coordinate → Prop) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (hallowed : ∀ (layers : Layer → Option ChronologicalLayerPart)
        (parts : Layer → ChronologicalLayerPart),
      traverseOption layers = some parts → ∀ lay chainIdx,
      allowed (chainValueCoordinate lay (treeIndexAt index lay)
        (leafIndexAt index lay) chainIdx ((parts lay).encoding chainIdx))) :
    ResolvedPreservesChainPublication allowed
      (maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedPublishedChronologicalSignAfterDigest
  exact (ResolvedPreservesChainPublication.of_noPublish allowed _
    (noPublish_simulateQ_ordinaryHashImpl
      (ftsOpen parameter index leaves (ftsSecret index)))).bind fun ftsPath =>
        (ResolvedPreservesChainPublication.of_noPublish allowed _
          (noPublish_maskedChronologicalSignLayers parameter ftsSecret index)).bind fun layers =>
            resolvedPreservesChainPublication_publishChronologicalSignature allowed ftsSecret
              randomness index leaves ftsPath layers (hallowed layers)

theorem resolvedPreservesChainPublication_maskedPublishedChronologicalSign
    (allowed : Coordinate → Prop) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (hallowed : ∀ (randomness : Randomness) (index : Index)
        (leaves : DigestTree → FtsLeaf)
        (layers : Layer → Option ChronologicalLayerPart)
        (parts : Layer → ChronologicalLayerPart),
      traverseOption layers = some parts → ∀ lay chainIdx,
        allowed (chainValueCoordinate lay (treeIndexAt index lay)
          (leafIndexAt index lay) chainIdx ((parts lay).encoding chainIdx))) :
    ResolvedPreservesChainPublication allowed
      (maskedPublishedChronologicalSign parameter root ftsSecret message) := by
  unfold maskedPublishedChronologicalSign
  apply (ResolvedPreservesChainPublication.of_noPublish allowed _
    (noPublish_simulateQ_ordinaryRomImpl
      (signDigestLoop digestAttemptLimit
        (⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ : SecretKey) message))).bind
  intro selected
  cases selected with
  | none => exact ResolvedPreservesChainPublication.pure allowed none
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      exact resolvedPreservesChainPublication_maskedPublishedChronologicalSignAfterDigest
        allowed parameter ftsSecret randomness index leaves (hallowed randomness index leaves)

theorem resolvedPreservesChainPublication_probingRomImpl
    (allowed : Coordinate → Prop) (parameter : PublicParameter)
    (hforward : ChainForwardClosed allowed) (query : OracleWorld.Domain) :
    ResolvedPreservesChainPublication allowed (probingRomImpl parameter query) := by
  cases query with
  | inl n =>
      exact ResolvedPreservesChainPublication.of_noPublish allowed
        (splitUniformImpl n) fun cache => resolvedNoPublish_splitUniformImpl n cache
  | inr input =>
      exact resolvedPreservesChainPublication_probingHashQuery allowed parameter input hforward

theorem resolvedPreservesChainPublication_probingRom
    (allowed : Coordinate → Prop) (parameter : PublicParameter)
    (hforward : ChainForwardClosed allowed)
    (computation : OracleComp OracleWorld alpha) :
    ResolvedPreservesChainPublication allowed
      (simulateQ (probingRomImpl parameter) computation) :=
  resolvedPreservesChainPublication_simulateQ allowed (probingRomImpl parameter)
    (resolvedPreservesChainPublication_probingRomImpl allowed parameter hforward) computation

theorem DeferredCompletion.not_probeHits_of_probingHashQuery_chain
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {fuel : Nat} {cache : SplitHashCache}
    {result : ResolvedRunResult (HashOutput × SplitHashCache)}
    {completion : Coordinate → HashOutput} {probe : Probe} {input : HashInput}
    (fallback : QueryImpl HashSpec Id)
    {lay : Layer} {tree : TreeIndex} {leafIdx : LeafIndex}
    {chainIdx : ChainIndex} {step : ChainStep}
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hmatches : probe.MatchesInput parameter input)
    (hposition : decodePosition? parameter input =
      some (.chain lay tree leafIdx chainIdx step))
    (hnotRevealed : probe.coordinate ∉ context.state.revealed)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((probingHashQuery parameter input).run cache)))
    (hcompletion : DeferredCompletion table result.context completion)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ¬probe.Hits (tableAnswer parameter completion fallback)
      parameter (tableOtsSecret completion) ftsSecret := by
  have hprobe : decodeProbe? parameter input = some probe :=
    (decodeProbe?_eq_some_iff parameter input probe).2 hmatches
  unfold probingHashQuery at hresult
  rw [hprobe, hposition] at hresult
  simp only at hresult
  rw [StateT.run_bind, runResolvedFromTable_bind] at hresult
  unfold SphincsSecurity.Concrete.OtsProbeSimulation.probe at hresult
  rw [StateT.run_liftM, LazyRevealProbe.probeQuery,
    runResolvedFromTable_probe_query_bind] at hresult
  cases fuel with
  | zero => simp at hresult
  | succ remaining =>
      rw [show remaining + 1 = Nat.succ remaining by omega] at hresult
      simp only at hresult
      rw [if_neg hnotRevealed] at hresult
      simp only [runResolvedFromTable] at hresult
      let probeContext : DeferredContext :=
        { context with state := context.state.addPending probe.coordinate probe.candidate }
      have hbefore : DeferredCompletion table probeContext completion :=
        hcompletion.of_mem_runResolvedFromTable _ probeContext remaining table result completion
          (hconsistent.addPending probe.coordinate probe.candidate)
          (hstarts.addPending probe.coordinate probe.candidate) (by
            simpa [probeContext, runResolvedFromTable] using hresult)
      apply hbefore.not_probeHits_tableAnswer_of_pending
        fallback ftsSecret probe input hmatches
      simp [probeContext, LazyRevealProbe.State.addPending]

theorem ResolvedContextInvariant.concreteCache_agreesWith_tableAnswer
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache concreteCache)
    (completion : Coordinate → HashOutput)
    (hcompletion : DeferredCompletion table context completion) :
    concreteCache.AgreesWithFn
      (tableAnswer parameter completion (fromCache ordinaryCache)) := by
  intro input output hcached
  rcases hinvariant.2.2.2.2.2 input output hcached with hordinary | hfixed
  · unfold tableAnswer
    cases hdecode : decodePosition? parameter input with
    | none =>
        change fromCache ordinaryCache input = output
        exact agreesWithFn_fromCache ordinaryCache hordinary
    | some position =>
        have hcanonicalOutput (hots : IsOtsPosition position)
            (hexact : input = tableInput parameter completion (.position position)) :
            completion (.position position) = output := by
          have hagrees := hinvariant.1 completion hcompletion position hots
          rw [← hexact] at hagrees
          unfold ResolveInputAgrees at hagrees
          cases hvalue : context.positionValue position with
          | none =>
              rw [hvalue] at hagrees
              rw [hcached] at hagrees
              simp at hagrees
          | some cached =>
              rw [hvalue] at hagrees
              have hcachedEq : cached = output := Option.some.inj (hagrees.symm.trans hcached)
              exact (hcompletion.eq_positionValue position cached hvalue).trans hcachedEq
        cases position with
        | chain lay tree leafIdx chainIdx step =>
            by_cases hexact : input = tableInput parameter completion
                (.position (.chain lay tree leafIdx chainIdx step))
            · rw [tableAnswerDecoded, if_pos hexact]
              exact hcanonicalOutput (by trivial) hexact
            · rw [tableAnswerDecoded, if_neg hexact]
              exact agreesWithFn_fromCache ordinaryCache hordinary
        | leaf lay tree leafIdx =>
            by_cases hexact : input = tableInput parameter completion
                (.position (.leaf lay tree leafIdx))
            · rw [tableAnswerDecoded, if_pos hexact]
              exact hcanonicalOutput (by trivial) hexact
            · rw [tableAnswerDecoded, if_neg hexact]
              exact agreesWithFn_fromCache ordinaryCache hordinary
        | node lay tree level nodeIdx =>
            by_cases hexact : input = tableInput parameter completion
                (.position (.node lay tree level nodeIdx))
            · rw [tableAnswerDecoded, if_pos hexact]
              exact hcanonicalOutput (by trivial) hexact
            · rw [tableAnswerDecoded, if_neg hexact]
              exact agreesWithFn_fromCache ordinaryCache hordinary
        | ftsLeaf | ftsNode | ftsRoots =>
            change fromCache ordinaryCache input = output
            exact agreesWithFn_fromCache ordinaryCache hordinary
  · rcases hfixed with ⟨position, hots, hvalue, hinput⟩
    rw [hinput completion hcompletion,
      tableAnswer_tableInput parameter completion (fromCache ordinaryCache) position hots,
      hcompletion.eq_positionValue position output hvalue]

end SphincsSecurity.Concrete.OtsProbeSimulation
