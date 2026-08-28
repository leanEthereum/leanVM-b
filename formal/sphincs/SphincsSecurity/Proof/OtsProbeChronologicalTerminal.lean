import SphincsSecurity.Proof.OtsProbeResolvedSampling

/-!
# Chronological one-time terminal argument

Private chronological resolution may materialize a chain value without publishing it. The old `ChainState.ValidFor` invariant deliberately identifies materialization with publication, so it is not the right invariant for this game. This file tracks publication separately and uses deferred completions only for the one exact verifier probe supplied by terminal extraction.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec OracleComp.ProgramLogic.Relational

theorem exists_right_of_relTriple_of_mem_support
    {left : ProbComp alpha} {right : ProbComp beta} {relation : alpha → beta → Prop}
    (hrel : RelTriple left right relation) {leftResult : alpha}
    (hleft : leftResult ∈ support left) :
    ∃ rightResult ∈ support right, relation leftResult rightResult := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost] at hrel
  obtain ⟨coupling, hrelation⟩ := hrel
  have hleftDist : leftResult ∈ support 𝒟[left] := by
    apply (mem_support_iff_evalDist_apply_ne_zero 𝒟[left] leftResult).2
    exact (mem_support_iff_evalDist_apply_ne_zero left leftResult).1 hleft
  have hleftMapped : leftResult ∈ support (Prod.fst <$> coupling.1) := by
    rw [coupling.2.map_fst]
    exact hleftDist
  rw [support_map] at hleftMapped
  obtain ⟨pair, hpair, heq⟩ := hleftMapped
  have hrightMapped : pair.2 ∈ support (Prod.snd <$> coupling.1) := by
    rw [support_map]
    exact ⟨pair, hpair, rfl⟩
  have hrightDist : pair.2 ∈ support 𝒟[right] := by
    rw [← coupling.2.map_snd]
    exact hrightMapped
  have hright : pair.2 ∈ support right := by
    apply (mem_support_iff_evalDist_apply_ne_zero right pair.2).2
    exact (mem_support_iff_evalDist_apply_ne_zero 𝒟[right] pair.2).1 hrightDist
  exact ⟨pair.2, hright, heq ▸ hrelation pair hpair⟩

theorem ReachableResolvedRunRel.clean_of_completion
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {result : ResolvedRunResult (alpha × SplitHashCache)}
    {value : alpha} {concreteCache : QueryCache HashSpec}
    (hrelation : ReachableResolvedRunRel parameter table (some result)
      (value, concreteCache))
    {completion : Coordinate → HashOutput}
    (hcompletion : DeferredCompletion table result.context completion) :
    result.value.1 = value ∧
      ResolvedContextInvariant parameter table result.context
        (ordinaryQueryCache result.value.2) concreteCache ∧
      VisibleResolvedComputationsCached parameter table result.context concreteCache ∧
      PublishedValues result.context.state := by
  rcases hrelation with hclean | hdoomed
  · exact ⟨hclean.2.1, hclean.2.2.1, hclean.2.2.2.1, hclean.2.2.2.2⟩
  · exact False.elim (hdoomed.2.2.2 ⟨completion, hcompletion⟩)

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

theorem resolvedOtsSelectFrom_replay
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter initial final result,
      (result, final) ∈ support
        ((resolvedOtsSelectFrom parameter lay tree leafIdx message attempts counter).run initial) →
      final.AgreesWithFn f →
      initial ≤ final ∧ ∀ selectedCounter encoding, result = some (selectedCounter, encoding) →
        evalWithAnswerFn f
          (encode parameter lay tree leafIdx message selectedCounter) = some encoding ∧
        CachedRun final f (encode parameter lay tree leafIdx message selectedCounter)
  | 0, counter, initial, final, result, hresult, _ => by
      simp [resolvedOtsSelectFrom] at hresult
      rcases hresult with ⟨rfl, rfl⟩
      exact ⟨le_rfl, by simp⟩
  | attempts + 1, counter, initial, final, result, hresult, hf => by
      rw [resolvedOtsSelectFrom, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨⟨encoded, encodedCache⟩, hencoded, hrest⟩ := hresult
      cases encoded with
      | none =>
          have hqueryLe := FtsProbeSimulation.simulateQ_randomOracle_cache_le
            (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter))
              initial encodedCache none hencoded
          have htail := resolvedOtsSelectFrom_replay f parameter lay tree leafIdx message attempts
            (counter + 1) encodedCache final result hrest hf
          exact ⟨hqueryLe.trans htail.1, htail.2⟩
      | some encoding =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hrest
          rcases hrest with ⟨rfl, rfl⟩
          obtain ⟨hle, heval, hcached⟩ := replay_of_mem_support
            (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter))
            initial (some encoding) final hencoded f hf
          refine ⟨hle, ?_⟩
          intro selectedCounter selectedEncoding heq
          rcases Option.some.inj heq with ⟨rfl, rfl⟩
          exact ⟨heval, hcached⟩

theorem resolvedSignLayer_some_honest_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer)
    (initial final : QueryCache HashSpec) (counter : Counter)
    (encoding : ChainIndex → Digit)
    (hresult : (some (counter, encoding), final) ∈ support
      ((resolvedSignLayer parameter table ftsSecret index lay).run initial))
    (hf : final.AgreesWithFn f) :
    evalWithAnswerFn f
      (encode parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f
          (layerMessage
            (⟨parameter, root,
              fun selectedLay selectedTree selectedLeaf selectedChain =>
                truncateHash
                  (table ⟨selectedLay, selectedTree, selectedLeaf, selectedChain⟩),
              ftsSecret⟩ : SecretKey)
              index lay)) counter) = some encoding ∧
      CachedRun final f
        (encode parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (evalWithAnswerFn f
            (layerMessage
              (⟨parameter, root,
                fun selectedLay selectedTree selectedLeaf selectedChain =>
                  truncateHash
                    (table ⟨selectedLay, selectedTree, selectedLeaf, selectedChain⟩),
                ftsSecret⟩ : SecretKey)
              index lay)) counter) := by
  unfold resolvedSignLayer at hresult
  rw [StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨⟨message, messageCache⟩, hmessage, hrest⟩ := hresult
  rw [StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨selected, selectedCache⟩, hselected, hfinish⟩ := hrest
  cases selected with
  | none => simp at hfinish
  | some selected =>
      rcases selected with ⟨selectedCounter, selectedEncoding⟩
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at hfinish
      rcases hfinish with ⟨⟨rfl, rfl⟩, rfl⟩
      have hselectedReplay := resolvedOtsSelectFrom_replay f parameter lay
        (treeIndexAt index lay) (leafIndexAt index lay) message encodingAttemptLimit 0
          messageCache final (some (counter, encoding)) hselected hf
      have hmessageEval : evalWithAnswerFn f
          (layerMessage
            (⟨parameter, root,
              fun selectedLay selectedTree selectedLeaf selectedChain =>
                truncateHash
                  (table ⟨selectedLay, selectedTree, selectedLeaf, selectedChain⟩),
              ftsSecret⟩ : SecretKey)
              index lay) = message := by
        rw [resolvedLayerMessage_eq_layerMessage parameter root table ftsSecret index lay]
          at hmessage
        exact (replay_of_mem_support_of_le _ initial message messageCache final hmessage
          hselectedReplay.1 f hf).1
      rw [hmessageEval]
      exact hselectedReplay.2 counter encoding rfl

theorem resolvedChronologicalSignLayer_select_support
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer)
    (initial final : QueryCache HashSpec) (part : ChronologicalLayerPart)
    (hresult : (some part, final) ∈ support
      ((resolvedChronologicalSignLayer parameter table ftsSecret index lay).run initial)) :
    ∃ selectedCache,
      (some (part.counter, part.encoding), selectedCache) ∈ support
        ((resolvedSignLayer parameter table ftsSecret index lay).run initial) ∧
      selectedCache ≤ final := by
  unfold resolvedChronologicalSignLayer at hresult
  rw [StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨⟨selected, selectedCache⟩, hselected, hrest⟩ := hresult
  cases selected with
  | none => simp at hrest
  | some selected =>
      rcases selected with ⟨counter, encoding⟩
      rw [StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨values, valuesCache⟩, hvalues, hfinish⟩ := hrest
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at hfinish
      rcases hfinish with ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩
      exact ⟨selectedCache, hselected,
        resolvedRevealLayerValues_cache_mono parameter table index lay encoding
          selectedCache final values hvalues⟩

theorem reachableResolvedCouples_maskedChronologicalSignLayers
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) :
    ReachableResolvedCouples parameter table
      (maskedChronologicalSignLayers parameter ftsSecret index)
      (sequenceFin fun lay =>
        resolvedChronologicalSignLayer parameter table ftsSecret index lay) := by
  unfold maskedChronologicalSignLayers
  exact reachableResolvedCouples_sequenceFin
    (fun lay => maskedChronologicalSignLayer parameter ftsSecret index lay)
    (fun lay => resolvedChronologicalSignLayer parameter table ftsSecret index lay)
    (fun lay => reachableResolvedCouples_maskedChronologicalSignLayer parameter table ftsSecret
      index lay)

theorem concreteSupport_of_mem_runResolved_maskedChronologicalSignLayer
    (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult
      (Option ChronologicalLayerPart × SplitHashCache))
    (completion : Coordinate → HashOutput)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((maskedChronologicalSignLayer parameter ftsSecret index lay).run cache)))
    (hcompletion : DeferredCompletion table result.context completion) :
    ∃ rightCache,
      (result.value.1, rightCache) ∈ support
        ((resolvedChronologicalSignLayer parameter table ftsSecret index lay).run concreteCache) ∧
      ResolvedContextInvariant parameter table result.context
        (ordinaryQueryCache result.value.2) rightCache ∧
      VisibleResolvedComputationsCached parameter table result.context rightCache ∧
      PublishedValues result.context.state := by
  let left := maskedChronologicalSignLayer parameter ftsSecret index lay
  let right := resolvedChronologicalSignLayer parameter table ftsSecret index lay
  have hrel : RelTriple
      (runResolvedFromTable context fuel table (left.run cache))
      (right.run concreteCache) (ReachableResolvedRunRel parameter table) :=
    reachableResolvedCouples_maskedChronologicalSignLayer parameter table ftsSecret index lay
      context fuel cache concreteCache hinvariant hclosed hpublished
  change some result ∈ support
    (runResolvedFromTable context fuel table (left.run cache)) at hresult
  obtain ⟨rightResult, hrightSupport, hrelation⟩ :=
    exists_right_of_relTriple_of_mem_support
      (relation := ReachableResolvedRunRel parameter table) hrel hresult
  rcases rightResult with ⟨rightValue, rightCache⟩
  have hclean := ReachableResolvedRunRel.clean_of_completion hrelation hcompletion
  refine ⟨rightCache, ?_, hclean.2.1, hclean.2.2.1, hclean.2.2.2⟩
  rw [hclean.1]
  exact hrightSupport

set_option maxHeartbeats 800000 in
theorem concreteSupport_of_mem_runResolved_chronologicalLayerSequence
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) :
    ∀ {n : Nat} (indices : Fin n → Layer)
      (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
      (concreteCache : QueryCache HashSpec)
      (result : ResolvedRunResult
        ((Fin n → Option ChronologicalLayerPart) × SplitHashCache))
      (completion : Coordinate → HashOutput),
      ResolvedContextInvariant parameter table context
        (ordinaryQueryCache cache) concreteCache →
      VisibleResolvedComputationsCached parameter table context concreteCache →
      PublishedValues context.state →
      some result ∈ support
        (runResolvedFromTable context fuel table
          ((sequenceFin fun position =>
            maskedChronologicalSignLayer parameter ftsSecret index (indices position)).run cache)) →
      DeferredCompletion table result.context completion →
      ∃ rightCache,
        ResolvedContextInvariant parameter table result.context
          (ordinaryQueryCache result.value.2) rightCache ∧
        VisibleResolvedComputationsCached parameter table result.context rightCache ∧
        PublishedValues result.context.state ∧
        (result.value.1, rightCache) ∈ support
          ((sequenceFin fun position =>
            resolvedChronologicalSignLayer parameter table ftsSecret index
              (indices position)).run concreteCache)
  | 0, indices, context, fuel, cache, concreteCache, result, completion,
      hinvariant, hclosed, hpublished, hresult, _ => by
      simp [sequenceFin, runResolvedFromTable] at hresult
      subst result
      refine ⟨concreteCache, hinvariant, hclosed, hpublished, ?_⟩
      simp [sequenceFin]
  | n + 1, indices, context, fuel, cache, concreteCache, result, completion,
      hinvariant, hclosed, hpublished, hresult, hcompletion => by
      rw [sequenceFin, StateT.run_bind, runResolvedFromTable_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨headOption, hhead, hrest⟩ := hresult
      cases headOption with
      | none => simp at hrest
      | some headResult =>
          have hheadCore := resolvedCore_of_mem_runResolvedFromTable
            ((maskedChronologicalSignLayer parameter ftsSecret index (indices 0)).run cache)
            context fuel table headResult hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hhead
          simp only at hrest
          rw [hheadCore.1] at hrest
          have hheadCompletion : DeferredCompletion table headResult.context completion :=
            hcompletion.of_mem_runResolvedFromTable _ headResult.context headResult.remaining table
              result completion hheadCore.2.1 hheadCore.2.2 hrest
          obtain ⟨rightHeadCache, hrightHead, hheadInvariant, hheadClosed, hheadPublished⟩ :=
            concreteSupport_of_mem_runResolved_maskedChronologicalSignLayer parameter table
              ftsSecret index (indices 0) context fuel cache concreteCache headResult completion
                hinvariant hclosed hpublished hhead hheadCompletion
          rw [StateT.run_bind, runResolvedFromTable_bind,
            mem_support_bind_iff] at hrest
          obtain ⟨tailOption, htail, hfinish⟩ := hrest
          cases tailOption with
          | none => simp at hfinish
          | some tailResult =>
              have htailCore := resolvedCore_of_mem_runResolvedFromTable
                ((sequenceFin fun position : Fin n =>
                  maskedChronologicalSignLayer parameter ftsSecret index
                    (indices position.succ)).run headResult.value.2)
                headResult.context headResult.remaining table tailResult
                  hheadCore.2.1 hheadCore.2.2 htail
              simp only at hfinish
              rw [htailCore.1] at hfinish
              simp [runResolvedFromTable] at hfinish
              subst result
              obtain ⟨rightTailCache, htailInvariant, htailClosed, htailPublished,
                  hrightTail⟩ :=
                concreteSupport_of_mem_runResolved_chronologicalLayerSequence parameter table
                  ftsSecret index (fun position : Fin n => indices position.succ)
                    headResult.context headResult.remaining headResult.value.2 rightHeadCache
                      tailResult completion hheadInvariant hheadClosed hheadPublished htail
                        hcompletion
              refine ⟨rightTailCache, htailInvariant, htailClosed, htailPublished, ?_⟩
              rw [sequenceFin, StateT.run_bind, mem_support_bind_iff]
              refine ⟨(headResult.value.1, rightHeadCache), hrightHead, ?_⟩
              rw [StateT.run_bind, mem_support_bind_iff]
              exact ⟨(tailResult.value.1, rightTailCache), hrightTail, by simp⟩

def LayerEncodingsCached (cache : QueryCache HashSpec) (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (index : Index)
    (parts : Layer → Counter × (ChainIndex → Digit)) : Prop :=
  ∀ lay, CachedRun cache f
    (encode secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn f (layerMessage secretKey index lay)) (parts lay).1)

set_option maxHeartbeats 500000 in
theorem honestLayerParts_of_support_resolvedChronologicalSignLayers
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (initial final : QueryCache HashSpec)
    (layers : Layer → Option ChronologicalLayerPart)
    (parts : Layer → ChronologicalLayerPart)
    (hresult : (layers, final) ∈ support
      ((sequenceFin fun lay =>
        resolvedChronologicalSignLayer parameter table ftsSecret index lay).run initial))
    (hparts : traverseOption layers = some parts)
    (hf : final.AgreesWithFn f) :
    HonestLayerParts f
      (⟨parameter, root,
        fun selectedLay selectedTree selectedLeaf selectedChain =>
          truncateHash (table ⟨selectedLay, selectedTree, selectedLeaf, selectedChain⟩),
        ftsSecret⟩ : SecretKey)
      index (fun lay => ((parts lay).counter, (parts lay).encoding)) ∧
    LayerEncodingsCached final f
      (⟨parameter, root,
        fun selectedLay selectedTree selectedLeaf selectedChain =>
          truncateHash (table ⟨selectedLay, selectedTree, selectedLeaf, selectedChain⟩),
        ftsSecret⟩ : SecretKey)
      index (fun lay => ((parts lay).counter, (parts lay).encoding)) := by
  have hresultAt : ∀ lay,
      evalWithAnswerFn f
        (encode parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (evalWithAnswerFn f
            (layerMessage
              (⟨parameter, root,
                fun selectedLay selectedTree selectedLeaf selectedChain =>
                  truncateHash
                    (table ⟨selectedLay, selectedTree, selectedLeaf, selectedChain⟩),
                ftsSecret⟩ : SecretKey)
              index lay)) (parts lay).counter) = some (parts lay).encoding ∧
        CachedRun final f
          (encode parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (evalWithAnswerFn f
              (layerMessage
                (⟨parameter, root,
                  fun selectedLay selectedTree selectedLeaf selectedChain =>
                    truncateHash
                      (table ⟨selectedLay, selectedTree, selectedLeaf, selectedChain⟩),
                  ftsSecret⟩ : SecretKey)
                index lay)) (parts lay).counter) := by
    intro lay
    obtain ⟨componentInitial, componentFinal, componentValue, hcomponent,
        hvalue, hcomponentLe⟩ :=
      queryCache_sequenceFin_component_support
        (fun selectedLay =>
          resolvedChronologicalSignLayer parameter table ftsSecret index selectedLay)
        (fun selectedLay => resolvedChronologicalSignLayer_cache_mono parameter table ftsSecret
          index selectedLay) initial final layers hresult lay
    have hpartsAt := traverseOption_eq_some_apply layers parts hparts lay
    have hcomponentValue : componentValue = some (parts lay) := hvalue.symm.trans hpartsAt
    rw [hcomponentValue] at hcomponent
    obtain ⟨selectedCache, hselected, hselectedLe⟩ :=
      resolvedChronologicalSignLayer_select_support parameter table ftsSecret index lay
        componentInitial componentFinal (parts lay) hcomponent
    have hselectedAgrees : selectedCache.AgreesWithFn f := fun input output hcached =>
      hf (hcomponentLe (hselectedLe hcached))
    have hselectedResult := resolvedSignLayer_some_honest_eval f parameter root table ftsSecret
      index lay componentInitial selectedCache (parts lay).counter (parts lay).encoding hselected
        hselectedAgrees
    exact ⟨hselectedResult.1, hselectedResult.2.mono (hselectedLe.trans hcomponentLe)⟩
  exact ⟨fun lay => (hresultAt lay).1, fun lay => (hresultAt lay).2⟩

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

def OffTableInput (parameter : PublicParameter)
    (completion : Coordinate → HashOutput) (input : HashInput) : Prop :=
  ∀ position, IsOtsPosition position →
    input ≠ tableInput parameter completion (.position position)

def CacheAgreesWithFnOffTable (parameter : PublicParameter)
    (completion : Coordinate → HashOutput) (cache : QueryCache HashSpec)
    (f : QueryImpl HashSpec Id) : Prop :=
  ∀ input output, OffTableInput parameter completion input →
    cache input = some output → f input = output

theorem CacheAgreesWithFnOffTable.of_agrees
    {parameter : PublicParameter} {completion : Coordinate → HashOutput}
    {cache : QueryCache HashSpec} {f : QueryImpl HashSpec Id}
    (hf : cache.AgreesWithFn f) :
    CacheAgreesWithFnOffTable parameter completion cache f := by
  intro input output _ hcached
  exact hf hcached

theorem offTableInput_of_decodePosition_none
    {parameter : PublicParameter} {completion : Coordinate → HashOutput}
    {input : HashInput} (hdecode : decodePosition? parameter input = none) :
    OffTableInput parameter completion input := by
  intro position _ heq
  have hsome : decodePosition? parameter input = some position := by
    rw [heq]
    exact (decodePosition?_eq_some_iff parameter _ position).2
      ⟨tablePayload completion position, rfl⟩
  rw [hdecode] at hsome
  simp at hsome

theorem offTableInput_of_decodePosition_some_ne
    {parameter : PublicParameter} {completion : Coordinate → HashOutput}
    {input : HashInput} {decoded : Position}
    (hdecode : decodePosition? parameter input = some decoded)
    (hne : input ≠ tableInput parameter completion (.position decoded)) :
    OffTableInput parameter completion input := by
  intro position _ heq
  have hdecode' : decodePosition? parameter input = some position := by
    rw [heq]
    exact (decodePosition?_eq_some_iff parameter _ position).2
      ⟨tablePayload completion position, rfl⟩
  have hposition : decoded = position := Option.some.inj (hdecode.symm.trans hdecode')
  subst position
  exact hne heq

theorem offTableInput_of_decodePosition_some_not_ots
    {parameter : PublicParameter} {completion : Coordinate → HashOutput}
    {input : HashInput} {decoded : Position}
    (hdecode : decodePosition? parameter input = some decoded)
    (hnotOts : ¬IsOtsPosition decoded) :
    OffTableInput parameter completion input := by
  intro position hots heq
  have hdecode' : decodePosition? parameter input = some position := by
    rw [heq]
    exact (decodePosition?_eq_some_iff parameter _ position).2
      ⟨tablePayload completion position, rfl⟩
  have hposition : decoded = position := Option.some.inj (hdecode.symm.trans hdecode')
  exact hnotOts (hposition ▸ hots)

theorem ResolvedContextInvariant.concreteCache_agreesWith_tableAnswer_of_fallback
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache concreteCache)
    (completion : Coordinate → HashOutput)
    (hcompletion : DeferredCompletion table context completion)
    (fallback : QueryImpl HashSpec Id)
    (hfallback : CacheAgreesWithFnOffTable parameter completion ordinaryCache fallback) :
    concreteCache.AgreesWithFn
      (tableAnswer parameter completion fallback) := by
  intro input output hcached
  rcases hinvariant.2.2.2.2.2 input output hcached with hordinary | hfixed
  · unfold tableAnswer
    cases hdecode : decodePosition? parameter input with
    | none =>
        exact hfallback input output (offTableInput_of_decodePosition_none hdecode) hordinary
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
              exact hfallback input output
                (offTableInput_of_decodePosition_some_ne hdecode hexact) hordinary
        | leaf lay tree leafIdx =>
            by_cases hexact : input = tableInput parameter completion
                (.position (.leaf lay tree leafIdx))
            · rw [tableAnswerDecoded, if_pos hexact]
              exact hcanonicalOutput (by trivial) hexact
            · rw [tableAnswerDecoded, if_neg hexact]
              exact hfallback input output
                (offTableInput_of_decodePosition_some_ne hdecode hexact) hordinary
        | node lay tree level nodeIdx =>
            by_cases hexact : input = tableInput parameter completion
                (.position (.node lay tree level nodeIdx))
            · rw [tableAnswerDecoded, if_pos hexact]
              exact hcanonicalOutput (by trivial) hexact
            · rw [tableAnswerDecoded, if_neg hexact]
              exact hfallback input output
                (offTableInput_of_decodePosition_some_ne hdecode hexact) hordinary
        | ftsLeaf | ftsNode | ftsRoots =>
            exact hfallback input output
              (offTableInput_of_decodePosition_some_not_ots hdecode (by simp [IsOtsPosition]))
              hordinary
  · rcases hfixed with ⟨position, hots, hvalue, hinput⟩
    rw [hinput completion hcompletion,
      tableAnswer_tableInput parameter completion fallback position hots,
      hcompletion.eq_positionValue position output hvalue]

theorem ResolvedContextInvariant.concreteCache_agreesWith_tableAnswer
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache concreteCache)
    (completion : Coordinate → HashOutput)
    (hcompletion : DeferredCompletion table context completion) :
    concreteCache.AgreesWithFn
      (tableAnswer parameter completion (fromCache ordinaryCache)) :=
  hinvariant.concreteCache_agreesWith_tableAnswer_of_fallback completion hcompletion
    (fromCache ordinaryCache)
      (CacheAgreesWithFnOffTable.of_agrees (agreesWithFn_fromCache ordinaryCache))

theorem CacheAgreesWithFnOffTable.of_reachableResolvedCouples
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {right : StateT (QueryCache HashSpec) ProbComp alpha}
    {context : DeferredContext} {fuel : Nat} {cache : SplitHashCache}
    {concreteCache : QueryCache HashSpec}
    {result : ResolvedRunResult (alpha × SplitHashCache)}
    {completion : Coordinate → HashOutput} {fallback : QueryImpl HashSpec Id}
    (hcoupled : ReachableResolvedCouples parameter table left right)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table (left.run cache)))
    (hcompletion : DeferredCompletion table result.context completion)
    (hfinal : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback)
    (hrightLe : ∀ value finalCache,
      (value, finalCache) ∈ support (right.run concreteCache) →
      concreteCache ≤ finalCache) :
    CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache cache) fallback := by
  obtain ⟨rightResult, hrightSupport, hrelation⟩ :=
    exists_right_of_relTriple_of_mem_support
      (hcoupled context fuel cache concreteCache hinvariant hclosed hpublished) hresult
  rcases rightResult with ⟨rightValue, rightCache⟩
  obtain ⟨_value, hfinalInvariant, _hfinalClosed, _hfinalPublished⟩ :=
    hrelation.clean_of_completion hcompletion
  intro input output hoff hcached
  have hconcrete : concreteCache input = some output :=
    hinvariant.2.2.2.2.1 input output hcached
  have hright : rightCache input = some output :=
    hrightLe rightValue rightCache hrightSupport hconcrete
  rcases hfinalInvariant.2.2.2.2.2 input output hright with hordinary | hfixed
  · exact hfinal input output hoff hordinary
  · rcases hfixed with ⟨position, hots, _hvalue, hinput⟩
    exact False.elim (hoff position hots (hinput completion hcompletion))

section

attribute [local irreducible] sequenceFin runResolvedFromTable

set_option maxHeartbeats 800000 in
theorem concreteSupport_of_mem_runResolved_maskedChronologicalSignLayers
    (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult
      ((Layer → Option ChronologicalLayerPart) × SplitHashCache))
    (completion : Coordinate → HashOutput)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((maskedChronologicalSignLayers parameter ftsSecret index).run cache)))
    (hcompletion : DeferredCompletion table result.context completion) :
    ∃ rightCache,
      ResolvedContextInvariant parameter table result.context
        (ordinaryQueryCache result.value.2) rightCache ∧
      VisibleResolvedComputationsCached parameter table result.context rightCache ∧
      PublishedValues result.context.state ∧
      (result.value.1, rightCache) ∈ support
        ((sequenceFin fun lay =>
          resolvedChronologicalSignLayer parameter table ftsSecret index lay).run concreteCache) := by
  unfold maskedChronologicalSignLayers at hresult
  have hbridge0 :=
    concreteSupport_of_mem_runResolved_chronologicalLayerSequence parameter table ftsSecret index
      (n := numLayers) (fun lay : Layer => lay)
  have hbridge1 := hbridge0 context fuel cache concreteCache result completion
  have hbridge2 := hbridge1 hinvariant
  have hbridge3 := hbridge2 hclosed
  have hbridge4 :
      some result ∈ support
          (runResolvedFromTable context fuel table
            ((sequenceFin fun lay =>
              maskedChronologicalSignLayer parameter ftsSecret index lay).run cache)) →
      DeferredCompletion table result.context completion →
      ∃ rightCache,
        ResolvedContextInvariant parameter table result.context
          (ordinaryQueryCache result.value.2) rightCache ∧
        VisibleResolvedComputationsCached parameter table result.context rightCache ∧
        PublishedValues result.context.state ∧
        (result.value.1, rightCache) ∈ support
          ((sequenceFin fun lay =>
            resolvedChronologicalSignLayer parameter table ftsSecret index lay).run concreteCache) :=
    hbridge3 hpublished
  have hbridge5 := hbridge4 hresult
  exact hbridge5 hcompletion

set_option maxHeartbeats 500000 in
theorem honestLayerParts_of_mem_runResolved_maskedChronologicalSignLayers
    (fallback : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult
      ((Layer → Option ChronologicalLayerPart) × SplitHashCache))
    (completion : Coordinate → HashOutput)
    (parts : Layer → ChronologicalLayerPart)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((maskedChronologicalSignLayers parameter ftsSecret index).run cache)))
    (hcompletion : DeferredCompletion table result.context completion)
    (hparts : traverseOption result.value.1 = some parts)
    (hfallback : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback) :
    HonestLayerParts (tableAnswer parameter completion fallback)
      (⟨parameter, root,
        fun selectedLay selectedTree selectedLeaf selectedChain =>
          truncateHash (table ⟨selectedLay, selectedTree, selectedLeaf, selectedChain⟩),
        ftsSecret⟩ : SecretKey)
      index (fun lay => ((parts lay).counter, (parts lay).encoding)) ∧
    LayerEncodingsCached (ordinaryQueryCache result.value.2)
      (tableAnswer parameter completion fallback)
      (⟨parameter, root,
        fun selectedLay selectedTree selectedLeaf selectedChain =>
          truncateHash (table ⟨selectedLay, selectedTree, selectedLeaf, selectedChain⟩),
        ftsSecret⟩ : SecretKey)
      index (fun lay => ((parts lay).counter, (parts lay).encoding)) := by
  obtain ⟨rightCache, hfinalInvariant, _hfinalClosed, _hfinalPublished, hright⟩ :=
    concreteSupport_of_mem_runResolved_maskedChronologicalSignLayers parameter table ftsSecret
      index context fuel cache concreteCache result completion hinvariant hclosed hpublished hresult
        hcompletion
  have hrightAgrees : rightCache.AgreesWithFn
      (tableAnswer parameter completion fallback) :=
    @ResolvedContextInvariant.concreteCache_agreesWith_tableAnswer_of_fallback
      parameter table result.context (ordinaryQueryCache result.value.2) rightCache
        hfinalInvariant completion hcompletion fallback hfallback
  have hrightResult := honestLayerParts_of_support_resolvedChronologicalSignLayers
    (tableAnswer parameter completion fallback) parameter root table ftsSecret index concreteCache
      rightCache result.value.1 parts hright hparts hrightAgrees
  refine ⟨hrightResult.1, ?_⟩
  intro lay input hinput
  have hstable := queriesStable_encode (tableAnswer parameter completion fallback) parameter lay
    (treeIndexAt index lay) (leafIndexAt index lay)
    (evalWithAnswerFn (tableAnswer parameter completion fallback)
      (layerMessage
        (⟨parameter, root,
          fun selectedLay selectedTree selectedLeaf selectedChain =>
            truncateHash (table ⟨selectedLay, selectedTree, selectedLeaf, selectedChain⟩),
          ftsSecret⟩ : SecretKey)
        index lay)) (parts lay).counter input hinput
  rw [hfinalInvariant.2.2.2.2.eq_of_stable hfinalInvariant.2.2.2.1 input hstable]
  exact hrightResult.2 lay input hinput

end

theorem DeferredCompletion.tableOtsSecret_eq
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hcompletion : DeferredCompletion table context completion) :
    tableOtsSecret completion =
      fun lay tree leafIdx chainIdx =>
        truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
  funext lay tree leafIdx chainIdx
  exact congrArg truncateHash
    (hcompletion.2.2.2 ⟨lay, tree, leafIdx, chainIdx⟩)

def ResolvedOrdinaryCachePreserving
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ context fuel table cache result,
    some result ∈ support
      (runResolvedFromTable context fuel table (computation.run cache)) →
    ordinaryQueryCache result.value.2 = ordinaryQueryCache cache

theorem ResolvedOrdinaryCachePreserving.pure (value : alpha) :
    ResolvedOrdinaryCachePreserving
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro context fuel table cache result hresult
  simp [runResolvedFromTable] at hresult
  subst result
  rfl

theorem ResolvedOrdinaryCachePreserving.bind
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : ResolvedOrdinaryCachePreserving left)
    (hnext : ∀ value, ResolvedOrdinaryCachePreserving (next value)) :
    ResolvedOrdinaryCachePreserving (left >>= next) := by
  intro context fuel table cache result hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨middle, hmiddle, hrest⟩ := hresult
  cases middle with
  | none => simp at hrest
  | some middle =>
      simp only at hrest
      exact (hnext middle.value.1 middle.context middle.remaining middle.table middle.value.2 result
        hrest).trans (hleft context fuel table cache middle hmiddle)

theorem resolvedOrdinaryCachePreserving_sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomponent : ∀ index, ResolvedOrdinaryCachePreserving (computation index)) :
    ResolvedOrdinaryCachePreserving (sequenceFin computation) := by
  induction n with
  | zero =>
      simpa [sequenceFin] using ResolvedOrdinaryCachePreserving.pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun head =>
        (ih (fun index : Fin n => computation index.succ)
          (fun index => hcomponent index.succ)).bind fun tail =>
            ResolvedOrdinaryCachePreserving.pure
              (Fin.cases head tail : Fin (n + 1) → alpha)

theorem resolvedOrdinaryCachePreserving_revealCoordinate (coordinate : Coordinate) :
    ResolvedOrdinaryCachePreserving (revealCoordinate coordinate) := by
  intro context fuel table cache result hresult
  rw [revealCoordinate_run, LazyRevealProbe.revealQuery,
    runResolvedFromTable_reveal_query_bind] at hresult
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp only [pure_bind] at hresult
      cases hresolved : resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context with
      | none => simp [hresolved] at hresult
      | some resolved =>
          simp only [hresolved] at hresult
          simp [runResolvedFromTable] at hresult
          subst result
          exact ordinaryQueryCache_update_hidden cache
            (.chainStart lay tree leafIdx chainIdx) resolved.output
  | position position =>
      rw [mem_support_bind_iff] at hresult
      obtain ⟨resolved, _hresolved, hrest⟩ := hresult
      cases resolved with
      | none => simp at hrest
      | some resolved =>
          simp [runResolvedFromTable] at hrest
          subst result
          exact ordinaryQueryCache_update_hidden cache (.position position) resolved.output

theorem resolvedOrdinaryCachePreserving_publishCoordinate (coordinate : Coordinate) :
    ResolvedOrdinaryCachePreserving (publishCoordinate coordinate) := by
  intro context fuel table cache result hresult
  unfold publishCoordinate at hresult
  rw [StateT.run_liftM, LazyRevealProbe.publishQuery,
    runResolvedFromTable_publish_query_bind] at hresult
  simp [runResolvedFromTable] at hresult
  subst result
  rfl

theorem resolvedOrdinaryCachePreserving_revealPublishedCoordinate
    (coordinate : Coordinate) :
    ResolvedOrdinaryCachePreserving (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (resolvedOrdinaryCachePreserving_revealCoordinate coordinate).bind fun _ =>
    (resolvedOrdinaryCachePreserving_publishCoordinate coordinate).bind fun _ =>
      ResolvedOrdinaryCachePreserving.pure _

theorem resolvedOrdinaryCachePreserving_revealLayerValues
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    ResolvedOrdinaryCachePreserving (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (resolvedOrdinaryCachePreserving_sequenceFin _ fun chainIdx =>
    resolvedOrdinaryCachePreserving_revealPublishedCoordinate
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx (encoding chainIdx))).bind fun _ =>
      (resolvedOrdinaryCachePreserving_sequenceFin _ fun level => by
        split
        · cases hlevelValue : level.val with
          | zero => exact resolvedOrdinaryCachePreserving_revealPublishedCoordinate _
          | succ current =>
              rw [show current + 1 = Nat.succ current by omega]
              change ResolvedOrdinaryCachePreserving
                (if hlevel : current < maxLayerHeight then
                  revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
                    ⟨current, hlevel⟩ (leafOfNat
                      (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
                else pure 0)
              by_cases hlevel : current < maxLayerHeight
              · rw [dif_pos hlevel]
                exact resolvedOrdinaryCachePreserving_revealPublishedCoordinate _
              · rw [dif_neg hlevel]
                exact ResolvedOrdinaryCachePreserving.pure 0
        · exact ResolvedOrdinaryCachePreserving.pure 0).bind fun _ =>
          ResolvedOrdinaryCachePreserving.pure _

theorem resolvedOrdinaryCachePreserving_publishChronologicalSignature
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (layers : Layer → Option ChronologicalLayerPart) :
    ResolvedOrdinaryCachePreserving
      (publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers) := by
  unfold publishChronologicalSignature
  cases hparts : traverseOption layers with
  | none => exact ResolvedOrdinaryCachePreserving.pure none
  | some parts =>
      exact (resolvedOrdinaryCachePreserving_sequenceFin _ fun lay =>
        resolvedOrdinaryCachePreserving_revealLayerValues index lay
          (parts lay).encoding).bind fun _ =>
            ResolvedOrdinaryCachePreserving.pure _

theorem concreteSupport_of_mem_runResolved_ftsOpen
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : Index) (leaves : DigestTree → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult
      ((FtsTree → Fin ftsTreeHeight → Digest) × SplitHashCache))
    (completion : Coordinate → HashOutput)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((simulateQ ordinaryHashImpl (ftsOpen parameter index leaves secret)).run cache)))
    (hcompletion : DeferredCompletion table result.context completion) :
    ∃ rightCache,
      ResolvedContextInvariant parameter table result.context
        (ordinaryQueryCache result.value.2) rightCache ∧
      VisibleResolvedComputationsCached parameter table result.context rightCache ∧
      PublishedValues result.context.state ∧
      (result.value.1, rightCache) ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (ftsOpen parameter index leaves secret)).run concreteCache) := by
  let left := simulateQ ordinaryHashImpl (ftsOpen parameter index leaves secret)
  let right := simulateQ (randomOracle : QueryImpl HashSpec _)
    (ftsOpen parameter index leaves secret)
  have hrel : RelTriple
      (runResolvedFromTable context fuel table (left.run cache))
      (right.run concreteCache) (ReachableResolvedRunRel parameter table) :=
    reachableResolvedCouples_ftsOpen parameter table index leaves secret context fuel cache
      concreteCache hinvariant hclosed hpublished
  change some result ∈ support
    (runResolvedFromTable context fuel table (left.run cache)) at hresult
  obtain ⟨rightResult, hrightSupport, hrelation⟩ :=
    exists_right_of_relTriple_of_mem_support
      (relation := ReachableResolvedRunRel parameter table) hrel hresult
  rcases rightResult with ⟨rightValue, rightCache⟩
  have hclean := ReachableResolvedRunRel.clean_of_completion hrelation hcompletion
  refine ⟨rightCache, hclean.2.1, hclean.2.2.1, hclean.2.2.2, ?_⟩
  rw [hclean.1]
  exact hrightSupport

set_option maxHeartbeats 500000 in
theorem publishedChronologicalSignature_support
    (initial : Coordinate → Prop)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (layers : Layer → Option ChronologicalLayerPart)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (completion : Coordinate → HashOutput)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hallowed : RevealedChainAllowed initial context.state)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers).run
          cache)))
    (hcompletion : DeferredCompletion table result.context completion) :
    (result.value.1 = none ∧
        RevealedChainAllowed initial result.context.state) ∨
      ∃ (signature : Signature) (parts : Layer → ChronologicalLayerPart),
        result.value.1 = some signature ∧
          traverseOption layers = some parts ∧
          signature.randomness = randomness ∧
          signature.counter = (fun lay => (parts lay).counter) ∧
          RevealedChainAllowed
            (fun coordinate => initial coordinate ∨
              PublishedByParts index
                (fun lay => ((parts lay).counter, (parts lay).encoding)) coordinate)
            result.context.state := by
  cases hparts : traverseOption layers with
  | none =>
      have hfinalAllowed :=
        resolvedPreservesChainPublication_publishChronologicalSignature initial ftsSecret
          randomness index leaves ftsPath layers
            (fun _ hparts' => by simp [hparts] at hparts') context cache fuel table result
              completion hconsistent hstarts hallowed hresult hcompletion
      unfold publishChronologicalSignature at hresult
      rw [hparts] at hresult
      simp [runResolvedFromTable] at hresult
      subst result
      exact Or.inl ⟨rfl, hfinalAllowed⟩
  | some parts =>
      let allowed := fun coordinate => initial coordinate ∨
        PublishedByParts index
          (fun lay => ((parts lay).counter, (parts lay).encoding)) coordinate
      have hallowed' : RevealedChainAllowed allowed context.state :=
        hallowed.mono fun coordinate hcoordinate => Or.inl hcoordinate
      have hendpoints : ∀ lay chainIdx,
          allowed (chainValueCoordinate lay (treeIndexAt index lay)
            (leafIndexAt index lay) chainIdx ((parts lay).encoding chainIdx)) :=
        fun lay chainIdx => Or.inr (publishedByParts_selected index
          (fun selectedLay =>
            ((parts selectedLay).counter, (parts selectedLay).encoding)) lay chainIdx)
      have hfinalAllowed :=
        resolvedPreservesChainPublication_publishChronologicalSignature allowed ftsSecret
          randomness index leaves ftsPath layers
            (fun selectedParts hselectedParts => by
              have heq : selectedParts = parts := Option.some.inj (hselectedParts.symm.trans hparts)
              subst selectedParts
              exact hendpoints) context cache fuel table result completion hconsistent hstarts
                hallowed' hresult hcompletion
      unfold publishChronologicalSignature at hresult
      rw [hparts, StateT.run_bind, runResolvedFromTable_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨publishedResult, hpublished, hfinish⟩ := hresult
      cases publishedResult with
      | none => simp at hfinish
      | some publishedResult =>
          simp [runResolvedFromTable] at hfinish
          subst result
          exact Or.inr ⟨_, parts, rfl, rfl, rfl, rfl, hfinalAllowed⟩

section

attribute [local irreducible] sequenceFin runResolvedFromTable

theorem resolvedCore_of_mem_maskedChronologicalSignLayers
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult
      ((Layer → Option ChronologicalLayerPart) × SplitHashCache))
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((maskedChronologicalSignLayers parameter ftsSecret index).run cache))) :
    result.table = table ∧ result.context.ValuesConsistent ∧
      StartTableAgrees result.context.state table := by
  exact resolvedCore_of_mem_runResolvedFromTable
    ((maskedChronologicalSignLayers parameter ftsSecret index).run cache)
      context fuel table result hconsistent hstarts hresult

set_option maxHeartbeats 1000000 in
theorem maskedPublishedChronologicalSignAfterDigest_support
    (initial : Coordinate → Prop)
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (completion : Coordinate → HashOutput)
    (fallback : QueryImpl HashSpec Id)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hallowed : RevealedChainAllowed initial context.state)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index
          leaves).run cache)))
    (hcompletion : DeferredCompletion table result.context completion)
    (hfallback : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback) :
    (result.value.1 = none ∧
        RevealedChainAllowed initial result.context.state) ∨
      ∃ (signature : Signature) (parts : Layer → ChronologicalLayerPart),
        result.value.1 = some signature ∧
          signature.randomness = randomness ∧
          signature.counter = (fun lay => (parts lay).counter) ∧
          HonestLayerParts
            (tableAnswer parameter completion fallback)
            (⟨parameter, root,
              fun lay tree leafIdx chainIdx =>
                truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
              ftsSecret⟩ : SecretKey)
            index (fun lay => ((parts lay).counter, (parts lay).encoding)) ∧
          LayerEncodingsCached (ordinaryQueryCache result.value.2)
            (tableAnswer parameter completion fallback)
            (⟨parameter, root,
              fun lay tree leafIdx chainIdx =>
                truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
              ftsSecret⟩ : SecretKey)
            index (fun lay => ((parts lay).counter, (parts lay).encoding)) ∧
          RevealedChainAllowed
            (fun coordinate => initial coordinate ∨
              PublishedByParts index
                (fun lay => ((parts lay).counter, (parts lay).encoding)) coordinate)
            result.context.state := by
  unfold maskedPublishedChronologicalSignAfterDigest at hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨pathOption, hpath, hafterPath⟩ := hresult
  cases pathOption with
  | none => simp at hafterPath
  | some pathResult =>
      have hpathCore := resolvedCore_of_mem_runResolvedFromTable
        ((simulateQ ordinaryHashImpl
          (ftsOpen parameter index leaves (ftsSecret index))).run cache)
        context fuel table pathResult hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hpath
      simp only at hafterPath
      rw [hpathCore.1] at hafterPath
      have hpathRevealed := revealed_eq_of_mem_runResolvedFromTable_of_noPublish
        (((simulateQ ordinaryHashImpl
          (ftsOpen parameter index leaves (ftsSecret index))).run cache))
        context fuel table pathResult
          (noPublish_simulateQ_ordinaryHashImpl
            (ftsOpen parameter index leaves (ftsSecret index)) cache) hpath
      have hpathAllowed : RevealedChainAllowed initial pathResult.context.state := by
        intro coordinate hchain hrevealed
        apply hallowed coordinate hchain
        rw [← hpathRevealed]
        exact hrevealed
      rw [StateT.run_bind, runResolvedFromTable_bind,
        mem_support_bind_iff] at hafterPath
      obtain ⟨layersOption, hlayers, hpublish⟩ := hafterPath
      cases layersOption with
      | none => simp at hpublish
      | some layersResult =>
          have hlayersCore := resolvedCore_of_mem_maskedChronologicalSignLayers parameter table
            ftsSecret index pathResult.context pathResult.remaining pathResult.value.2 layersResult
              hpathCore.2.1 hpathCore.2.2 hlayers
          simp only at hpublish
          rw [hlayersCore.1] at hpublish
          have hlayersCompletion : DeferredCompletion table layersResult.context completion :=
            hcompletion.of_mem_runResolvedFromTable _ layersResult.context
              layersResult.remaining table result completion hlayersCore.2.1 hlayersCore.2.2
                hpublish
          have hpathCompletion : DeferredCompletion table pathResult.context completion :=
            hlayersCompletion.of_mem_runResolvedFromTable
              ((maskedChronologicalSignLayers parameter ftsSecret index).run pathResult.value.2)
              pathResult.context pathResult.remaining table layersResult completion hpathCore.2.1
                hpathCore.2.2 hlayers
          obtain ⟨pathConcreteCache, hpathInvariant, hpathClosed, hpathPublished,
              _hpathConcrete⟩ :=
            concreteSupport_of_mem_runResolved_ftsOpen parameter table index leaves
              (ftsSecret index) context fuel cache concreteCache pathResult completion hinvariant
                hclosed hpublished hpath hpathCompletion
          have hlayersRevealed := revealed_eq_of_mem_runResolvedFromTable_of_noPublish
            ((maskedChronologicalSignLayers parameter ftsSecret index).run pathResult.value.2)
            pathResult.context pathResult.remaining table layersResult
              (noPublish_maskedChronologicalSignLayers parameter ftsSecret index
                pathResult.value.2) hlayers
          have hlayersAllowed : RevealedChainAllowed initial layersResult.context.state := by
            intro coordinate hchain hrevealed
            apply hpathAllowed coordinate hchain
            rw [← hlayersRevealed]
            exact hrevealed
          have hpublishedResult := publishedChronologicalSignature_support initial ftsSecret
            randomness index leaves pathResult.value.1 layersResult.value.1 layersResult.context
              layersResult.remaining layersResult.value.2 table result completion hlayersCore.2.1
                hlayersCore.2.2 hlayersAllowed hpublish hcompletion
          rcases hpublishedResult with ⟨hnone, hfinalAllowed⟩ |
              ⟨signature, parts, hsignature, hparts, hrandomness, hcounter, hfinalAllowed⟩
          · exact Or.inl ⟨hnone, hfinalAllowed⟩
          · have hcacheEq :=
              resolvedOrdinaryCachePreserving_publishChronologicalSignature ftsSecret randomness
                index leaves pathResult.value.1 layersResult.value.1 layersResult.context
                  layersResult.remaining table layersResult.value.2 result hpublish
            have hlayersFallback : CacheAgreesWithFnOffTable parameter completion
                (ordinaryQueryCache layersResult.value.2) fallback := by
              rw [← hcacheEq]
              exact hfallback
            have hhonest :=
              honestLayerParts_of_mem_runResolved_maskedChronologicalSignLayers
                fallback parameter root table ftsSecret index pathResult.context
                  pathResult.remaining pathResult.value.2 pathConcreteCache layersResult
                    completion parts hpathInvariant hpathClosed hpathPublished hlayers
                      hlayersCompletion hparts hlayersFallback
            have hcachedFinal : LayerEncodingsCached (ordinaryQueryCache result.value.2)
                (tableAnswer parameter completion fallback)
                (⟨parameter, root,
                  fun lay tree leafIdx chainIdx =>
                    truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
                  ftsSecret⟩ : SecretKey)
                index (fun lay => ((parts lay).counter, (parts lay).encoding)) := by
              rw [hcacheEq]
              exact hhonest.2
            exact Or.inr
              ⟨signature, parts, hsignature, hrandomness, hcounter, hhonest.1,
                hcachedFinal, hfinalAllowed⟩

end

theorem concreteSupport_of_mem_runResolved_signDigestLoop
    (table : OtsSecretIndex → HashOutput) (secretKey : SecretKey)
    (message : Message) (attempts : Nat)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult
      (Option (Randomness × Index × (DigestTree → FtsLeaf)) × SplitHashCache))
    (completion : Coordinate → HashOutput)
    (hinvariant : ResolvedContextInvariant secretKey.parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached secretKey.parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((simulateQ ordinaryRomImpl
          (signDigestLoop attempts secretKey message)).run cache)))
    (hcompletion : DeferredCompletion table result.context completion) :
    ∃ rightCache,
      ResolvedContextInvariant secretKey.parameter table result.context
        (ordinaryQueryCache result.value.2) rightCache ∧
      VisibleResolvedComputationsCached secretKey.parameter table result.context rightCache ∧
      PublishedValues result.context.state ∧
      (result.value.1, rightCache) ∈ support
        ((simulateQ romImpl (signDigestLoop attempts secretKey message)).run concreteCache) := by
  let left := simulateQ ordinaryRomImpl (signDigestLoop attempts secretKey message)
  let right := simulateQ romImpl (signDigestLoop attempts secretKey message)
  have hrel : RelTriple
      (runResolvedFromTable context fuel table (left.run cache))
      (right.run concreteCache)
      (ReachableResolvedRunRel secretKey.parameter table) :=
    reachableResolvedCouples_signDigestLoop table secretKey message attempts context fuel cache
      concreteCache hinvariant hclosed hpublished
  change some result ∈ support
    (runResolvedFromTable context fuel table (left.run cache)) at hresult
  obtain ⟨rightResult, hrightSupport, hrelation⟩ :=
    exists_right_of_relTriple_of_mem_support
      (relation := ReachableResolvedRunRel secretKey.parameter table) hrel hresult
  rcases rightResult with ⟨rightValue, rightCache⟩
  have hclean := ReachableResolvedRunRel.clean_of_completion hrelation hcompletion
  refine ⟨rightCache, hclean.2.1, hclean.2.2.1, hclean.2.2.2, ?_⟩
  rw [hclean.1]
  exact hrightSupport

theorem concreteSupport_of_mem_runResolved_maskedPublishedChronologicalSignAfterDigest
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (completion : Coordinate → HashOutput)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index
          leaves).run cache)))
    (hcompletion : DeferredCompletion table result.context completion) :
    ∃ rightCache,
      ResolvedContextInvariant parameter table result.context
        (ordinaryQueryCache result.value.2) rightCache ∧
      VisibleResolvedComputationsCached parameter table result.context rightCache ∧
      PublishedValues result.context.state ∧
      (result.value.1, rightCache) ∈ support
        ((resolvedImmediateSignAfterDigest parameter table ftsSecret randomness index
          leaves).run concreteCache) := by
  let left := maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index
    leaves
  let right := resolvedImmediateSignAfterDigest parameter table ftsSecret randomness index leaves
  have hrel : RelTriple
      (runResolvedFromTable context fuel table (left.run cache))
      (right.run concreteCache)
      (ReachableResolvedRunRel parameter table) :=
    reachableResolvedCouples_maskedPublishedChronologicalSignAfterDigest_immediate parameter table
      ftsSecret randomness index leaves context fuel cache concreteCache hinvariant hclosed
        hpublished
  change some result ∈ support
    (runResolvedFromTable context fuel table (left.run cache)) at hresult
  obtain ⟨rightResult, hrightSupport, hrelation⟩ :=
    exists_right_of_relTriple_of_mem_support
      (relation := ReachableResolvedRunRel parameter table) hrel hresult
  rcases rightResult with ⟨rightValue, rightCache⟩
  have hclean := ReachableResolvedRunRel.clean_of_completion hrelation hcompletion
  refine ⟨rightCache, hclean.2.1, hclean.2.2.1, hclean.2.2.2, ?_⟩
  rw [hclean.1]
  exact hrightSupport

theorem concreteSupport_of_mem_runResolved_of_reachableResolvedCouples
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {right : StateT (QueryCache HashSpec) ProbComp alpha}
    {context : DeferredContext} {fuel : Nat} {cache : SplitHashCache}
    {concreteCache : QueryCache HashSpec}
    {result : ResolvedRunResult (alpha × SplitHashCache)}
    {completion : Coordinate → HashOutput}
    (hcoupled : ReachableResolvedCouples parameter table left right)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table (left.run cache)))
    (hcompletion : DeferredCompletion table result.context completion) :
    ∃ rightCache,
      ResolvedContextInvariant parameter table result.context
        (ordinaryQueryCache result.value.2) rightCache ∧
      VisibleResolvedComputationsCached parameter table result.context rightCache ∧
      PublishedValues result.context.state ∧
      (result.value.1, rightCache) ∈ support (right.run concreteCache) := by
  obtain ⟨rightResult, hrightSupport, hrelation⟩ :=
    exists_right_of_relTriple_of_mem_support
      (hcoupled context fuel cache concreteCache hinvariant hclosed hpublished) hresult
  rcases rightResult with ⟨rightValue, rightCache⟩
  have hclean := hrelation.clean_of_completion hcompletion
  refine ⟨rightCache, hclean.2.1, hclean.2.2.1, hclean.2.2.2, ?_⟩
  rw [hclean.1]
  exact hrightSupport

theorem resolvedCore_of_mem_runResolved_of_reachableResolvedCouples
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {right : StateT (QueryCache HashSpec) ProbComp alpha}
    {context : DeferredContext} {fuel : Nat} {cache : SplitHashCache}
    {concreteCache : QueryCache HashSpec}
    {result : ResolvedRunResult (alpha × SplitHashCache)}
    (hcoupled : ReachableResolvedCouples parameter table left right)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table (left.run cache))) :
    result.table = table ∧ result.context.ValuesConsistent ∧
      StartTableAgrees result.context.state table := by
  obtain ⟨rightResult, _hrightSupport, hrelation⟩ :=
    exists_right_of_relTriple_of_mem_support
      (hcoupled context fuel cache concreteCache hinvariant hclosed hpublished) hresult
  rcases rightResult with ⟨rightValue, rightCache⟩
  rcases hrelation with hclean | hdoomed
  · exact ⟨hclean.1, hclean.2.2.1.2.1.valuesConsistent, hclean.2.2.1.2.2.1⟩
  · exact ⟨hdoomed.1, hdoomed.2.1, hdoomed.2.2.1⟩

theorem successfulDigestRun_changeSecretKey
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {left right : SecretKey} {message : Message} {randomness : Randomness}
    {index : Index} {leaves : DigestTree → FtsLeaf}
    (hrun : SuccessfulDigestRun f cache left message randomness index leaves)
    (hparameter : left.parameter = right.parameter) (hroot : left.root = right.root) :
    SuccessfulDigestRun f cache right message randomness index leaves := by
  simpa only [SuccessfulDigestRun, signAttempt, hparameter, hroot] using hrun

theorem simulateQ_randomOracle_cache_le_resolved
    (computation : OracleComp HashSpec alpha) (initial final : QueryCache HashSpec)
    (value : alpha)
    (hresult : (value, final) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run initial)) :
    initial ≤ final := by
  exact OracleComp.simulateQ_run_preservesInv
    (randomOracle : QueryImpl HashSpec _)
    (fun cache => initial ≤ cache)
    (QueryImpl.PreservesInv.withCaching_le uniformSampleImpl initial)
    computation initial le_rfl (value, final) hresult

set_option maxHeartbeats 1000000 in
theorem maskedPublishedChronologicalSign_support
    (initial : Coordinate → Prop)
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (completion : Coordinate → HashOutput)
    (fallback : QueryImpl HashSpec Id)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hallowed : RevealedChainAllowed initial context.state)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)))
    (hcompletion : DeferredCompletion table result.context completion)
    (hfallback : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback) :
    (result.value.1 = none ∧
        RevealedChainAllowed initial result.context.state) ∨
      ∃ (signature : Signature) (index : Index) (leaves : DigestTree → FtsLeaf)
          (parts : Layer → ChronologicalLayerPart),
        result.value.1 = some signature ∧
          SuccessfulDigestRun
            (tableAnswer parameter completion fallback)
            (ordinaryQueryCache result.value.2)
            (⟨parameter, root,
              fun lay tree leafIdx chainIdx =>
                truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
              ftsSecret⟩ : SecretKey)
            message signature.randomness index leaves ∧
          signature.counter = (fun lay => (parts lay).counter) ∧
          HonestLayerParts
            (tableAnswer parameter completion fallback)
            (⟨parameter, root,
              fun lay tree leafIdx chainIdx =>
                truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
              ftsSecret⟩ : SecretKey)
            index (fun lay => ((parts lay).counter, (parts lay).encoding)) ∧
          LayerEncodingsCached (ordinaryQueryCache result.value.2)
            (tableAnswer parameter completion fallback)
            (⟨parameter, root,
              fun lay tree leafIdx chainIdx =>
                truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
              ftsSecret⟩ : SecretKey)
            index (fun lay => ((parts lay).counter, (parts lay).encoding)) ∧
          RevealedChainAllowed
            (fun coordinate => initial coordinate ∨
              PublishedByParts index
                (fun lay => ((parts lay).counter, (parts lay).encoding)) coordinate)
            result.context.state := by
  let digestSecretKey : SecretKey :=
    ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩
  unfold maskedPublishedChronologicalSign at hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨loopOption, hloop, hrest⟩ := hresult
  cases loopOption with
  | none => simp at hrest
  | some loopResult =>
      have hloopCore := resolvedCore_of_mem_runResolvedFromTable
        ((simulateQ ordinaryRomImpl
          (signDigestLoop digestAttemptLimit digestSecretKey message)).run cache)
        context fuel table loopResult hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hloop
      simp only at hrest
      rw [hloopCore.1] at hrest
      cases selected : loopResult.value.1 with
      | none =>
          simp [selected, runResolvedFromTable] at hrest
          subst result
          have hloopRevealed := revealed_eq_of_mem_runResolvedFromTable_of_noPublish
            ((simulateQ ordinaryRomImpl
              (signDigestLoop digestAttemptLimit digestSecretKey message)).run cache)
            context fuel table loopResult
              (noPublish_simulateQ_ordinaryRomImpl
                (signDigestLoop digestAttemptLimit digestSecretKey message) cache) hloop
          apply Or.inl
          refine ⟨rfl, ?_⟩
          intro coordinate hchain hrevealed
          apply hallowed coordinate hchain
          rw [← hloopRevealed]
          exact hrevealed
      | some selectedValue =>
          rcases selectedValue with ⟨randomness, index, leaves⟩
          have hloopCompletion : DeferredCompletion table loopResult.context completion :=
            hcompletion.of_mem_runResolvedFromTable
              ((maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index
                leaves).run loopResult.value.2)
              loopResult.context loopResult.remaining table result completion hloopCore.2.1
                hloopCore.2.2 (by simpa [selected] using hrest)
          obtain ⟨loopConcreteCache, hloopInvariant, hloopClosed, hloopPublished,
              _hloopConcrete⟩ :=
            concreteSupport_of_mem_runResolved_signDigestLoop table digestSecretKey message
              digestAttemptLimit context fuel cache concreteCache loopResult completion hinvariant
                hclosed hpublished hloop hloopCompletion
          have hloopRevealed := revealed_eq_of_mem_runResolvedFromTable_of_noPublish
            ((simulateQ ordinaryRomImpl
              (signDigestLoop digestAttemptLimit digestSecretKey message)).run cache)
            context fuel table loopResult
              (noPublish_simulateQ_ordinaryRomImpl
                (signDigestLoop digestAttemptLimit digestSecretKey message) cache) hloop
          have hloopAllowed : RevealedChainAllowed initial loopResult.context.state := by
            intro coordinate hchain hrevealed
            apply hallowed coordinate hchain
            rw [← hloopRevealed]
            exact hrevealed
          have hafterSupport : some result ∈ support
              (runResolvedFromTable loopResult.context loopResult.remaining table
                ((maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness
                  index leaves).run loopResult.value.2)) := by
            simpa [selected] using hrest
          obtain ⟨afterConcreteCache, hafterInvariant, _hafterClosed, _hafterPublished,
              hafterConcrete⟩ :=
            concreteSupport_of_mem_runResolved_maskedPublishedChronologicalSignAfterDigest
              parameter table ftsSecret randomness index leaves loopResult.context
                loopResult.remaining loopResult.value.2 loopConcreteCache result completion
                  hloopInvariant hloopClosed hloopPublished hafterSupport hcompletion
          have hafter := maskedPublishedChronologicalSignAfterDigest_support initial parameter root
            table ftsSecret randomness index leaves loopResult.context loopResult.remaining
              loopResult.value.2 loopConcreteCache result completion fallback hloopInvariant
                hloopClosed hloopPublished hloopAllowed hafterSupport hcompletion hfallback
          rcases hafter with ⟨hnone, hfinalAllowed⟩ |
              ⟨signature, parts, hsignature, _hrandomness, hcounter, hhonest,
                hcachedEncodings, hfinalAllowed⟩
          · exact Or.inl ⟨hnone, hfinalAllowed⟩
          · let answer := tableAnswer parameter completion fallback
            have hafterAgrees : afterConcreteCache.AgreesWithFn answer :=
              hafterInvariant.concreteCache_agreesWith_tableAnswer_of_fallback completion
                hcompletion fallback hfallback
            have hafterConcrete' : (result.value.1, afterConcreteCache) ∈ support
                ((simulateQ (randomOracle : QueryImpl HashSpec _)
                  (signAfterDigest
                    (⟨parameter, root,
                      fun lay tree leafIdx chainIdx =>
                        truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
                      ftsSecret⟩ : SecretKey)
                    randomness index leaves)).run loopConcreteCache) := by
              rw [resolvedImmediateSignAfterDigest_eq_concrete parameter root table ftsSecret
                randomness index leaves,
                concreteSignAfterDigestFromTable_eq_signAfterDigest parameter root table ftsSecret
                  randomness index leaves] at hafterConcrete
              exact hafterConcrete
            have hloopLe : loopConcreteCache ≤ afterConcreteCache :=
              simulateQ_randomOracle_cache_le_resolved
                (signAfterDigest
                  (⟨parameter, root,
                    fun lay tree leafIdx chainIdx =>
                      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
                    ftsSecret⟩ : SecretKey)
                  randomness index leaves)
                loopConcreteCache afterConcreteCache result.value.1 hafterConcrete'
            have hloopAgrees : loopConcreteCache.AgreesWithFn answer :=
              fun input output hcached => hafterAgrees (hloopLe hcached)
            have hloopConcrete :
                (some (randomness, index, leaves), loopConcreteCache) ∈ support
                  ((simulateQ romImpl
                    (signDigestLoop digestAttemptLimit digestSecretKey message)).run
                    concreteCache) := by
              simpa [selected] using _hloopConcrete
            have hloopReplay := replayRom_of_mem_support
              (signDigestLoop digestAttemptLimit digestSecretKey message) concreteCache
                (some (randomness, index, leaves)) loopConcreteCache hloopConcrete answer
                  hloopAgrees
            have hdigest := successfulDigestLoop_of_mem_support answer digestSecretKey message
              digestAttemptLimit randomness index leaves concreteCache loopConcreteCache
                afterConcreteCache hloopReplay hloopLe hafterAgrees
            have hdigest' := successfulDigestRun_changeSecretKey hdigest
              (right := (⟨parameter, root,
                fun lay tree leafIdx chainIdx =>
                  truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
                ftsSecret⟩ : SecretKey))
              rfl rfl
            rw [← _hrandomness] at hdigest'
            have hdigestLeft : SuccessfulDigestRun answer
                (ordinaryQueryCache result.value.2)
                (⟨parameter, root,
                  fun lay tree leafIdx chainIdx =>
                    truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
                  ftsSecret⟩ : SecretKey)
                message signature.randomness index leaves := by
              refine ⟨hdigest'.1, hdigest'.2.1, ?_⟩
              intro input hinput
              have hstable := queriesStable_signAttempt answer
                (⟨parameter, root,
                  fun lay tree leafIdx chainIdx =>
                    truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
                  ftsSecret⟩ : SecretKey)
                message signature.randomness input hinput
              rw [hafterInvariant.2.2.2.2.eq_of_stable
                hafterInvariant.2.2.2.1 input hstable]
              exact hdigest'.2.2 input hinput
            exact Or.inr
              ⟨signature, index, leaves, parts, hsignature, hdigestLeft,
                hcounter, hhonest, hcachedEncodings, hfinalAllowed⟩

theorem revealedChainAllowed_maskedPublishedChronologicalSign_covered
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (targetCache : QueryCache HashSpec) (signingLog : QueryLog SigningSpec)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (completion : Coordinate → HashOutput)
    (fallback : QueryImpl HashSpec Id)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hallowed : RevealedChainAllowed
      (CoveredChainCoordinate
        (tableAnswer parameter completion fallback)
        targetCache
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        signingLog)
      context.state)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)))
    (hcompletion : DeferredCompletion table result.context completion)
    (hfallback : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback)
    (hentry : (⟨message, result.value.1⟩ :
      (request : SignRequest) × SigningSpec.Range request) ∈ signingLog)
    (hrun : ∀ signature, result.value.1 = some signature →
      SuccessfulSignRun
        (tableAnswer parameter completion fallback)
        targetCache
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        message signature) :
    RevealedChainAllowed
      (CoveredChainCoordinate
        (tableAnswer parameter completion fallback)
        targetCache
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        signingLog)
      result.context.state := by
  let answer := tableAnswer parameter completion fallback
  let secretKey : SecretKey :=
    ⟨parameter, root,
      fun lay tree leafIdx chainIdx =>
        truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
      ftsSecret⟩
  have hclassified := maskedPublishedChronologicalSign_support
    (CoveredChainCoordinate answer targetCache secretKey signingLog)
    parameter root table ftsSecret message context fuel cache concreteCache result completion
      fallback hinvariant hclosed hpublished hallowed hresult hcompletion hfallback
  rcases hclassified with ⟨_, hfinal⟩ |
      ⟨signature, index, leaves, parts, hsignature, hdigest, hcounter,
        hhonest, _hcachedEncodings, hfinal⟩
  · exact hfinal
  · change RevealedChainAllowed
      (CoveredChainCoordinate answer targetCache secretKey signingLog) result.context.state
    refine hfinal.mono
      (final := CoveredChainCoordinate answer targetCache secretKey signingLog) ?_
    intro coordinate hcoordinate
    rcases hcoordinate with hcovered | hpublishedCoordinate
    · exact hcovered
    · have hrun' : SuccessfulSignRun answer targetCache secretKey message signature :=
        hrun signature hsignature
      obtain ⟨runIndex, runLeaves, runParts, hrunDigest, hftsSecret, hftsPath,
          hrunCounter, hrunValues, hrunPath, hftsCached, hlayers, hlayersCached⟩ := hrun'
      have hselected : (index, leaves) = (runIndex, runLeaves) :=
        Option.some.inj (hdigest.2.1.symm.trans hrunDigest.2.1)
      obtain ⟨hindex, hleaves⟩ := Prod.mk.inj hselected
      subst runIndex
      subst runLeaves
      exact (hpublishedCoordinate.toPublishedChainCoordinate
        ⟨message, result.value.1⟩ signature leaves hentry hsignature
          (hrun signature hsignature) hrunDigest hcounter hhonest).covered

theorem revealedChainAllowed_maskedChronologicalExpandedAdversaryQuery
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (targetCache : QueryCache HashSpec) (allowedLog : QueryLog SigningSpec)
    (completion : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id)
    (hlogRuns : ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ allowedLog → entry.2 = some signature →
        SuccessfulSignRun (tableAnswer parameter completion fallback) targetCache
          (⟨parameter, root,
            fun lay tree leafIdx chainIdx =>
              truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey)
          entry.1 signature)
    (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult
      ((OracleWorld + SigningSpec).Range input × SplitHashCache))
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hallowed : RevealedChainAllowed
      (CoveredChainCoordinate (tableAnswer parameter completion fallback) targetCache
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        allowedLog)
      context.state)
    (hfragment : ∀ entry, entry ∈ signingLogFragment input result.value.1 →
      entry ∈ allowedLog)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)))
    (hcompletion : DeferredCompletion table result.context completion)
    (hfallback : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback) :
    RevealedChainAllowed
      (CoveredChainCoordinate (tableAnswer parameter completion fallback) targetCache
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        allowedLog)
      result.context.state := by
  cases input with
  | inl query =>
      exact resolvedPreservesChainPublication_probingRomImpl
        (CoveredChainCoordinate (tableAnswer parameter completion fallback) targetCache
          (⟨parameter, root,
            fun lay tree leafIdx chainIdx =>
              truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey)
          allowedLog)
        parameter
        (coveredChainCoordinate_forwardClosed (tableAnswer parameter completion fallback)
          targetCache
          (⟨parameter, root,
            fun lay tree leafIdx chainIdx =>
              truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey)
          allowedLog)
        query context cache fuel table result completion hinvariant.2.1.valuesConsistent
          hinvariant.2.2.1 hallowed hresult hcompletion
  | inr message =>
      apply revealedChainAllowed_maskedPublishedChronologicalSign_covered parameter root table
        ftsSecret message targetCache allowedLog context fuel cache concreteCache result completion
          fallback hinvariant hclosed hpublished hallowed hresult hcompletion hfallback
      · exact hfragment ⟨message, result.value.1⟩ (by simp [signingLogFragment])
      · intro signature hsignature
        exact hlogRuns ⟨message, result.value.1⟩ signature
          (hfragment _ (by simp [signingLogFragment])) hsignature

set_option maxRecDepth 100000 in
theorem revealedChainAllowed_signingTraceComputation
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (targetCache : QueryCache HashSpec) (allowedLog : QueryLog SigningSpec)
    (completion : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id)
    (hlogRuns : ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ allowedLog → entry.2 = some signature →
        SuccessfulSignRun (tableAnswer parameter completion fallback) targetCache
          (⟨parameter, root,
            fun lay tree leafIdx chainIdx =>
              truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey)
          entry.1 signature)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult ((alpha × QueryLog SigningSpec) × SplitHashCache))
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hallowed : RevealedChainAllowed
      (CoveredChainCoordinate (tableAnswer parameter completion fallback) targetCache
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        allowedLog)
      context.state)
    (hsub : ∀ entry, entry ∈ result.value.1.2 → entry ∈ allowedLog)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
          (signingTraceComputation computation)).run cache)))
    (hcompletion : DeferredCompletion table result.context completion)
    (hfallback : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback) :
    RevealedChainAllowed
      (CoveredChainCoordinate (tableAnswer parameter completion fallback) targetCache
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        allowedLog)
      result.context.state := by
  induction computation using OracleComp.inductionOn generalizing
      context fuel cache concreteCache result with
  | pure value =>
      simp [signingTraceComputation, runResolvedFromTable] at hresult
      subst result
      exact hallowed
  | query_bind input next ih =>
      rw [signingTraceComputation_query_bind, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
      obtain ⟨queryOption, hquery, hrest⟩ := hresult
      cases queryOption with
      | none => simp at hrest
      | some queryResult =>
          have hqueryCore := resolvedCore_of_mem_runResolvedFromTable
            ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
            context fuel table queryResult hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hquery
          simp only at hrest
          rw [hqueryCore.1, map_eq_bind_pure_comp, simulateQ_bind, StateT.run_bind,
            runResolvedFromTable_bind, mem_support_bind_iff] at hrest
          obtain ⟨tailOption, htail, hfinish⟩ := hrest
          cases tailOption with
          | none => simp at hfinish
          | some tailResult =>
              simp [runResolvedFromTable] at hfinish
              subst result
              have htailCore := resolvedCore_of_mem_runResolvedFromTable
                ((simulateQ
                  (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
                  (signingTraceComputation (next queryResult.value.1))).run
                    queryResult.value.2)
                queryResult.context queryResult.remaining table tailResult
                  hqueryCore.2.1 hqueryCore.2.2 htail
              have hqueryCompletion : DeferredCompletion table queryResult.context completion :=
                hcompletion.of_mem_runResolvedFromTable _ queryResult.context
                  queryResult.remaining table tailResult completion hqueryCore.2.1 hqueryCore.2.2
                    htail
              obtain ⟨queryConcreteCache, hqueryInvariant, hqueryClosed, hqueryPublished,
                  _hqueryConcrete⟩ :=
                concreteSupport_of_mem_runResolved_of_reachableResolvedCouples
                  (reachableResolvedCouples_maskedChronologicalExpandedAdversaryImpl parameter
                    root table ftsSecret input)
                  hinvariant hclosed hpublished hquery hqueryCompletion
              let secretKey : SecretKey :=
                ⟨parameter, root,
                  fun lay tree leafIdx chainIdx =>
                    truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
                  ftsSecret⟩
              have htailCoupled : ReachableResolvedCouples parameter table
                  (simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
                    (signingTraceComputation (next queryResult.value.1)))
                  (simulateQ (unloggedMappedAdversaryImpl secretKey)
                    (signingTraceComputation (next queryResult.value.1))) :=
                reachableResolvedCouples_simulateQ
                  (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
                  (unloggedMappedAdversaryImpl secretKey)
                  (reachableResolvedCouples_maskedChronologicalExpandedAdversaryImpl parameter
                    root table ftsSecret)
                  (signingTraceComputation (next queryResult.value.1))
              have hqueryFallback : CacheAgreesWithFnOffTable parameter completion
                  (ordinaryQueryCache queryResult.value.2) fallback :=
                CacheAgreesWithFnOffTable.of_reachableResolvedCouples htailCoupled
                  hqueryInvariant hqueryClosed hqueryPublished htail hcompletion hfallback
                    (fun value finalCache hright =>
                      FtsProbeSimulation.simulateQ_unloggedMappedAdversaryImpl_cache_le secretKey
                        (signingTraceComputation (next queryResult.value.1)) queryConcreteCache
                          finalCache value hright)
              have hqueryAllowed :=
                revealedChainAllowed_maskedChronologicalExpandedAdversaryQuery parameter root
                  table ftsSecret targetCache allowedLog completion fallback hlogRuns input
                    context fuel cache concreteCache queryResult hinvariant hclosed hpublished
                      hallowed
                      (fun entry hentry => hsub entry
                        (List.mem_append_left tailResult.value.1.2 hentry))
                      hquery hqueryCompletion hqueryFallback
              apply ih queryResult.value.1 queryResult.context queryResult.remaining
                queryResult.value.2 queryConcreteCache tailResult hqueryInvariant hqueryClosed
                  hqueryPublished hqueryAllowed
              · intro entry hentry
                exact hsub entry (List.mem_append_right _ hentry)
              · exact htail
              · exact hcompletion
              · exact hfallback

theorem reachableResolvedCouples_probingHashImpl_query
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) :
    ReachableResolvedCouples parameter table (probingHashImpl parameter input)
      (randomOracle input) :=
  reachableResolvedCouples_probingHashQuery parameter table input

theorem resolvedPreservesChainPublication_probingHashImpl_query
    (allowed : Coordinate → Prop) (parameter : PublicParameter)
    (input : HashInput) (hforward : ChainForwardClosed allowed) :
    ResolvedPreservesChainPublication allowed (probingHashImpl parameter input) :=
  resolvedPreservesChainPublication_probingHashQuery allowed parameter input hforward

theorem DeferredCompletion.not_probeHits_of_probingHashImpl_query_chain
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
        ((probingHashImpl parameter input).run cache)))
    (hcompletion : DeferredCompletion table result.context completion)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ¬probe.Hits (tableAnswer parameter completion fallback)
      parameter (tableOtsSecret completion) ftsSecret :=
  hcompletion.not_probeHits_of_probingHashQuery_chain fallback hconsistent hstarts hmatches
    hposition hnotRevealed hresult ftsSecret

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem not_probeHits_of_mem_runResolved_probingHashImpl
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (allowed : Coordinate → Prop) (hforward : ChainForwardClosed allowed)
    (completion : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec alpha)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult (alpha × SplitHashCache))
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hallowed : RevealedChainAllowed allowed context.state)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((simulateQ (probingHashImpl parameter) computation).run cache)))
    (hcompletion : DeferredCompletion table result.context completion)
    (hfallback : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback)
    (probe : Probe) (input : HashInput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep)
    (hmatches : probe.MatchesInput parameter input)
    (hposition : decodePosition? parameter input =
      some (.chain lay tree leafIdx chainIdx step))
    (hnotAllowed : ¬allowed probe.coordinate)
    (hquery : input ∈ queriedInputs
      (tableAnswer parameter completion fallback) computation)
    (hhits : probe.Hits (tableAnswer parameter completion fallback)
      parameter (tableOtsSecret completion) ftsSecret) : False := by
  induction computation using OracleComp.inductionOn generalizing
      context fuel cache concreteCache result with
  | pure value =>
      simp at hquery
  | query_bind queried next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, runResolvedFromTable_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨queryOption, hqueryRun, hrest⟩ := hresult
      cases queryOption with
      | none => simp at hrest
      | some queryResult =>
          have hqueryRun' : some queryResult ∈ support
              (runResolvedFromTable context fuel table
                ((probingHashImpl parameter queried).run cache)) := hqueryRun
          have hqueryCore : queryResult.table = table ∧
              queryResult.context.ValuesConsistent ∧
              StartTableAgrees queryResult.context.state table :=
            resolvedCore_of_mem_runResolved_of_reachableResolvedCouples
              (reachableResolvedCouples_probingHashImpl_query parameter table queried)
              hinvariant hclosed hpublished hqueryRun'
          simp only at hrest
          rw [hqueryCore.1] at hrest
          have hqueryCompletion : DeferredCompletion table queryResult.context completion :=
            hcompletion.of_mem_runResolvedFromTable
              ((simulateQ (probingHashImpl parameter) (next queryResult.value.1)).run
                queryResult.value.2)
              queryResult.context queryResult.remaining table result completion hqueryCore.2.1
                hqueryCore.2.2 hrest
          obtain ⟨queryConcreteCache, hqueryInvariant, hqueryClosed, hqueryPublished,
              hqueryConcrete⟩ :=
            concreteSupport_of_mem_runResolved_of_reachableResolvedCouples
              (reachableResolvedCouples_probingHashImpl_query parameter table queried)
              hinvariant hclosed hpublished hqueryRun' hqueryCompletion
          have htailCoupled : ReachableResolvedCouples parameter table
              (simulateQ (probingHashImpl parameter) (next queryResult.value.1))
              (simulateQ randomOracle (next queryResult.value.1)) :=
            reachableResolvedCouples_simulateQ (probingHashImpl parameter) randomOracle
              (reachableResolvedCouples_probingHashQuery parameter table)
              (next queryResult.value.1)
          have hqueryFallback : CacheAgreesWithFnOffTable parameter completion
              (ordinaryQueryCache queryResult.value.2) fallback :=
            CacheAgreesWithFnOffTable.of_reachableResolvedCouples htailCoupled
              hqueryInvariant hqueryClosed hqueryPublished hrest hcompletion hfallback
                (fun value finalCache hright =>
                  simulateQ_randomOracle_cache_le_resolved (next queryResult.value.1)
                    queryConcreteCache finalCache value hright)
          have hqueryAllowed : RevealedChainAllowed allowed queryResult.context.state :=
            resolvedPreservesChainPublication_probingHashImpl_query allowed parameter queried
              hforward
              context cache fuel table queryResult completion
                hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hallowed hqueryRun'
                  hqueryCompletion
          have hagrees : queryConcreteCache.AgreesWithFn
              (tableAnswer parameter completion fallback) :=
            hqueryInvariant.concreteCache_agreesWith_tableAnswer_of_fallback
              completion hqueryCompletion fallback hqueryFallback
          have hcached : queryConcreteCache queried = some queryResult.value.1 :=
            randomOracle_run_output_cached queried concreteCache queryConcreteCache
              queryResult.value.1 hqueryConcrete
          have hanswer : tableAnswer parameter completion fallback queried =
              queryResult.value.1 := hagrees hcached
          rw [queriedInputs_query_bind, hanswer] at hquery
          rcases List.mem_cons.mp hquery with hhead | htail
          · subst queried
            have hnotRevealed : probe.coordinate ∉ context.state.revealed := by
              intro hrevealed
              exact hnotAllowed
                (hallowed probe.coordinate (probe.isChainCoordinate_of_matchesInput hmatches)
                  hrevealed)
            exact (hqueryCompletion.not_probeHits_of_probingHashImpl_query_chain fallback
              hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hmatches hposition hnotRevealed
                hqueryRun' ftsSecret) hhits
          · exact ih queryResult.value.1 queryResult.context queryResult.remaining
              queryResult.value.2 queryConcreteCache result hqueryInvariant hqueryClosed
                hqueryPublished hqueryAllowed hrest hcompletion hfallback htail

set_option maxRecDepth 100000 in
theorem not_verifyProbe_of_mem_runResolved_verifier
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (targetCache : QueryCache HashSpec) (root : Digest) (forgery : Forgery)
    (signingLog : QueryLog SigningSpec)
    (completion : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult (Bool × SplitHashCache))
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hallowed : RevealedChainAllowed
      (CoveredChainCoordinate
        (tableAnswer parameter completion fallback) targetCache
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        signingLog)
      context.state)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((simulateQ (probingRomImpl parameter)
          (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run cache)))
    (hcompletion : DeferredCompletion table result.context completion)
    (hfallback : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback)
    (hprobe : VerifyProbeWitness
      (tableAnswer parameter completion fallback) targetCache
      (⟨parameter, root,
        fun lay tree leafIdx chainIdx =>
          truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
        ftsSecret⟩ : SecretKey)
      signingLog forgery.message forgery.signature) : False := by
  obtain ⟨lay, digest, layerMessage, codeword, chainIdx, hdigit, probe, input, hinput,
      _hdigest, _hadmissible, _hencode, _hverifierMessage, hhits, hmatches, hquery,
      _hcached, hnotCovered⟩ := hprobe
  have hposition : decodePosition? parameter input =
      some (.chain lay (treeIndexAt (digestIndex digest) lay)
        (leafIndexAt (digestIndex digest) lay) chainIdx
          ⟨(codeword chainIdx).val, hdigit⟩) :=
    (decodePosition?_eq_some_iff parameter input _).2
      ⟨digestBytes (forgery.signature.chainValue lay chainIdx), hinput⟩
  have hresult' : some result ∈ support
      (runResolvedFromTable context fuel table
        ((simulateQ (probingHashImpl parameter)
          (verify ⟨root, parameter⟩ forgery.message forgery.signature)).run cache)) := by
    rw [← simulateQ_probingRom_scheme_verify]
    exact hresult
  have hhits' : probe.Hits (tableAnswer parameter completion fallback)
      parameter (tableOtsSecret completion) ftsSecret := by
    rw [hcompletion.tableOtsSecret_eq]
    exact hhits
  exact not_probeHits_of_mem_runResolved_probingHashImpl parameter table ftsSecret
    (CoveredChainCoordinate
      (tableAnswer parameter completion fallback) targetCache
      (⟨parameter, root,
        fun selectedLay selectedTree selectedLeaf selectedChain =>
          truncateHash (table ⟨selectedLay, selectedTree, selectedLeaf, selectedChain⟩),
        ftsSecret⟩ : SecretKey)
      signingLog)
    (coveredChainCoordinate_forwardClosed (tableAnswer parameter completion fallback)
      targetCache
      (⟨parameter, root,
        fun selectedLay selectedTree selectedLeaf selectedChain =>
          truncateHash (table ⟨selectedLay, selectedTree, selectedLeaf, selectedChain⟩),
        ftsSecret⟩ : SecretKey)
      signingLog)
    completion fallback (verify ⟨root, parameter⟩ forgery.message forgery.signature)
      context fuel cache concreteCache result hinvariant hclosed hpublished hallowed hresult'
        hcompletion hfallback probe input lay (treeIndexAt (digestIndex digest) lay)
          (leafIndexAt (digestIndex digest) lay) chainIdx
            ⟨(codeword chainIdx).val, hdigit⟩ hmatches hposition hnotCovered hquery hhits'

theorem not_uncoveredChainProbe_of_mem_runResolved_verifier
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (targetCache : QueryCache HashSpec) (root : Digest) (forgery : Forgery)
    (signingLog : QueryLog SigningSpec)
    (completion : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult (Bool × SplitHashCache))
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hallowed : RevealedChainAllowed
      (CoveredChainCoordinate
        (tableAnswer parameter completion fallback) targetCache
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        signingLog)
      context.state)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((simulateQ (probingRomImpl parameter)
          (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run cache)))
    (hcompletion : DeferredCompletion table result.context completion)
    (hfallback : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback)
    (probe : Probe) (input : HashInput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep)
    (hmatches : probe.MatchesInput parameter input)
    (hposition : decodePosition? parameter input =
      some (.chain lay tree leafIdx chainIdx step))
    (hnotCovered : ¬CoveredChainCoordinate
      (tableAnswer parameter completion fallback) targetCache
      (⟨parameter, root,
        fun selectedLay selectedTree selectedLeaf selectedChain =>
          truncateHash (table ⟨selectedLay, selectedTree, selectedLeaf, selectedChain⟩),
        ftsSecret⟩ : SecretKey)
      signingLog probe.coordinate)
    (hquery : input ∈ queriedInputs (tableAnswer parameter completion fallback)
      (verify ⟨root, parameter⟩ forgery.message forgery.signature))
    (hhits : probe.Hits (tableAnswer parameter completion fallback)
      parameter (tableOtsSecret completion) ftsSecret) : False := by
  have hresult' : some result ∈ support
      (runResolvedFromTable context fuel table
        ((simulateQ (probingHashImpl parameter)
          (verify ⟨root, parameter⟩ forgery.message forgery.signature)).run cache)) := by
    rw [← simulateQ_probingRom_scheme_verify]
    exact hresult
  exact not_probeHits_of_mem_runResolved_probingHashImpl parameter table ftsSecret
    (CoveredChainCoordinate
      (tableAnswer parameter completion fallback) targetCache
      (⟨parameter, root,
        fun selectedLay selectedTree selectedLeaf selectedChain =>
          truncateHash (table ⟨selectedLay, selectedTree, selectedLeaf, selectedChain⟩),
        ftsSecret⟩ : SecretKey)
      signingLog)
    (coveredChainCoordinate_forwardClosed (tableAnswer parameter completion fallback)
      targetCache
      (⟨parameter, root,
        fun selectedLay selectedTree selectedLeaf selectedChain =>
          truncateHash (table ⟨selectedLay, selectedTree, selectedLeaf, selectedChain⟩),
        ftsSecret⟩ : SecretKey)
      signingLog)
    completion fallback (verify ⟨root, parameter⟩ forgery.message forgery.signature)
      context fuel cache concreteCache result hinvariant hclosed hpublished hallowed hresult'
        hcompletion hfallback probe input lay tree leafIdx chainIdx step hmatches hposition
          hnotCovered hquery hhits

set_option maxHeartbeats 1000000 in
theorem resolvedPreservesChainPublication_maskedPublishedTreeRoot
    (allowed : Coordinate → Prop) :
    ResolvedPreservesChainPublication allowed maskedPublishedTreeRoot := by
  unfold maskedPublishedTreeRoot
  apply (ResolvedPreservesChainPublication.of_noPublish allowed
    (ensureTreeNode topLayer rootTree (layerHeight topLayer) 0) fun cache =>
      noPublish_ensureTreeNode topLayer rootTree (layerHeight topLayer) 0 cache).bind
  intro _
  exact resolvedPreservesChainPublication_revealPublishedCoordinate allowed _
    (by simp [IsChainCoordinate])

theorem successfulSignRuns_of_mem_support_unloggedMapped_signingTrace
    (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (initialCache : QueryCache HashSpec) (value : alpha)
    (signingLog : QueryLog SigningSpec) (adversaryCache finalCache : QueryCache HashSpec)
    (hmem : ((value, signingLog), adversaryCache) ∈ support
      ((simulateQ (unloggedMappedAdversaryImpl secretKey)
        (signingTraceComputation computation)).run initialCache))
    (hle : adversaryCache ≤ finalCache) (hf : finalCache.AgreesWithFn f) :
    ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ signingLog → entry.2 = some signature →
        SuccessfulSignRun f finalCache secretKey entry.1 signature := by
  rw [← simulateQ_withTraceAppend_run_eq_signingTraceComputation,
    ← FtsProbeSimulation.writerTMapBase_expanded_withTraceAppend_eq_unlogged,
    ← QueryImpl.simulateQ_writerTMapBase_run,
    ← SphincsSecurity.forwardOracles_add_signingOracle_eq_withTraceAppend] at hmem
  intro entry signature hentry hresponse
  exact successfulSignRun_of_signing_entry f secretKey computation initialCache value signingLog
    adversaryCache finalCache hmem hle hf entry signature hresponse hentry

theorem successfulSignRuns_of_mem_support_concreteRetainedPrefix
    (adversary : Adversary) (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (initialCache : QueryCache HashSpec) (root : Digest) (forgery : Forgery)
    (signingLog : QueryLog SigningSpec) (prefixCache finalCache : QueryCache HashSpec)
    (hmem : ((root, (forgery, signingLog)), prefixCache) ∈ support
      ((concreteRetainedPrefixAfterFtsSecrets adversary parameter table ftsSecret).run
        initialCache))
    (hle : prefixCache ≤ finalCache) (hf : finalCache.AgreesWithFn f) :
    ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ signingLog → entry.2 = some signature →
        SuccessfulSignRun f finalCache
          (⟨parameter, root,
            fun lay tree leafIdx chainIdx =>
              truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey)
          entry.1 signature := by
  unfold concreteRetainedPrefixAfterFtsSecrets at hmem
  rw [StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨rootResult, hroot, hrest⟩ := hmem
  rcases rootResult with ⟨sampledRoot, rootCache⟩
  rw [StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨adversaryResult, hadversary, hfinish⟩ := hrest
  rcases adversaryResult with ⟨forgeryLog, adversaryCache⟩
  rcases forgeryLog with ⟨sampledForgery, sampledLog⟩
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfinish
  obtain ⟨hvalue, hcache⟩ := hfinish
  subst adversaryCache
  obtain ⟨hrootValue, hforgeryLog⟩ := hvalue
  subst sampledRoot
  obtain ⟨hforgery, hlog⟩ := hforgeryLog
  subst sampledForgery
  subst sampledLog
  exact successfulSignRuns_of_mem_support_unloggedMapped_signingTrace f
    (⟨parameter, root,
      fun lay tree leafIdx chainIdx =>
        truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
      ftsSecret⟩ : SecretKey)
    (adversary.main ⟨root, parameter⟩) rootCache forgery signingLog prefixCache finalCache
      hadversary hle hf

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxHeartbeats 1000000 in
theorem resolvedCore_of_mem_runResolved_maskedPublishedTreeRoot
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (fuel : Nat)
    (result : ResolvedRunResult (Digest × SplitHashCache))
    (hresult : some result ∈ support
      (runResolvedFromTable
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    result.table = table ∧ result.context.ValuesConsistent ∧
      StartTableAgrees result.context.state table :=
  resolvedCore_of_mem_runResolved_of_reachableResolvedCouples
    (reachableResolvedCouples_maskedPublishedTreeRoot parameter table)
    (resolvedContextInvariant_empty parameter table)
    (visibleResolvedComputationsCached_empty parameter table emptyDeferredStructuralValues ∅)
    publishedValues_empty hresult

set_option maxHeartbeats 1000000 in
theorem concreteSupport_of_mem_runResolved_maskedPublishedTreeRoot
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (fuel : Nat)
    (result : ResolvedRunResult (Digest × SplitHashCache))
    (completion : Coordinate → HashOutput)
    (hresult : some result ∈ support
      (runResolvedFromTable
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)))
    (hcompletion : DeferredCompletion table result.context completion) :
    ∃ concreteCache,
      ResolvedContextInvariant parameter table result.context
        (ordinaryQueryCache result.value.2) concreteCache ∧
      VisibleResolvedComputationsCached parameter table result.context concreteCache ∧
      PublishedValues result.context.state ∧
      (result.value.1, concreteCache) ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (treeNode parameter topLayer rootTree
            (fun leafIdx chainIdx =>
              truncateHash (table ⟨topLayer, rootTree, leafIdx, chainIdx⟩))
            (layerHeight topLayer) 0)).run ∅) :=
  concreteSupport_of_mem_runResolved_of_reachableResolvedCouples
    (reachableResolvedCouples_maskedPublishedTreeRoot parameter table)
    (resolvedContextInvariant_empty parameter table)
    (visibleResolvedComputationsCached_empty parameter table emptyDeferredStructuralValues ∅)
    publishedValues_empty hresult hcompletion

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem revealedChainAllowed_of_mem_runResolved_chronologicalRetainedPrefix
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (targetCache : QueryCache HashSpec)
    (completion : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id)
    (fuel : Nat)
    (result : ResolvedRunResult
      ((Digest × (Forgery × QueryLog SigningSpec)) × SplitHashCache))
    (hresult : some result ∈ support
      (runResolvedFromTable
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table
        ((maskedChronologicalRetainedPrefixAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache)))
    (hcompletion : DeferredCompletion table result.context completion)
    (hfallback : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback)
    (hlogRuns : ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ result.value.1.2.2 → entry.2 = some signature →
        SuccessfulSignRun (tableAnswer parameter completion fallback) targetCache
          (⟨parameter, result.value.1.1,
            fun lay tree leafIdx chainIdx =>
              truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey)
          entry.1 signature) :
    RevealedChainAllowed
      (CoveredChainCoordinate (tableAnswer parameter completion fallback) targetCache
        (⟨parameter, result.value.1.1,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        result.value.1.2.2)
      result.context.state := by
  unfold maskedChronologicalRetainedPrefixAfterFtsSecrets at hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨rootOption, hroot, hrest⟩ := hresult
  cases rootOption with
  | none => simp at hrest
  | some rootResult =>
      have hrootCore : rootResult.table = table ∧ rootResult.context.ValuesConsistent ∧
          StartTableAgrees rootResult.context.state table :=
        resolvedCore_of_mem_runResolved_maskedPublishedTreeRoot parameter table fuel rootResult
          hroot
      simp only at hrest
      rw [hrootCore.1] at hrest
      have hrootCompletion : DeferredCompletion table rootResult.context completion :=
        hcompletion.of_mem_runResolvedFromTable _ rootResult.context rootResult.remaining table
          result completion hrootCore.2.1 hrootCore.2.2 hrest
      obtain ⟨rootConcreteCache, hrootInvariant, hrootClosed, hrootPublished,
          _hrootConcrete⟩ :=
        concreteSupport_of_mem_runResolved_maskedPublishedTreeRoot parameter table fuel rootResult
          completion hroot hrootCompletion
      have hemptyAllowed : RevealedChainAllowed
          (CoveredChainCoordinate (tableAnswer parameter completion fallback) targetCache
            (⟨parameter, rootResult.value.1,
              fun lay tree leafIdx chainIdx =>
                truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
              ftsSecret⟩ : SecretKey)
            result.value.1.2.2)
          (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) := by
        intro coordinate hchain hrevealed
        simp [LazyRevealProbe.State.empty] at hrevealed
      have hrootAllowed : RevealedChainAllowed
          (CoveredChainCoordinate (tableAnswer parameter completion fallback) targetCache
            (⟨parameter, rootResult.value.1,
              fun lay tree leafIdx chainIdx =>
                truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
              ftsSecret⟩ : SecretKey)
            result.value.1.2.2)
          rootResult.context.state :=
        resolvedPreservesChainPublication_maskedPublishedTreeRoot _
          { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
            values := emptyDeferredStructuralValues }
          emptySplitHashCache fuel table rootResult completion
              (resolvedContextInvariant_empty parameter table).2.1.valuesConsistent
              (resolvedContextInvariant_empty parameter table).2.2.1 hemptyAllowed hroot
                hrootCompletion
      rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hrest
      obtain ⟨adversaryOption, hadversary, hfinish⟩ := hrest
      cases adversaryOption with
      | none => simp at hfinish
      | some adversaryResult =>
          simp [runResolvedFromTable] at hfinish
          subst result
          exact revealedChainAllowed_signingTraceComputation parameter rootResult.value.1 table
            ftsSecret targetCache adversaryResult.value.1.2 completion fallback hlogRuns
              (adversary.main ⟨rootResult.value.1, parameter⟩) rootResult.context
                rootResult.remaining rootResult.value.2 rootConcreteCache adversaryResult
                  hrootInvariant hrootClosed hrootPublished hrootAllowed (fun entry => id)
                    hadversary hcompletion hfallback

theorem successfulSignRuns_of_mem_support_actualRetainedGameAfterTable
    (adversary : Adversary) (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (root : Digest) (forgery : Forgery) (signingLog : QueryLog SigningSpec)
    (verified : Bool) (finalCache : QueryCache HashSpec)
    (hactual : ((root, ((forgery, signingLog), verified)), finalCache) ∈ support
      (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)))
    (hf : finalCache.AgreesWithFn f) :
    ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ signingLog → entry.2 = some signature →
        SuccessfulSignRun f finalCache
          (⟨parameter, root,
            fun lay tree leafIdx chainIdx =>
              truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey)
          entry.1 signature := by
  rw [← concreteRetainedGameAfterFtsSecrets_run_eq_actual] at hactual
  unfold concreteRetainedGameAfterFtsSecrets at hactual
  rw [StateT.run_bind, mem_support_bind_iff] at hactual
  obtain ⟨prefixResult, hprefix, hrest⟩ := hactual
  rcases prefixResult with ⟨prefixValue, prefixCache⟩
  rcases prefixValue with ⟨sampledRoot, forgeryLog⟩
  rcases forgeryLog with ⟨sampledForgery, sampledLog⟩
  rw [StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨verifierResult, hverifier, hfinish⟩ := hrest
  rcases verifierResult with ⟨sampledVerified, verifierCache⟩
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfinish
  obtain ⟨hvalue, hcache⟩ := hfinish
  subst verifierCache
  obtain ⟨hroot, hrestValue⟩ := hvalue
  subst sampledRoot
  obtain ⟨hforgeryLog, hverified⟩ := hrestValue
  subst sampledVerified
  obtain ⟨hforgery, hlog⟩ := hforgeryLog
  subst sampledForgery
  subst sampledLog
  have hle : prefixCache ≤ finalCache :=
    simulateQ_romImpl_cache_le
      (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)
      prefixCache (verified, finalCache) hverifier
  exact successfulSignRuns_of_mem_support_concreteRetainedPrefix adversary f parameter table
    ftsSecret ∅ root forgery signingLog prefixCache finalCache hprefix hle hf

theorem SuccessfulDigestRun.changeAnswerFn
    {f g : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {message : Message} {randomness : Randomness}
    {index : Index} {leaves : DigestTree → FtsLeaf}
    (hrun : SuccessfulDigestRun f cache secretKey message randomness index leaves)
    (hf : cache.AgreesWithFn f) (hg : cache.AgreesWithFn g) :
    SuccessfulDigestRun g cache secretKey message randomness index leaves := by
  refine ⟨hrun.1, ?_, hrun.2.2.changeAnswerFn hf hg⟩
  rw [← hrun.2.2.eval_eq hf hg]
  exact hrun.2.1

theorem SuccessfulSignRun.changeAnswerFn
    {f g : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {message : Message} {signature : Signature}
    (hrun : SuccessfulSignRun f cache secretKey message signature)
    (hf : cache.AgreesWithFn f) (hg : cache.AgreesWithFn g) :
    SuccessfulSignRun g cache secretKey message signature := by
  obtain ⟨index, leaves, parts, hdigest, hftsSecret, hftsPath, hcounter, hvalues,
      hauthPath, hftsCached, hlayers, hlayersCached⟩ := hrun
  refine ⟨index, leaves, parts, SuccessfulDigestRun.changeAnswerFn hdigest hf hg, hftsSecret,
    ?_, hcounter,
    hvalues, hauthPath, hftsCached.changeAnswerFn hf hg, ?_, ?_⟩
  · rw [← hftsCached.eval_eq hf hg]
    exact hftsPath
  · intro lay
    rw [← (hlayersCached lay).eval_eq hf hg]
    exact hlayers lay
  · intro lay
    exact (hlayersCached lay).changeAnswerFn hf hg

theorem CoveredChainCoordinate.changeAnswerFn
    {f g : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {coordinate : Coordinate}
    (hcovered : CoveredChainCoordinate f cache secretKey signingLog coordinate)
    (hf : cache.AgreesWithFn f) (hg : cache.AgreesWithFn g) :
    CoveredChainCoordinate g cache secretKey signingLog coordinate := by
  obtain ⟨entry, signature, index, leaves, lay, chainIdx, codeword, targetDigit, hentry,
      hresponse, hrun, hdigest, hencode, hle, hcoordinate⟩ := hcovered
  have hmessageCached : CachedRun cache f (layerMessage secretKey index lay) := by
    obtain ⟨runIndex, runLeaves, parts, runDigest, _hftsSecret, _hftsPath, _hcounter,
        _hvalues, _hauthPath, _hftsCached, _hlayers, hlayersCached⟩ := hrun
    have hselection : (runIndex, runLeaves) = (index, leaves) := by
      apply Option.some.inj
      exact runDigest.2.1.symm.trans hdigest.2.1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hselection
    exact (hlayersCached lay).bind_left
  have hmessageEq := hmessageCached.eval_eq hf hg
  have hencodingInputCached := hrun.signed_encode_cached_of_digest hdigest lay
  have hencodeCached : CachedRun cache f
      (encode secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage secretKey index lay))
        (signature.counter lay)) := by
    intro input hinput
    simp only [encode, queriedInputs_bind, queriedInputs_tweakableHash, queriedInputs_pure,
      List.append_nil, List.mem_singleton] at hinput
    subst input
    exact hencodingInputCached
  have hencode' : evalWithAnswerFn g
      (encode secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn g (layerMessage secretKey index lay))
        (signature.counter lay)) = some codeword := by
    rw [← hmessageEq, ← hencodeCached.eval_eq hf hg]
    exact hencode
  exact ⟨entry, signature, index, leaves, lay, chainIdx, codeword, targetDigit, hentry,
    hresponse, SuccessfulSignRun.changeAnswerFn hrun hf hg,
    SuccessfulDigestRun.changeAnswerFn hdigest hf hg, hencode', hle, hcoordinate⟩

attribute [local irreducible] maskedChronologicalRetainedPrefixAfterFtsSecrets

theorem resolvedCore_of_mem_runResolved_chronologicalRetainedPrefix
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (result : ResolvedRunResult
      ((Digest × (Forgery × QueryLog SigningSpec)) × SplitHashCache))
    (hresult : some result ∈ support
      (runResolvedFromTable
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table
        ((maskedChronologicalRetainedPrefixAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache))) :
    result.table = table ∧ result.context.ValuesConsistent ∧
      StartTableAgrees result.context.state table :=
  resolvedCore_of_mem_runResolved_of_reachableResolvedCouples
    (reachableResolvedCouples_chronologicalRetainedPrefixAfterFtsSecrets adversary parameter
      table ftsSecret)
    (resolvedContextInvariant_empty parameter table)
    (visibleResolvedComputationsCached_empty parameter table emptyDeferredStructuralValues ∅)
    publishedValues_empty hresult

theorem concreteSupport_of_mem_runResolved_chronologicalRetainedPrefix
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (result : ResolvedRunResult
      ((Digest × (Forgery × QueryLog SigningSpec)) × SplitHashCache))
    (completion : Coordinate → HashOutput)
    (hresult : some result ∈ support
      (runResolvedFromTable
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table
        ((maskedChronologicalRetainedPrefixAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache)))
    (hcompletion : DeferredCompletion table result.context completion) :
    ∃ concreteCache,
      ResolvedContextInvariant parameter table result.context
        (ordinaryQueryCache result.value.2) concreteCache ∧
      VisibleResolvedComputationsCached parameter table result.context concreteCache ∧
      PublishedValues result.context.state ∧
      (result.value.1, concreteCache) ∈ support
        ((concreteRetainedPrefixAfterFtsSecrets adversary parameter table ftsSecret).run ∅) :=
  concreteSupport_of_mem_runResolved_of_reachableResolvedCouples
    (reachableResolvedCouples_chronologicalRetainedPrefixAfterFtsSecrets adversary parameter
      table ftsSecret)
    (resolvedContextInvariant_empty parameter table)
    (visibleResolvedComputationsCached_empty parameter table emptyDeferredStructuralValues ∅)
    publishedValues_empty hresult hcompletion

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem not_verifyProbe_of_mem_runResolved_maskedChronologicalRetainedGame
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (targetCache : QueryCache HashSpec)
    (completion : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id)
    (fuel : Nat)
    (result : ResolvedRunResult (RetainedGameResult × SplitHashCache))
    (hresult : some result ∈ support
      (runResolvedFromTable
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table
        ((maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache)))
    (hcompletion : DeferredCompletion table result.context completion)
    (hfallback : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback)
    (hlogRuns : ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ result.value.1.2.1.2 → entry.2 = some signature →
        SuccessfulSignRun (tableAnswer parameter completion fallback) targetCache
          (⟨parameter, result.value.1.1,
            fun lay tree leafIdx chainIdx =>
              truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey)
          entry.1 signature)
    (hprobe : VerifyProbeWitness (tableAnswer parameter completion fallback) targetCache
      (⟨parameter, result.value.1.1,
        fun lay tree leafIdx chainIdx =>
          truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
        ftsSecret⟩ : SecretKey)
      result.value.1.2.1.2 result.value.1.2.1.1.message
        result.value.1.2.1.1.signature) : False := by
  unfold maskedChronologicalRetainedGameAfterFtsSecrets at hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨prefixOption, hprefix, hrest⟩ := hresult
  cases prefixOption with
  | none => simp at hrest
  | some prefixResult =>
      have hprefixCore : prefixResult.table = table ∧
          prefixResult.context.ValuesConsistent ∧
          StartTableAgrees prefixResult.context.state table :=
        resolvedCore_of_mem_runResolved_chronologicalRetainedPrefix adversary parameter table
          ftsSecret fuel prefixResult hprefix
      simp only at hrest
      rw [hprefixCore.1] at hrest
      have hprefixCompletion : DeferredCompletion table prefixResult.context completion :=
        hcompletion.of_mem_runResolvedFromTable _ prefixResult.context prefixResult.remaining table
          result completion hprefixCore.2.1 hprefixCore.2.2 hrest
      obtain ⟨prefixConcreteCache, hprefixInvariant, hprefixClosed, hprefixPublished,
          _hprefixConcrete⟩ :=
        concreteSupport_of_mem_runResolved_chronologicalRetainedPrefix adversary parameter table
          ftsSecret fuel prefixResult completion hprefix hprefixCompletion
      rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hrest
      obtain ⟨verifierOption, hverifier, hfinish⟩ := hrest
      cases verifierOption with
      | none => simp at hfinish
      | some verifierResult =>
          simp [runResolvedFromTable] at hfinish
          subst result
          have hprefixAllowed :=
            revealedChainAllowed_of_mem_runResolved_chronologicalRetainedPrefix adversary
              parameter table ftsSecret targetCache completion fallback fuel prefixResult hprefix
                hprefixCompletion
                (CacheAgreesWithFnOffTable.of_reachableResolvedCouples
                  (reachableResolvedCouples_probingRom parameter table
                    (scheme.verify ⟨prefixResult.value.1.1, parameter⟩
                      prefixResult.value.1.2.1.message prefixResult.value.1.2.1.signature))
                  hprefixInvariant hprefixClosed hprefixPublished hverifier hcompletion hfallback
                    (fun value finalCache hright =>
                      simulateQ_romImpl_cache_le
                        (scheme.verify ⟨prefixResult.value.1.1, parameter⟩
                          prefixResult.value.1.2.1.message
                            prefixResult.value.1.2.1.signature)
                        prefixConcreteCache (value, finalCache) hright))
                hlogRuns
          exact not_verifyProbe_of_mem_runResolved_verifier parameter table ftsSecret targetCache
            prefixResult.value.1.1 prefixResult.value.1.2.1 prefixResult.value.1.2.2 completion
              fallback prefixResult.context prefixResult.remaining prefixResult.value.2
                prefixConcreteCache verifierResult hprefixInvariant hprefixClosed hprefixPublished
                  hprefixAllowed hverifier hcompletion hfallback hprobe

end SphincsSecurity.Concrete.OtsProbeSimulation
