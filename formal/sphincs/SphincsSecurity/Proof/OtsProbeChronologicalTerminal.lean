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

theorem resolvedNoPublish_peekCoordinate (coordinate : Coordinate)
    (cache : SplitHashCache) :
    ResolvedNoPublish ((peekCoordinate coordinate).run cache) := by
  unfold peekCoordinate
  rw [StateT.run_bind]
  change ResolvedNoPublish
    (LazyRevealProbe.peekQuery coordinate >>= fun output => pure (_, cache))
  simp [ResolvedNoPublish, LazyRevealProbe.peekQuery, IsPublishQuery]

theorem resolvedNoPublish_probe (candidate : Probe) (cache : SplitHashCache) :
    ResolvedNoPublish ((probe candidate).run cache) := by
  unfold probe
  rw [StateT.run_liftM]
  simp [ResolvedNoPublish, LazyRevealProbe.probeQuery, IsPublishQuery]

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
