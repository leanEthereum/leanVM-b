import SphincsSecurity.Proof.OtsProbeRetained

/-!
# Origins of published one-time chain values

Every chain value published by the masked signer belongs to one successful signing-log entry. This
module packages that semantic endpoint and proves the incompatibilities needed by the exact forged
opening events.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def IsChainCoordinate : Coordinate → Prop
  | .chainStart _ _ _ _ => True
  | .position (.chain _ _ _ _ _) => True
  | _ => False

def ChainForwardClosed (allowed : Coordinate → Prop) : Prop :=
  ∀ candidate : Probe, allowed candidate.coordinate →
    IsChainCoordinate candidate.outputCoordinate → allowed candidate.outputCoordinate

def ordinaryQueryCache (cache : SplitHashCache) : QueryCache HashSpec :=
  fun input => cache (.ordinary input)

theorem ordinaryQueryCache_update (cache : SplitHashCache) (input : HashInput)
    (output : HashOutput) :
    ordinaryQueryCache (Function.update cache (.ordinary input) (some output)) =
      (ordinaryQueryCache cache).cacheQuery input output := by
  funext other
  by_cases heq : other = input
  · subst other
    simp [ordinaryQueryCache, QueryCache.cacheQuery, Function.update]
  · simp [ordinaryQueryCache, QueryCache.cacheQuery, Function.update, heq]

theorem ordinaryQueryCache_update_hidden (cache : SplitHashCache)
    (coordinate : Coordinate) (output : HashOutput) :
    ordinaryQueryCache (Function.update cache (.hidden coordinate) (some output)) =
      ordinaryQueryCache cache := by
  funext input
  simp [ordinaryQueryCache, Function.update]

def LazyRevealProbe.ValuesLE (initial final : LazyRevealProbe.State Coordinate) : Prop :=
  ∀ coordinate output, initial.values coordinate = some output →
    final.values coordinate = some output

theorem LazyRevealProbe.ValuesLE.refl (state : LazyRevealProbe.State Coordinate) :
    LazyRevealProbe.ValuesLE state state := by
  intro coordinate output hvalue
  exact hvalue

theorem LazyRevealProbe.ValuesLE.trans
    {first second third : LazyRevealProbe.State Coordinate}
    (hleft : LazyRevealProbe.ValuesLE first second)
    (hright : LazyRevealProbe.ValuesLE second third) :
    LazyRevealProbe.ValuesLE first third := by
  intro coordinate output hvalue
  exact hright coordinate output (hleft coordinate output hvalue)

theorem LazyRevealProbe.valuesLE_ensure (state : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) : LazyRevealProbe.ValuesLE state (state.ensure coordinate) := by
  intro other output hvalue
  exact hvalue

theorem LazyRevealProbe.valuesLE_addPending (state : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (candidate : Digest) :
    LazyRevealProbe.ValuesLE state (state.addPending coordinate candidate) := by
  intro other output hvalue
  exact hvalue

theorem LazyRevealProbe.valuesLE_publish (state : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) : LazyRevealProbe.ValuesLE state (state.publish coordinate) := by
  intro other output hvalue
  exact hvalue

theorem LazyRevealProbe.valuesLE_materialize_of_none
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate)
    (sampled : HashOutput) (hnone : state.values coordinate = none) :
    LazyRevealProbe.ValuesLE state (state.materialize coordinate sampled) := by
  intro other output hvalue
  by_cases heq : other = coordinate
  · subst other
    rw [hnone] at hvalue
    simp at hvalue
  · simpa [LazyRevealProbe.State.materialize, Function.update, heq] using hvalue

theorem LazyRevealProbe.valuesLE_of_mem_runRaw_done
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (state finalState : LazyRevealProbe.State Coordinate) (fuel remaining : Nat)
    (value : alpha)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining value ∈
      support (LazyRevealProbe.runRaw state fuel computation)) :
    LazyRevealProbe.ValuesLE state finalState := by
  induction computation using OracleComp.inductionOn generalizing
      state finalState fuel remaining value with
  | pure result =>
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl⟩
      exact fun _ _ hvalue => hvalue
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [LazyRevealProbe.runRaw_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _, htail⟩ := hresult
          exact ih output state finalState fuel remaining value htail
      | hashOutput =>
          rw [LazyRevealProbe.runRaw_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _, htail⟩ := hresult
          exact ih output state finalState fuel remaining value htail
      | ensure coordinate =>
          rw [LazyRevealProbe.runRaw_ensure_query_bind] at hresult
          exact (LazyRevealProbe.valuesLE_ensure state coordinate).trans
            (ih () (state.ensure coordinate) finalState fuel remaining value hresult)
      | probe coordinate candidate =>
          rw [LazyRevealProbe.runRaw_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remainingFuel =>
              simp only at hresult
              by_cases hrevealed : coordinate ∈ state.revealed
              · rw [if_pos hrevealed] at hresult
                exact ih () state finalState remainingFuel remaining value hresult
              · rw [if_neg hrevealed] at hresult
                exact (LazyRevealProbe.valuesLE_addPending state coordinate candidate).trans
                  (ih () (state.addPending coordinate candidate) finalState remainingFuel
                    remaining value hresult)
      | peek coordinate =>
          rw [LazyRevealProbe.runRaw_peek_query_bind] at hresult
          exact ih (state.values coordinate) state finalState fuel remaining value hresult
      | publish coordinate =>
          rw [LazyRevealProbe.runRaw_publish_query_bind] at hresult
          exact (LazyRevealProbe.valuesLE_publish state coordinate).trans
            (ih () (state.publish coordinate) finalState fuel remaining value hresult)
      | reveal coordinate =>
          rw [LazyRevealProbe.runRaw_reveal_query_bind] at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              rw [hvalue] at hresult
              exact ih output state finalState fuel remaining value hresult
          | none =>
              rw [hvalue] at hresult
              rw [mem_support_bind_iff] at hresult
              obtain ⟨output, _, htail⟩ := hresult
              by_cases hhit : state.hitAt coordinate output
              · rw [if_pos hhit] at htail
                simp at htail
              · rw [if_neg hhit] at htail
                exact (LazyRevealProbe.valuesLE_materialize_of_none state coordinate output
                  hvalue).trans (ih output (state.materialize coordinate output) finalState fuel
                    remaining value htail)

theorem mem_runRaw_splitHashQuery_ordinary_projects
    (input : HashInput) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((splitHashQuery (.ordinary input)).run cache))) :
    finalState = state ∧ remaining = fuel ∧
      (output, ordinaryQueryCache finalCache) ∈ support
        ((randomOracle (spec := HashSpec) input).run (ordinaryQueryCache cache)) := by
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache (.ordinary input) with
  | some cached =>
      rw [hlookup] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      refine ⟨rfl, rfl, ?_⟩
      have hordinary : ordinaryQueryCache finalCache input = some output := hlookup
      rw [QueryImpl.withCaching_run_some uniformSampleImpl hordinary]
      simp
  | none =>
      rw [hlookup] at hresult
      dsimp only at hresult
      change LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈ support
        (LazyRevealProbe.runRaw state fuel
          (LazyRevealProbe.hashOutputQuery >>= fun sampled =>
            pure (sampled, Function.update cache (.ordinary input) (some sampled)))) at hresult
      rw [LazyRevealProbe.hashOutputQuery,
        LazyRevealProbe.runRaw_hashOutput_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨sampled, _, hdone⟩ := hresult
      simp [LazyRevealProbe.runRaw] at hdone
      rcases hdone with ⟨rfl, rfl, rfl, rfl⟩
      refine ⟨rfl, rfl, ?_⟩
      have hordinary : ordinaryQueryCache cache input = none := hlookup
      rw [QueryImpl.withCaching_run_none uniformSampleImpl hordinary, support_map,
        ordinaryQueryCache_update]
      exact ⟨output, by simp [uniformSampleImpl], rfl⟩

theorem mem_runRaw_simulateQ_ordinaryHashImpl_projects
    (computation : OracleComp HashSpec alpha)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : alpha)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryHashImpl computation).run cache))) :
    finalState = state ∧ remaining = fuel ∧
      (value, ordinaryQueryCache finalCache) ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run
          (ordinaryQueryCache cache)) := by
  induction computation using OracleComp.inductionOn generalizing
      state cache finalState finalCache fuel remaining value with
  | pure result =>
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, by simp⟩
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨raw, hquery, hrest⟩ := hresult
      cases raw with
      | stopped hit => simp at hrest
      | done queryState queryRemaining queryResult =>
          rcases queryResult with ⟨answer, queryCache⟩
          have hqueryProjection := mem_runRaw_splitHashQuery_ordinary_projects input state
            queryState cache queryCache fuel queryRemaining answer hquery
          obtain ⟨rfl, rfl, hqueryActual⟩ := hqueryProjection
          have htailProjection := ih answer queryState finalState queryCache finalCache
            queryRemaining remaining value hrest
          obtain ⟨rfl, rfl, htailActual⟩ := htailProjection
          refine ⟨rfl, rfl, ?_⟩
          rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff]
          exact ⟨(answer, ordinaryQueryCache queryCache), hqueryActual, htailActual⟩

theorem mem_runRaw_simulateQ_splitUniformImpl_projects
    (computation : ProbComp alpha)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : alpha)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ splitUniformImpl computation).run cache))) :
    finalState = state ∧ remaining = fuel ∧ finalCache = cache ∧
      value ∈ support computation := by
  induction computation using OracleComp.inductionOn generalizing
      state cache finalState finalCache fuel remaining value with
  | pure result =>
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl, by simp⟩
  | query_bind n next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨raw, hquery, hrest⟩ := hresult
      cases raw with
      | stopped hit => simp at hrest
      | done queryState queryRemaining queryResult =>
          rcases queryResult with ⟨output, queryCache⟩
          change Fin (n + 1) at output
          change LazyRevealProbe.RawResult.done queryState queryRemaining
              (output, queryCache) ∈ support
            ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun sampled =>
              pure (LazyRevealProbe.RawResult.done state fuel (sampled, cache))) at hquery
          rw [mem_support_bind_iff] at hquery
          obtain ⟨sampled, hsampled, hdone⟩ := hquery
          simp at hdone
          rcases hdone with ⟨rfl, rfl, rfl, rfl⟩
          obtain ⟨rfl, rfl, rfl, htail⟩ := ih output queryState finalState queryCache
            finalCache queryRemaining remaining value hrest
          refine ⟨rfl, rfl, rfl, ?_⟩
          rw [mem_support_bind_iff]
          exact ⟨output, hsampled, htail⟩

theorem evalWithAnswerFn_eq_of_mem_runRaw_ordinaryHashImpl
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec alpha)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : alpha)
    (hf : (ordinaryQueryCache finalCache).AgreesWithFn f)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryHashImpl computation).run cache))) :
    evalWithAnswerFn f computation = value := by
  have hprojection := mem_runRaw_simulateQ_ordinaryHashImpl_projects computation state
    finalState cache finalCache fuel remaining value hresult
  exact (replay_of_mem_support computation (ordinaryQueryCache cache) value
    (ordinaryQueryCache finalCache) hprojection.2.2 f hf).2.1

def SplitCachePreserving
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache,
    LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
    finalCache = cache

def OrdinaryCacheIncreasing
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache,
    LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
    ordinaryQueryCache cache ≤ ordinaryQueryCache finalCache

def OrdinaryEntryPreserving (input : HashInput)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache output,
    cache (.ordinary input) = some output →
    LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
    finalCache (.ordinary input) = some output

def CachesOrdinaryInput (input : HashInput)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache,
    LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
    finalCache (.ordinary input) ≠ none

theorem CachesOrdinaryInput.bind_right
    {input : HashInput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hnext : ∀ value, CachesOrdinaryInput input (next value)) :
    CachesOrdinaryInput input (left >>= next) := by
  intro state cache fuel finalState remaining result finalCache hresult
  change LazyRevealProbe.RawResult.done finalState remaining (result, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun leftResult => (next leftResult.1).run leftResult.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, _, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining leftResult =>
      rcases leftResult with ⟨leftValue, middleCache⟩
      exact hnext leftValue middleState middleCache middleRemaining finalState remaining result
        finalCache hrest

theorem CachesOrdinaryInput.bind_preserving
    {input : HashInput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : CachesOrdinaryInput input left)
    (hnext : ∀ value, OrdinaryEntryPreserving input (next value)) :
    CachesOrdinaryInput input (left >>= next) := by
  intro state cache fuel finalState remaining result finalCache hresult
  change LazyRevealProbe.RawResult.done finalState remaining (result, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun leftResult => (next leftResult.1).run leftResult.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining leftResult =>
      rcases leftResult with ⟨leftValue, middleCache⟩
      obtain ⟨output, hcached⟩ := Option.ne_none_iff_exists'.mp
        (hleft state cache fuel middleState middleRemaining leftValue middleCache hraw)
      exact Option.ne_none_iff_exists'.2 ⟨output,
        hnext leftValue middleState middleCache middleRemaining finalState remaining result
          finalCache output hcached hrest⟩

def StableOrdinaryInput (parameter : PublicParameter) (input : HashInput) : Prop :=
  decodeProbe? parameter input = none ∧
    ∀ position, decodePosition? parameter input = some position → ¬IsOtsPosition position

def StableCacheAgreesWithFn (parameter : PublicParameter) (cache : SplitHashCache)
    (f : QueryImpl HashSpec Id) : Prop :=
  ∀ input output, StableOrdinaryInput parameter input →
    cache (.ordinary input) = some output → f input = output

theorem StableCacheAgreesWithFn.of_agrees
    {parameter : PublicParameter} {cache : SplitHashCache} {f : QueryImpl HashSpec Id}
    (hf : (ordinaryQueryCache cache).AgreesWithFn f) :
    StableCacheAgreesWithFn parameter cache f := by
  intro input output _ hcached
  exact hf hcached

theorem StableCacheAgreesWithFn.of_run
    {parameter : PublicParameter} {f : QueryImpl HashSpec Id}
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    (hpreserving : ∀ input, StableOrdinaryInput parameter input →
      OrdinaryEntryPreserving input computation)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : alpha)
    (hfinal : StableCacheAgreesWithFn parameter finalCache f)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache))) :
    StableCacheAgreesWithFn parameter cache f := by
  intro input output hstable hcached
  exact hfinal input output hstable
    (hpreserving input hstable state cache fuel finalState remaining value finalCache output
      hcached hresult)

def QueriesStable (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec alpha) : Prop :=
  ∀ input, input ∈ queriedInputs f computation → StableOrdinaryInput parameter input

theorem QueriesStable.pure
    (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (value : alpha) :
    QueriesStable parameter f (pure value : OracleComp HashSpec alpha) := by
  intro input hinput
  simp at hinput

theorem QueriesStable.bind
    {parameter : PublicParameter} {f : QueryImpl HashSpec Id}
    {left : OracleComp HashSpec alpha} {next : alpha → OracleComp HashSpec beta}
    (hleft : QueriesStable parameter f left)
    (hnext : QueriesStable parameter f (next (evalWithAnswerFn f left))) :
    QueriesStable parameter f (left >>= next) := by
  intro input hinput
  rw [queriedInputs_bind] at hinput
  rcases List.mem_append.mp hinput with hinput | hinput
  · exact hleft input hinput
  · exact hnext input hinput

theorem QueriesStable.sequenceFin
    {parameter : PublicParameter} {f : QueryImpl HashSpec Id} {n : Nat}
    (computation : Fin n → OracleComp HashSpec alpha)
    (hcomputation : ∀ index, QueriesStable parameter f (computation index)) :
    QueriesStable parameter f (sequenceFin computation) := by
  induction n with
  | zero => exact QueriesStable.pure parameter f Fin.elim0
  | succ n ih =>
      rw [SphincsSecurity.Concrete.sequenceFin]
      exact (hcomputation 0).bind <|
        (ih (fun index => computation index.succ) fun index => hcomputation index.succ).bind
          (QueriesStable.pure parameter f _)

theorem replay_of_mem_support_of_stable
    (parameter : PublicParameter) (computation : OracleComp HashSpec alpha)
    (cache : QueryCache HashSpec) (value : alpha) (finalCache : QueryCache HashSpec)
    (hresult : (value, finalCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run cache))
    (f : QueryImpl HashSpec Id)
    (hfinal : ∀ input output, StableOrdinaryInput parameter input →
      finalCache input = some output → f input = output)
    (hstable : QueriesStable parameter f computation) :
    cache ≤ finalCache ∧ evalWithAnswerFn f computation = value ∧
      CachedRun finalCache f computation := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache value finalCache with
  | pure result =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hresult
      obtain ⟨rfl, rfl⟩ := hresult
      refine ⟨le_rfl, rfl, ?_⟩
      simp [CachedRun]
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨⟨answer, middleCache⟩, hquery, hrest⟩ := hresult
      change (answer, middleCache) ∈ support ((randomOracle input).run cache) at hquery
      have hcached : middleCache input = some answer := by
        cases hcache : cache input with
        | some old =>
            rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache, support_pure,
              Set.mem_singleton_iff] at hquery
            obtain ⟨rfl, rfl⟩ := hquery
            exact hcache
        | none =>
            rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map] at hquery
            obtain ⟨sampled, _, heq⟩ := hquery
            obtain ⟨rfl, rfl⟩ := heq
            exact QueryCache.cacheQuery_self cache input answer
      have hinputStable : StableOrdinaryInput parameter input := by
        apply hstable input
        rw [queriedInputs_query_bind]
        simp
      have hmiddleLe : middleCache ≤ finalCache :=
        FtsProbeSimulation.simulateQ_randomOracle_cache_le (next answer) middleCache finalCache
          value hrest
      have hcachedFinal : finalCache input = some answer := hmiddleLe hcached
      have hfinput : f input = answer := hfinal input answer hinputStable hcachedFinal
      have htailStable : QueriesStable parameter f (next answer) := by
        intro other hother
        apply hstable other
        rw [queriedInputs_query_bind, hfinput]
        exact List.mem_cons_of_mem input hother
      obtain ⟨hle, heval, hqueries⟩ := ih answer middleCache value finalCache hrest
        hfinal htailStable
      refine ⟨(QueryImpl.withCaching_cache_le uniformSampleImpl input cache
        (answer, middleCache) hquery).trans hle, ?_, ?_⟩
      · rw [evalWithAnswerFn_bind,
          show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
            simulateQ_spec_query f input, hfinput]
        exact heval
      · intro other hqueried
        rw [queriedInputs_query_bind, hfinput] at hqueried
        simp only [List.mem_cons] at hqueried
        rcases hqueried with rfl | htail
        ·
          simp [hcachedFinal]
        · exact hqueries other htail

theorem replay_of_mem_runRaw_ordinaryHashImpl_of_stable
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (computation : OracleComp HashSpec alpha)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : alpha)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (hstable : QueriesStable parameter f computation)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryHashImpl computation).run cache))) :
    evalWithAnswerFn f computation = value ∧
      CachedRun (ordinaryQueryCache finalCache) f computation := by
  have hprojection := mem_runRaw_simulateQ_ordinaryHashImpl_projects computation state
    finalState cache finalCache fuel remaining value hresult
  have hreplay := replay_of_mem_support_of_stable parameter computation
    (ordinaryQueryCache cache) value (ordinaryQueryCache finalCache) hprojection.2.2 f
      (fun input output hinput hcached => hf input output hinput hcached) hstable
  exact ⟨hreplay.2.1, hreplay.2.2⟩

theorem OrdinaryEntryPreserving.pure (input : HashInput) (value : alpha) :
    OrdinaryEntryPreserving input
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro state cache fuel finalState remaining result finalCache output hcached hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hcached

theorem OrdinaryEntryPreserving.bind
    {input : HashInput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : OrdinaryEntryPreserving input left)
    (hnext : ∀ value, OrdinaryEntryPreserving input (next value)) :
    OrdinaryEntryPreserving input (left >>= next) := by
  intro state cache fuel finalState remaining result finalCache output hcached hresult
  change LazyRevealProbe.RawResult.done finalState remaining (result, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun leftResult => (next leftResult.1).run leftResult.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining leftResult =>
      rcases leftResult with ⟨leftValue, middleCache⟩
      exact hnext leftValue middleState middleCache middleRemaining finalState remaining result
        finalCache output (hleft state cache fuel middleState middleRemaining leftValue middleCache
          output hcached hraw) hrest

theorem OrdinaryCacheIncreasing.entryPreserving
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    (hincreasing : OrdinaryCacheIncreasing computation) (input : HashInput) :
    OrdinaryEntryPreserving input computation := by
  intro state cache fuel finalState remaining value finalCache output hcached hresult
  exact hincreasing state cache fuel finalState remaining value finalCache hresult hcached

theorem OrdinaryCacheIncreasing.pure (value : alpha) :
    OrdinaryCacheIncreasing
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro state cache fuel finalState remaining result finalCache hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact le_rfl

theorem OrdinaryCacheIncreasing.bind
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : OrdinaryCacheIncreasing left)
    (hnext : ∀ value, OrdinaryCacheIncreasing (next value)) :
    OrdinaryCacheIncreasing (left >>= next) := by
  intro state cache fuel finalState remaining result finalCache hresult
  change LazyRevealProbe.RawResult.done finalState remaining (result, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun leftResult => (next leftResult.1).run leftResult.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining leftResult =>
      rcases leftResult with ⟨leftValue, middleCache⟩
      exact (hleft state cache fuel middleState middleRemaining leftValue middleCache hraw).trans
        (hnext leftValue middleState middleCache middleRemaining finalState remaining result
          finalCache hrest)

theorem ordinaryCacheIncreasing_simulateQ_ordinaryHashImpl
    (computation : OracleComp HashSpec alpha) :
    OrdinaryCacheIncreasing (simulateQ ordinaryHashImpl computation) := by
  intro state cache fuel finalState remaining value finalCache hresult
  have hprojection := mem_runRaw_simulateQ_ordinaryHashImpl_projects computation state
    finalState cache finalCache fuel remaining value hresult
  exact FtsProbeSimulation.simulateQ_randomOracle_cache_le computation
    (ordinaryQueryCache cache) (ordinaryQueryCache finalCache) value hprojection.2.2

theorem ordinaryCacheIncreasing_splitHashQuery_ordinary (input : HashInput) :
    OrdinaryCacheIncreasing (splitHashQuery (.ordinary input)) := by
  have hincreasing := ordinaryCacheIncreasing_simulateQ_ordinaryHashImpl
    (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput)
  simpa [ordinaryHashImpl] using hincreasing

theorem cachesOrdinaryInput_splitHashQuery (input : HashInput) :
    CachesOrdinaryInput input (splitHashQuery (.ordinary input)) := by
  intro state cache fuel finalState remaining output finalCache hresult
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache (.ordinary input) with
  | some cached =>
      rw [hlookup] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      simp [hlookup]
  | none =>
      rw [hlookup] at hresult
      dsimp only at hresult
      change LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈ support
        (LazyRevealProbe.runRaw state fuel
          (LazyRevealProbe.hashOutputQuery >>= fun sampled =>
            pure (sampled, Function.update cache (.ordinary input) (some sampled)))) at hresult
      rw [LazyRevealProbe.hashOutputQuery,
        LazyRevealProbe.runRaw_hashOutput_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨sampled, _, hdone⟩ := hresult
      simp [LazyRevealProbe.runRaw] at hdone
      rcases hdone with ⟨rfl, rfl, rfl, rfl⟩
      simp [Function.update]

theorem ordinaryCacheIncreasing_simulateQ_splitUniformImpl
    (computation : ProbComp alpha) :
    OrdinaryCacheIncreasing (simulateQ splitUniformImpl computation) := by
  intro state cache fuel finalState remaining value finalCache hresult
  have hprojection := mem_runRaw_simulateQ_splitUniformImpl_projects computation state
    finalState cache finalCache fuel remaining value hresult
  rw [hprojection.2.2.1]

theorem SplitCachePreserving.pure (value : alpha) :
    SplitCachePreserving
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro state cache fuel finalState remaining result finalCache hresult
  simp [LazyRevealProbe.runRaw] at hresult
  exact hresult.2.2.2

theorem SplitCachePreserving.bind
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : SplitCachePreserving left)
    (hnext : ∀ value, SplitCachePreserving (next value)) :
    SplitCachePreserving (left >>= next) := by
  intro state cache fuel finalState remaining result finalCache hresult
  change LazyRevealProbe.RawResult.done finalState remaining (result, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun leftResult => (next leftResult.1).run leftResult.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining leftResult =>
      rcases leftResult with ⟨leftValue, middleCache⟩
      exact (hnext leftValue middleState middleCache middleRemaining finalState remaining result
        finalCache hrest).trans (hleft state cache fuel middleState middleRemaining leftValue
          middleCache hraw)

theorem SplitCachePreserving.ordinaryCacheIncreasing
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    (hpreserves : SplitCachePreserving computation) :
    OrdinaryCacheIncreasing computation := by
  intro state cache fuel finalState remaining value finalCache hresult
  rw [hpreserves state cache fuel finalState remaining value finalCache hresult]

theorem SplitCachePreserving.entryPreserving
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    (hpreserves : SplitCachePreserving computation) (input : HashInput) :
    OrdinaryEntryPreserving input computation :=
  hpreserves.ordinaryCacheIncreasing.entryPreserving input

theorem splitCachePreserving_ensureCoordinate (coordinate : Coordinate) :
    SplitCachePreserving (ensureCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.ensureQuery coordinate >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.ensureQuery, LazyRevealProbe.runRaw_ensure_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  exact hresult.2.2

theorem splitCachePreserving_sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomputation : ∀ index, SplitCachePreserving (computation index)) :
    SplitCachePreserving (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact SplitCachePreserving.pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomputation 0).bind fun _ =>
        (ih (fun index => computation index.succ)
          (fun index => hcomputation index.succ)).bind fun _ =>
            SplitCachePreserving.pure _

theorem splitCachePreserving_ensureChainPrefix
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (digit : Digit) :
    SplitCachePreserving (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (splitCachePreserving_sequenceFin _ fun step => by
    split
    · exact splitCachePreserving_ensureCoordinate _
    · exact SplitCachePreserving.pure ()).bind fun _ => SplitCachePreserving.pure ()

theorem splitCachePreserving_ensureFullChain
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    SplitCachePreserving (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (splitCachePreserving_sequenceFin _ fun _ =>
    splitCachePreserving_ensureCoordinate _).bind fun _ => SplitCachePreserving.pure ()

theorem splitCachePreserving_ensureOtsLeaf
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    SplitCachePreserving (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (splitCachePreserving_sequenceFin _ fun chainIdx =>
    splitCachePreserving_ensureFullChain lay tree leafIdx chainIdx).bind fun _ =>
      splitCachePreserving_ensureCoordinate _

theorem splitCachePreserving_ensureTreeNode (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx, SplitCachePreserving (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => splitCachePreserving_ensureOtsLeaf lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (splitCachePreserving_ensureTreeNode lay tree level (2 * nodeIdx)).bind fun _ =>
        (splitCachePreserving_ensureTreeNode lay tree level (2 * nodeIdx + 1)).bind fun _ => by
          split
          · exact splitCachePreserving_ensureCoordinate _
          · exact SplitCachePreserving.pure ()

theorem splitCachePreserving_ensureTreePath
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    SplitCachePreserving (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (splitCachePreserving_sequenceFin _ fun level => by
    split
    · exact splitCachePreserving_ensureTreeNode lay tree level.val
        (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
    · exact SplitCachePreserving.pure ()).bind fun _ => SplitCachePreserving.pure ()

theorem ordinaryCacheIncreasing_sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomputation : ∀ index, OrdinaryCacheIncreasing (computation index)) :
    OrdinaryCacheIncreasing (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact OrdinaryCacheIncreasing.pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomputation 0).bind fun _ =>
        (ih (fun index => computation index.succ)
          (fun index => hcomputation index.succ)).bind fun _ =>
            OrdinaryCacheIncreasing.pure _

theorem isChainCoordinate_chainValueCoordinate (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    IsChainCoordinate (chainValueCoordinate lay tree leafIdx chainIdx digit) := by
  unfold chainValueCoordinate
  split <;> trivial

def ChainState.ValidFor (allowed : Coordinate → Prop)
    (state : LazyRevealProbe.State Coordinate) : Prop :=
  ∀ coordinate, IsChainCoordinate coordinate →
    (state.values coordinate ≠ none → coordinate ∈ state.revealed) ∧
    (coordinate ∈ state.revealed → state.values coordinate ≠ none) ∧
    (coordinate ∈ state.revealed → allowed coordinate)

def ChainProbeAccounted (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) : Prop :=
  ∀ (probe : Probe) (input : HashInput), probe.MatchesInput parameter input →
    cache (.ordinary input) ≠ none →
    ¬allowed probe.coordinate → probe.candidate ∈ state.pendingAt probe.coordinate

theorem chainProbeAccounted_empty (parameter : PublicParameter) (allowed : Coordinate → Prop) :
    ChainProbeAccounted parameter allowed
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) emptySplitHashCache := by
  intro probe input hmatch hcached
  simp [emptySplitHashCache] at hcached

theorem Probe.target_eq_truncate_table_of_chain
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (probe : Probe)
    (hchain : IsChainCoordinate probe.coordinate)
    (hf : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position)) :
    probe.target f parameter (tableOtsSecret table) ftsSecret =
      truncateHash (table probe.coordinate) := by
  rcases probe with ⟨coordinate, candidate⟩
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx => simp [Probe.target, tableOtsSecret]
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          change honestValue f parameter (tableOtsSecret table) ftsSecret
              (.chain lay tree leafIdx chainIdx step) =
            truncateHash (table (.position (.chain lay tree leafIdx chainIdx step)))
          rw [honestValue_chain,
            honestChain_eq_table_succ f parameter table lay tree leafIdx chainIdx hf
              step.val step.isLt]
          rfl
      | leaf => simp [IsChainCoordinate] at hchain
      | node => simp [IsChainCoordinate] at hchain
      | ftsLeaf => simp [IsChainCoordinate] at hchain
      | ftsNode => simp [IsChainCoordinate] at hchain
      | ftsRoots => simp [IsChainCoordinate] at hchain

theorem ChainProbeAccounted.hitAt
    {parameter : PublicParameter} {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (haccounted : ChainProbeAccounted parameter allowed state cache)
    (f : QueryImpl HashSpec Id) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (probe : Probe) (input : HashInput)
    (hchain : IsChainCoordinate probe.coordinate)
    (hf : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hhits : probe.Hits f parameter (tableOtsSecret table) ftsSecret)
    (hmatches : probe.MatchesInput parameter input) (hcached : cache (.ordinary input) ≠ none)
    (hnotAllowed : ¬allowed probe.coordinate) : state.hitAt probe.coordinate (table probe.coordinate) := by
  have hpending := haccounted probe input hmatches hcached hnotAllowed
  rw [LazyRevealProbe.State.hitAt]
  rw [← probe.target_eq_truncate_table_of_chain f parameter table ftsSecret hchain hf,
    ← hhits]
  exact hpending

theorem Probe.isChainCoordinate_of_matchesInput
    {parameter : PublicParameter} {probe : Probe} {input : HashInput}
    (hmatches : probe.MatchesInput parameter input) :
    IsChainCoordinate probe.coordinate := by
  rcases probe with ⟨coordinate, candidate⟩
  cases coordinate with
  | chainStart => trivial
  | position position =>
      cases position with
      | chain => trivial
      | leaf => simp [Probe.MatchesInput] at hmatches
      | node => simp [Probe.MatchesInput] at hmatches
      | ftsLeaf => simp [Probe.MatchesInput] at hmatches
      | ftsNode => simp [Probe.MatchesInput] at hmatches
      | ftsRoots => simp [Probe.MatchesInput] at hmatches

theorem decodeProbe?_tweakableHashInput_of_not_chain_leaf
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (hinRange : domain.InRange)
    (hchain : ∀ lay tree leafIdx chainIdx step,
      domain ≠ .chain lay tree leafIdx chainIdx step)
    (hleaf : ∀ lay tree leafIdx, domain ≠ .leaf lay tree leafIdx) :
    decodeProbe? parameter (tweakableHashInput parameter domain payload) = none := by
  rw [decodeProbe?_eq_none_iff]
  rintro ⟨coordinate, candidate⟩ hmatches
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      obtain ⟨step, hstep, hinput⟩ := hmatches
      have hdomain := (tweakableHashInput_injective parameter hinRange (by trivial) hinput).1
      exact hchain lay tree leafIdx chainIdx step hdomain
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          simp only [Probe.MatchesInput] at hmatches
          split at hmatches
          · obtain ⟨nextStep, hnext, hinput⟩ := hmatches
            have hdomain :=
              (tweakableHashInput_injective parameter hinRange (by trivial) hinput).1
            exact hchain lay tree leafIdx chainIdx nextStep hdomain
          · obtain ⟨hchainZero, leafPayload, hinput, hslot⟩ := hmatches
            have hdomain :=
              (tweakableHashInput_injective parameter hinRange (by trivial) hinput).1
            exact hleaf lay tree leafIdx hdomain
      | leaf => simp [Probe.MatchesInput] at hmatches
      | node => simp [Probe.MatchesInput] at hmatches
      | ftsLeaf => simp [Probe.MatchesInput] at hmatches
      | ftsNode => simp [Probe.MatchesInput] at hmatches
      | ftsRoots => simp [Probe.MatchesInput] at hmatches

theorem stableOrdinaryInput_tweakableHashInput
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (hinRange : domain.InRange)
    (hchain : ∀ lay tree leafIdx chainIdx step,
      domain ≠ .chain lay tree leafIdx chainIdx step)
    (hleaf : ∀ lay tree leafIdx, domain ≠ .leaf lay tree leafIdx)
    (hnode : ∀ lay tree level nodeIdx, domain ≠ .node lay tree level nodeIdx) :
    StableOrdinaryInput parameter (tweakableHashInput parameter domain payload) := by
  refine ⟨decodeProbe?_tweakableHashInput_of_not_chain_leaf parameter domain payload hinRange
    hchain hleaf, ?_⟩
  intro position hposition hots
  have hat := (decodePosition?_eq_some_iff parameter _ position).1 hposition
  obtain ⟨positionPayload, hinput⟩ := hat
  have hdomain := (tweakableHashInput_injective parameter hinRange position.domain_inRange
    hinput).1
  cases position with
  | chain lay tree leafIdx chainIdx step => exact hchain lay tree leafIdx chainIdx step hdomain
  | leaf lay tree leafIdx => exact hleaf lay tree leafIdx hdomain
  | node lay tree level nodeIdx =>
      exact hnode lay tree (level.val + 1) nodeIdx.val hdomain
  | ftsLeaf | ftsNode | ftsRoots => simp [IsOtsPosition] at hots

theorem queriesStable_tweakableHash
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) (hinRange : domain.InRange)
    (hchain : ∀ lay tree leafIdx chainIdx step,
      domain ≠ .chain lay tree leafIdx chainIdx step)
    (hleaf : ∀ lay tree leafIdx, domain ≠ .leaf lay tree leafIdx)
    (hnode : ∀ lay tree level nodeIdx, domain ≠ .node lay tree level nodeIdx) :
    QueriesStable parameter f (tweakableHash parameter domain payload) := by
  intro input hinput
  rw [queriedInputs_tweakableHash] at hinput
  simp only [List.mem_singleton] at hinput
  subst input
  exact stableOrdinaryInput_tweakableHashInput parameter domain payload hinRange hchain hleaf
    hnode

theorem queriesStable_ftsLeafHash
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf) (secret : Digest) :
    QueriesStable parameter f (ftsLeafHash parameter index tree leafIdx secret) := by
  unfold ftsLeafHash
  exact queriesStable_tweakableHash f parameter (.ftsLeaf index tree leafIdx) _ (by trivial)
    (by simp) (by simp) (by simp)

theorem queriesStable_ftsNode
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (tree : FtsTree) (secret : FtsLeaf → Digest) :
    ∀ level nodeIdx, level ≤ ftsTreeHeight →
      2 ^ level * (nodeIdx + 1) ≤ 2 ^ ftsTreeHeight → QueriesStable parameter f
      (ftsNode parameter index tree secret level nodeIdx)
  | 0, nodeIdx, hlevel, hspan => by
      rw [ftsNode_zero_eq]
      exact queriesStable_ftsLeafHash f parameter index tree _ _
  | level + 1, nodeIdx, hlevel, hspan => by
      rw [ftsNode_succ_eq]
      have hleftSpan : 2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ ftsTreeHeight := by
        rw [pow_succ] at hspan
        calc
          2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ level * (2 * (nodeIdx + 1)) :=
            Nat.mul_le_mul_left _ (by omega)
          _ = 2 ^ level * 2 * (nodeIdx + 1) := by ring
          _ ≤ 2 ^ ftsTreeHeight := hspan
      have hrightSpan : 2 ^ level * (2 * nodeIdx + 1 + 1) ≤ 2 ^ ftsTreeHeight := by
        rw [pow_succ] at hspan
        calc
          2 ^ level * (2 * nodeIdx + 1 + 1) = 2 ^ level * 2 * (nodeIdx + 1) := by
            ring
          _ ≤ 2 ^ ftsTreeHeight := hspan
      have hinRange : (HashDomain.ftsNode index tree (level + 1) nodeIdx).InRange := by
        show level + 1 < 2 ^ 32 ∧ nodeIdx < 2 ^ 32
        constructor
        · have : ftsTreeHeight < 2 ^ 32 := by norm_num [ftsTreeHeight]
          omega
        · have hnode : nodeIdx < 2 ^ ftsTreeHeight := by
            have hpow : 0 < 2 ^ (level + 1) := Nat.two_pow_pos _
            nlinarith
          have : 2 ^ ftsTreeHeight ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) (by
            norm_num [ftsTreeHeight])
          omega
      exact (queriesStable_ftsNode f parameter index tree secret level (2 * nodeIdx)
        (by omega) hleftSpan).bind <|
        (queriesStable_ftsNode f parameter index tree secret level (2 * nodeIdx + 1)
          (by omega) hrightSpan).bind <|
          queriesStable_tweakableHash f parameter (.ftsNode index tree (level + 1) nodeIdx) _
            hinRange (by simp) (by simp) (by simp)

theorem queriesStable_ftsKey
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    QueriesStable parameter f (ftsKey parameter index secret) := by
  unfold ftsKey
  exact (QueriesStable.sequenceFin
    (fun tree => ftsNode parameter index tree (secret tree) ftsTreeHeight 0)
    (fun tree => queriesStable_ftsNode f parameter index tree (secret tree) ftsTreeHeight 0
      le_rfl (by simp))).bind
      (queriesStable_tweakableHash f parameter (.ftsRoots index) _ (by trivial)
        (by simp) (by simp) (by simp))

theorem queriesStable_ftsOpen
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (leaves : DigestTree → FtsLeaf) (secret : FtsTree → FtsLeaf → Digest) :
    QueriesStable parameter f (ftsOpen parameter index leaves secret) := by
  unfold ftsOpen
  exact QueriesStable.sequenceFin _ fun tree =>
    QueriesStable.sequenceFin _ fun level =>
      queriesStable_ftsNode f parameter index tree (secret tree) level.val
        (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)
          (Nat.le_of_lt level.isLt)
          (FtsProbeSimulation.ftsOpen_node_bound (leaves (ftsIndexOf tree)) level)

theorem queriesStable_encode
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) :
    QueriesStable parameter f (encode parameter lay tree leafIdx message counter) := by
  unfold encode
  exact (queriesStable_tweakableHash f parameter (.encoding lay tree leafIdx) _ (by trivial)
    (by simp) (by simp) (by simp)).bind (QueriesStable.pure parameter f _)

theorem queriesStable_messageDigest
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) :
    QueriesStable parameter f (messageDigest parameter root message randomness) := by
  unfold messageDigest oracleHash
  intro input hinput
  change input ∈ queriedInputs f
    ((liftM (HashSpec.query (tweakableHashInput parameter .message
      (messageDigestPayload root message randomness))) : OracleComp HashSpec HashOutput) >>=
        fun output => pure (truncateMessageDigest output)) at hinput
  rw [queriedInputs_query_bind, queriedInputs_pure] at hinput
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hinput
  subst input
  exact stableOrdinaryInput_tweakableHashInput parameter .message _ (by trivial)
    (by simp) (by simp) (by simp)

theorem queriesStable_signAttempt
    (f : QueryImpl HashSpec Id) (secretKey : SecretKey) (message : Message)
    (randomness : Randomness) :
    QueriesStable secretKey.parameter f (signAttempt secretKey message randomness) := by
  unfold signAttempt
  exact (queriesStable_messageDigest f secretKey.parameter secretKey.root message randomness).bind
    (by split <;> exact QueriesStable.pure secretKey.parameter f _)

theorem maskedOtsSignFrom_some_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter (state finalState : LazyRevealProbe.State Coordinate)
      (cache finalCache : SplitHashCache) (fuel remaining : Nat)
      (selectedCounter : Counter) (encoding : ChainIndex → Digit),
      StableCacheAgreesWithFn parameter finalCache f →
      LazyRevealProbe.RawResult.done finalState remaining
          (some (selectedCounter, encoding), finalCache) ∈ support
        (LazyRevealProbe.runRaw state fuel
          ((maskedOtsSignFrom parameter lay tree leafIdx message attempts counter).run cache)) →
      evalWithAnswerFn f
        (encode parameter lay tree leafIdx message selectedCounter) = some encoding
  | 0, counter, state, finalState, cache, finalCache, fuel, remaining,
      selectedCounter, encoding, hf, hresult => by
      simp [maskedOtsSignFrom, LazyRevealProbe.runRaw] at hresult
  | attempts + 1, counter, state, finalState, cache, finalCache, fuel, remaining,
      selectedCounter, encoding, hf, hresult => by
      rw [maskedOtsSignFrom, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨raw, hencode, hrest⟩ := hresult
      cases raw with
      | stopped hit => simp at hrest
      | done encodeState encodeRemaining encodeResult =>
          rcases encodeResult with ⟨encoded, encodeCache⟩
          simp only at hrest
          cases encoded with
          | none =>
              exact maskedOtsSignFrom_some_eval f parameter lay tree leafIdx message attempts
                (counter + 1) encodeState finalState encodeCache finalCache encodeRemaining
                  remaining selectedCounter encoding hf hrest
          | some selectedEncoding =>
              rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
                mem_support_bind_iff] at hrest
              obtain ⟨ensureRaw, hensure, hfinish⟩ := hrest
              cases ensureRaw with
              | stopped hit => simp at hfinish
              | done ensureState ensureRemaining ensureResult =>
                  rcases ensureResult with ⟨ensured, ensureCache⟩
                  have hcache := splitCachePreserving_sequenceFin
                    (fun chainIdx => ensureChainPrefix lay tree leafIdx chainIdx
                      (selectedEncoding chainIdx))
                    (fun chainIdx => splitCachePreserving_ensureChainPrefix lay tree leafIdx
                      chainIdx (selectedEncoding chainIdx)) encodeState encodeCache
                        encodeRemaining ensureState ensureRemaining ensured ensureCache hensure
                  simp [LazyRevealProbe.runRaw] at hfinish
                  rcases hfinish with ⟨rfl, hremaining, houtput, hfinalCache⟩
                  rcases houtput with ⟨hselectedCounter, hencoding⟩
                  subst selectedCounter
                  subst encoding
                  subst finalCache
                  rw [hcache] at hf
                  exact (replay_of_mem_runRaw_ordinaryHashImpl_of_stable f parameter
                    (encode parameter lay tree leafIdx message
                      (BitVec.ofNat counterBits counter)) state encodeState cache encodeCache fuel
                        encodeRemaining (some selectedEncoding) hf
                          (queriesStable_encode f parameter lay tree leafIdx message
                            (BitVec.ofNat counterBits counter)) hencode).1

theorem maskedOtsSign_some_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (counter : Counter) (encoding : ChainIndex → Digit)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some (counter, encoding), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedOtsSign parameter lay tree leafIdx message).run cache))) :
    evalWithAnswerFn f (encode parameter lay tree leafIdx message counter) = some encoding := by
  exact maskedOtsSignFrom_some_eval f parameter lay tree leafIdx message encodingAttemptLimit 0
    state finalState cache finalCache fuel remaining counter encoding hf hresult

theorem tweakableHashInput_ftsNode_ne_chain
    (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (level nodeIdx : Nat) (payload : HashInput) (lay : Layer) (otsTree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
    (chainPayload : HashInput) :
    tweakableHashInput parameter (.ftsNode index tree level nodeIdx) payload ≠
      tweakableHashInput parameter (.chain lay otsTree leafIdx chainIdx step) chainPayload := by
  intro hinput
  simp only [tweakableHashInput] at hinput
  obtain ⟨hprefix, _⟩ := List.append_inj hinput
    (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  rw [tweakBytes_eq_iff] at htweak
  simp [hashDomainFields, TweakFields.mk.injEq] at htweak

theorem tweakableHashInput_ftsNode_ne_leaf
    (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (level nodeIdx : Nat) (payload : HashInput) (lay : Layer) (otsTree : TreeIndex)
    (leafIdx : LeafIndex) (leafPayload : HashInput) :
    tweakableHashInput parameter (.ftsNode index tree level nodeIdx) payload ≠
      tweakableHashInput parameter (.leaf lay otsTree leafIdx) leafPayload := by
  intro hinput
  simp only [tweakableHashInput] at hinput
  obtain ⟨hprefix, _⟩ := List.append_inj hinput
    (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  rw [tweakBytes_eq_iff] at htweak
  simp [hashDomainFields, TweakFields.mk.injEq] at htweak

theorem decodeProbe?_tweakableHashInput_ftsNode
    (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (level nodeIdx : Nat) (payload : HashInput) :
    decodeProbe? parameter
      (tweakableHashInput parameter (.ftsNode index tree level nodeIdx) payload) = none := by
  rw [decodeProbe?_eq_none_iff]
  rintro ⟨coordinate, candidate⟩ hmatches
  cases coordinate with
  | chainStart lay otsTree leafIdx chainIdx =>
      obtain ⟨step, hstep, hinput⟩ := hmatches
      exact tweakableHashInput_ftsNode_ne_chain parameter index tree level nodeIdx payload lay
        otsTree leafIdx chainIdx step _ hinput
  | position position =>
      cases position with
      | chain lay otsTree leafIdx chainIdx step =>
          simp only [Probe.MatchesInput] at hmatches
          split at hmatches
          · obtain ⟨nextStep, hnext, hinput⟩ := hmatches
            exact tweakableHashInput_ftsNode_ne_chain parameter index tree level nodeIdx payload
              lay otsTree leafIdx chainIdx nextStep _ hinput
          · obtain ⟨hchainZero, candidatePayload, hinput, hslot⟩ := hmatches
            exact tweakableHashInput_ftsNode_ne_leaf parameter index tree level nodeIdx payload lay
              otsTree leafIdx candidatePayload hinput
      | leaf => simp [Probe.MatchesInput] at hmatches
      | node => simp [Probe.MatchesInput] at hmatches
      | ftsLeaf => simp [Probe.MatchesInput] at hmatches
      | ftsNode => simp [Probe.MatchesInput] at hmatches
      | ftsRoots => simp [Probe.MatchesInput] at hmatches

theorem ChainProbeAccounted.ensure
    {parameter : PublicParameter} {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (haccounted : ChainProbeAccounted parameter allowed state cache)
    (coordinate : Coordinate) :
    ChainProbeAccounted parameter allowed (state.ensure coordinate) cache := by
  change ChainProbeAccounted parameter allowed state cache
  exact haccounted

theorem ChainProbeAccounted.addPending
    {parameter : PublicParameter} {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (haccounted : ChainProbeAccounted parameter allowed state cache)
    (coordinate : Coordinate) (candidate : Digest) :
    ChainProbeAccounted parameter allowed (state.addPending coordinate candidate) cache := by
  intro probe input hmatches hcached hnotAllowed
  have hpending := haccounted probe input hmatches hcached hnotAllowed
  simp [LazyRevealProbe.State.pendingAt] at hpending
  simp [LazyRevealProbe.State.pendingAt, LazyRevealProbe.State.addPending]
  exact Or.inr hpending

theorem ChainProbeAccounted.publish
    {parameter : PublicParameter} {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (haccounted : ChainProbeAccounted parameter allowed state cache)
    (coordinate : Coordinate) :
    ChainProbeAccounted parameter allowed (state.publish coordinate) cache := by
  change ChainProbeAccounted parameter allowed state cache
  exact haccounted

theorem ChainProbeAccounted.updateHidden
    {parameter : PublicParameter} {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (haccounted : ChainProbeAccounted parameter allowed state cache)
    (coordinate : Coordinate) (output : HashOutput) :
    ChainProbeAccounted parameter allowed state
      (Function.update cache (.hidden coordinate) (some output)) := by
  intro probe input hmatches hcached hnotAllowed
  simp [Function.update] at hcached
  exact haccounted probe input hmatches hcached hnotAllowed

theorem ChainProbeAccounted.materialize
    {parameter : PublicParameter} {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (haccounted : ChainProbeAccounted parameter allowed state cache)
    (coordinate : Coordinate) (output : HashOutput)
    (hallowed : IsChainCoordinate coordinate → allowed coordinate) :
    ChainProbeAccounted parameter allowed (state.materialize coordinate output) cache := by
  intro probe input hmatches hcached hnotAllowed
  have hpending := haccounted probe input hmatches hcached hnotAllowed
  have hne : probe.coordinate ≠ coordinate := by
    intro heq
    rw [heq] at hnotAllowed
    exact hnotAllowed (hallowed (heq ▸ probe.isChainCoordinate_of_matchesInput hmatches))
  simpa [LazyRevealProbe.State.pendingAt, LazyRevealProbe.State.materialize,
    LazyRevealProbe.State.pendingAway, hne] using hpending

theorem ChainProbeAccounted.materialize_publish
    {parameter : PublicParameter} {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (haccounted : ChainProbeAccounted parameter allowed state cache)
    (coordinate : Coordinate) (output : HashOutput)
    (hallowed : IsChainCoordinate coordinate → allowed coordinate) :
    ChainProbeAccounted parameter allowed
      ((state.materialize coordinate output).publish coordinate) cache := by
  intro probe input hmatches hcached hnotAllowed
  have hpending := haccounted probe input hmatches hcached hnotAllowed
  have hne : probe.coordinate ≠ coordinate := by
    intro heq
    rw [heq] at hnotAllowed
    exact hnotAllowed (hallowed (heq ▸ probe.isChainCoordinate_of_matchesInput hmatches))
  simpa [LazyRevealProbe.State.pendingAt, LazyRevealProbe.State.materialize,
    LazyRevealProbe.State.publish, LazyRevealProbe.State.pendingAway, hne] using hpending

theorem secured_materialize_publish
    {allowed : Coordinate → Prop} {state : LazyRevealProbe.State Coordinate}
    (candidate : Probe) (coordinate : Coordinate) (output : HashOutput)
    (hsourceChain : IsChainCoordinate candidate.coordinate)
    (hallowed : IsChainCoordinate coordinate → allowed coordinate)
    (hsecured : allowed candidate.coordinate ∨
      candidate.candidate ∈ state.pendingAt candidate.coordinate) :
    allowed candidate.coordinate ∨ candidate.candidate ∈
      ((state.materialize coordinate output).publish coordinate).pendingAt candidate.coordinate := by
  rcases hsecured with hcovered | hpending
  · exact Or.inl hcovered
  · by_cases heq : candidate.coordinate = coordinate
    · exact Or.inl (heq ▸ hallowed (heq ▸ hsourceChain))
    · right
      simpa [LazyRevealProbe.State.pendingAt, LazyRevealProbe.State.materialize,
        LazyRevealProbe.State.publish, LazyRevealProbe.State.pendingAway, heq] using hpending

theorem ChainProbeAccounted.updateOrdinary_of_decode_none
    {parameter : PublicParameter} {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (haccounted : ChainProbeAccounted parameter allowed state cache)
    (input : HashInput) (output : HashOutput) (hdecode : decodeProbe? parameter input = none) :
    ChainProbeAccounted parameter allowed state
      (Function.update cache (.ordinary input) (some output)) := by
  intro probe other hmatches hcached hnotAllowed
  by_cases heq : other = input
  · subst other
    exact ((decodeProbe?_eq_none_iff parameter input).1 hdecode probe hmatches).elim
  · simp [Function.update, heq] at hcached
    exact haccounted probe other hmatches hcached hnotAllowed

theorem ChainProbeAccounted.addDecodedPending_updateOrdinary
    {parameter : PublicParameter} {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (haccounted : ChainProbeAccounted parameter allowed state cache)
    (candidate : Probe) (input : HashInput) (output : HashOutput)
    (hdecode : decodeProbe? parameter input = some candidate) :
    ChainProbeAccounted parameter allowed
      (state.addPending candidate.coordinate candidate.candidate)
      (Function.update cache (.ordinary input) (some output)) := by
  intro probe other hmatches hcached hnotAllowed
  by_cases heq : other = input
  · subst other
    have hcandidateMatches := (decodeProbe?_eq_some_iff parameter input candidate).1 hdecode
    have hprobe : probe = candidate :=
      Probe.matchesInput_unique parameter input hmatches hcandidateMatches
    subst probe
    exact LazyRevealProbe.State.pendingAt_addPending_self state candidate.coordinate
      candidate.candidate
  · simp [Function.update, heq] at hcached
    exact haccounted.addPending candidate.coordinate candidate.candidate probe other hmatches
      hcached hnotAllowed

theorem ChainProbeAccounted.updateOrdinary_of_decoded_allowed
    {parameter : PublicParameter} {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (haccounted : ChainProbeAccounted parameter allowed state cache)
    (candidate : Probe) (input : HashInput) (output : HashOutput)
    (hdecode : decodeProbe? parameter input = some candidate)
    (hallowed : allowed candidate.coordinate) :
    ChainProbeAccounted parameter allowed state
      (Function.update cache (.ordinary input) (some output)) := by
  intro probe other hmatches hcached hnotAllowed
  by_cases heq : other = input
  · subst other
    have hcandidateMatches := (decodeProbe?_eq_some_iff parameter input candidate).1 hdecode
    have hprobe : probe = candidate :=
      Probe.matchesInput_unique parameter input hmatches hcandidateMatches
    subst probe
    exact (hnotAllowed hallowed).elim
  · simp [Function.update, heq] at hcached
    exact haccounted probe other hmatches hcached hnotAllowed

theorem ChainProbeAccounted.updateOrdinary_of_decoded_secured
    {parameter : PublicParameter} {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (haccounted : ChainProbeAccounted parameter allowed state cache)
    (candidate : Probe) (input : HashInput) (output : HashOutput)
    (hdecode : decodeProbe? parameter input = some candidate)
    (hsecured : allowed candidate.coordinate ∨
      candidate.candidate ∈ state.pendingAt candidate.coordinate) :
    ChainProbeAccounted parameter allowed state
      (Function.update cache (.ordinary input) (some output)) := by
  rcases hsecured with hallowed | hpending
  · exact haccounted.updateOrdinary_of_decoded_allowed candidate input output hdecode hallowed
  · intro probe other hmatches hcached hnotAllowed
    by_cases heq : other = input
    · subst other
      have hcandidateMatches := (decodeProbe?_eq_some_iff parameter input candidate).1 hdecode
      have hprobe : probe = candidate :=
        Probe.matchesInput_unique parameter input hmatches hcandidateMatches
      subst probe
      exact hpending
    · simp [Function.update, heq] at hcached
      exact haccounted probe other hmatches hcached hnotAllowed

def ChainInvariant (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) : Prop :=
  ChainState.ValidFor allowed state ∧ ChainProbeAccounted parameter allowed state cache

theorem ChainState.ValidFor.mono
    {initial final : Coordinate → Prop} {state : LazyRevealProbe.State Coordinate}
    (hvalid : ChainState.ValidFor initial state)
    (hle : ∀ coordinate, initial coordinate → final coordinate) :
    ChainState.ValidFor final state := by
  intro coordinate hchain
  have hcoordinate := hvalid coordinate hchain
  exact ⟨hcoordinate.1, hcoordinate.2.1,
    fun hrevealed => hle coordinate (hcoordinate.2.2 hrevealed)⟩

theorem ChainProbeAccounted.mono
    {parameter : PublicParameter} {initial final : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (haccounted : ChainProbeAccounted parameter initial state cache)
    (hle : ∀ coordinate, initial coordinate → final coordinate) :
    ChainProbeAccounted parameter final state cache := by
  intro probe input hmatches hcached hnotAllowed
  exact haccounted probe input hmatches hcached
    (fun hinitial => hnotAllowed (hle probe.coordinate hinitial))

theorem ChainInvariant.mono
    {parameter : PublicParameter} {initial final : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hinvariant : ChainInvariant parameter initial state cache)
    (hle : ∀ coordinate, initial coordinate → final coordinate) :
    ChainInvariant parameter final state cache :=
  ⟨hinvariant.1.mono hle, hinvariant.2.mono hle⟩

def PreservesChainInvariant (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache,
    ChainInvariant parameter allowed state cache →
      LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
        support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
      ChainInvariant parameter allowed finalState finalCache

theorem PreservesChainInvariant.bind
    {parameter : PublicParameter} {allowed : Coordinate → Prop}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : PreservesChainInvariant parameter allowed left)
    (hnext : ∀ value, PreservesChainInvariant parameter allowed (next value)) :
    PreservesChainInvariant parameter allowed (left >>= next) := by
  intro state cache fuel finalState remaining result finalCache hinvariant hresult
  change LazyRevealProbe.RawResult.done finalState remaining (result, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun leftResult => (next leftResult.1).run leftResult.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining leftResult =>
      rcases leftResult with ⟨leftValue, middleCache⟩
      exact hnext leftValue middleState middleCache middleRemaining finalState remaining result
        finalCache (hleft state cache fuel middleState middleRemaining leftValue middleCache
          hinvariant hraw) hrest

theorem preservesChainInvariant_pure
    (parameter : PublicParameter) (allowed : Coordinate → Prop) (value : alpha) :
    PreservesChainInvariant parameter allowed
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro state cache fuel finalState remaining result finalCache hinvariant hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hinvariant

theorem preservesChainInvariant_probe
    (parameter : PublicParameter) (allowed : Coordinate → Prop) (candidate : Probe) :
    PreservesChainInvariant parameter allowed (probe candidate) := by
  intro state cache fuel finalState remaining value finalCache hinvariant hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate >>= fun output =>
        pure (output, cache))) at hresult
  rw [LazyRevealProbe.probeQuery, LazyRevealProbe.runRaw_probe_query_bind] at hresult
  cases fuel with
  | zero => simp at hresult
  | succ remainingFuel =>
      simp only at hresult
      by_cases hrevealed : candidate.coordinate ∈ state.revealed
      · rw [if_pos hrevealed] at hresult
        simp [LazyRevealProbe.runRaw] at hresult
        rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
        exact hinvariant
      · rw [if_neg hrevealed] at hresult
        simp [LazyRevealProbe.runRaw] at hresult
        rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
        refine ⟨?_, hinvariant.2.addPending candidate.coordinate candidate.candidate⟩
        simpa [ChainState.ValidFor, LazyRevealProbe.State.addPending] using hinvariant.1

theorem preservesChainInvariant_ensureCoordinate
    (parameter : PublicParameter) (allowed : Coordinate → Prop) (coordinate : Coordinate) :
    PreservesChainInvariant parameter allowed (ensureCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hinvariant hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.ensureQuery coordinate >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.ensureQuery, LazyRevealProbe.runRaw_ensure_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨?_, hinvariant.2.ensure coordinate⟩
  simpa [ChainState.ValidFor, LazyRevealProbe.State.ensure] using hinvariant.1

theorem preservesChainInvariant_peekCoordinate
    (parameter : PublicParameter) (allowed : Coordinate → Prop) (coordinate : Coordinate) :
    PreservesChainInvariant parameter allowed (peekCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hinvariant hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.peekQuery coordinate >>= fun output =>
        pure (truncateHash <$> output, cache))) at hresult
  rw [LazyRevealProbe.peekQuery, LazyRevealProbe.runRaw_peek_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hinvariant

theorem preservesChainInvariant_peekPositionValues
    (parameter : PublicParameter) (allowed : Coordinate → Prop) (positions : List Position) :
    PreservesChainInvariant parameter allowed (peekPositionValues positions) := by
  induction positions with
  | nil => exact preservesChainInvariant_pure parameter allowed (some [])
  | cons position remaining ih =>
      rw [peekPositionValues]
      exact (preservesChainInvariant_peekCoordinate parameter allowed (.position position)).bind
        fun value => match value with
        | none => preservesChainInvariant_pure parameter allowed none
        | some _ => ih.bind fun values =>
            match values with
            | none => preservesChainInvariant_pure parameter allowed none
            | some _ => preservesChainInvariant_pure parameter allowed _

theorem preservesChainInvariant_peekTableInput
    (parameter : PublicParameter) (allowed : Coordinate → Prop) (coordinate : Coordinate) :
    PreservesChainInvariant parameter allowed (peekTableInput parameter coordinate) := by
  cases coordinate with
  | chainStart => exact preservesChainInvariant_pure parameter allowed none
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero]
            exact (preservesChainInvariant_peekCoordinate parameter allowed
              (.chainStart lay tree leafIdx chainIdx)).bind fun value =>
                match value with
                | none => preservesChainInvariant_pure parameter allowed none
                | some _ => preservesChainInvariant_pure parameter allowed _
          · rw [if_neg hzero]
            exact (preservesChainInvariant_peekPositionValues parameter allowed
              (Position.chain lay tree leafIdx chainIdx step).children).bind fun values =>
                match values with
                | none => preservesChainInvariant_pure parameter allowed none
                | some _ => preservesChainInvariant_pure parameter allowed _
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp only [peekTableInput]
          exact (preservesChainInvariant_peekPositionValues parameter allowed _).bind fun values =>
            match values with
            | none => preservesChainInvariant_pure parameter allowed none
            | some _ => preservesChainInvariant_pure parameter allowed _

def RawReadOnly
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache,
    LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
    finalState = state ∧ remaining = fuel ∧ finalCache = cache

theorem RawReadOnly.pure (value : alpha) :
    RawReadOnly
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro state cache fuel finalState remaining result finalCache hresult
  simp [LazyRevealProbe.runRaw] at hresult
  exact ⟨hresult.1, hresult.2.1, hresult.2.2.2⟩

theorem RawReadOnly.bind
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : RawReadOnly left) (hnext : ∀ value, RawReadOnly (next value)) :
    RawReadOnly (left >>= next) := by
  intro state cache fuel finalState remaining result finalCache hresult
  change LazyRevealProbe.RawResult.done finalState remaining (result, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun leftResult => (next leftResult.1).run leftResult.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining leftResult =>
      rcases leftResult with ⟨leftValue, middleCache⟩
      obtain ⟨hfinalState, hremaining, hfinalCache⟩ := hnext leftValue middleState
        middleCache middleRemaining finalState remaining result finalCache hrest
      obtain ⟨hmiddleState, hmiddleRemaining, hmiddleCache⟩ := hleft state cache fuel
        middleState middleRemaining leftValue middleCache hraw
      exact ⟨hfinalState.trans hmiddleState, hremaining.trans hmiddleRemaining,
        hfinalCache.trans hmiddleCache⟩

theorem RawReadOnly.entryPreserving
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    (hreadonly : RawReadOnly computation) (input : HashInput) :
    OrdinaryEntryPreserving input computation := by
  intro state cache fuel finalState remaining value finalCache output hcached hresult
  rw [hreadonly state cache fuel finalState remaining value finalCache hresult |>.2.2]
  exact hcached

theorem rawReadOnly_peekCoordinate (coordinate : Coordinate) :
    RawReadOnly (peekCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.peekQuery coordinate >>= fun output =>
        pure (truncateHash <$> output, cache))) at hresult
  rw [LazyRevealProbe.peekQuery, LazyRevealProbe.runRaw_peek_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  exact ⟨hresult.1, hresult.2.1, hresult.2.2.2⟩

theorem rawReadOnly_peekPositionValues (positions : List Position) :
    RawReadOnly (peekPositionValues positions) := by
  induction positions with
  | nil => exact RawReadOnly.pure (some [])
  | cons position remaining ih =>
      rw [peekPositionValues]
      exact (rawReadOnly_peekCoordinate (.position position)).bind fun value =>
        match value with
        | none => RawReadOnly.pure none
        | some _ => ih.bind fun values =>
            match values with
            | none => RawReadOnly.pure none
            | some _ => RawReadOnly.pure _

theorem rawReadOnly_peekTableInput (parameter : PublicParameter) (coordinate : Coordinate) :
    RawReadOnly (peekTableInput parameter coordinate) := by
  cases coordinate with
  | chainStart => exact RawReadOnly.pure none
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero]
            exact (rawReadOnly_peekCoordinate (.chainStart lay tree leafIdx chainIdx)).bind
              fun value => match value with
              | none => RawReadOnly.pure none
              | some _ => RawReadOnly.pure _
          · rw [if_neg hzero]
            exact (rawReadOnly_peekPositionValues
              (Position.chain lay tree leafIdx chainIdx step).children).bind fun values =>
                match values with
                | none => RawReadOnly.pure none
                | some _ => RawReadOnly.pure _
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp only [peekTableInput]
          exact (rawReadOnly_peekPositionValues _).bind fun values =>
            match values with
            | none => RawReadOnly.pure none
            | some _ => RawReadOnly.pure _

theorem ordinaryEntryPreserving_revealCoordinateOutput
    (input : HashInput) (coordinate : Coordinate) :
    OrdinaryEntryPreserving input (revealCoordinateOutput coordinate) := by
  intro state cache fuel finalState remaining value finalCache output hcached hresult
  rw [revealCoordinateOutput_run, LazyRevealProbe.revealQuery,
    LazyRevealProbe.runRaw_reveal_query_bind] at hresult
  cases hvalue : state.values coordinate with
  | some existing =>
      rw [hvalue] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      simpa [Function.update] using hcached
  | none =>
      rw [hvalue, mem_support_bind_iff] at hresult
      obtain ⟨sampled, _, hsampled⟩ := hresult
      by_cases hhit : state.hitAt coordinate sampled
      · rw [if_pos hhit] at hsampled
        simp at hsampled
      · rw [if_neg hhit] at hsampled
        simp [LazyRevealProbe.runRaw] at hsampled
        rcases hsampled with ⟨rfl, rfl, rfl, rfl⟩
        simpa [Function.update] using hcached

theorem ordinaryEntryPreserving_modifyOrdinary_of_ne
    (input other : HashInput) (answer : HashOutput) (hne : input ≠ other) :
    OrdinaryEntryPreserving input
      (modify fun cache : SplitHashCache =>
        Function.update cache (.ordinary other) (some answer)) := by
  intro state cache fuel finalState remaining value finalCache output hcached hresult
  simp [StateT.run_modify, LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  simpa [Function.update, hne] using hcached

theorem cachesOrdinaryInput_modifyOrdinary
    (input : HashInput) (answer : HashOutput) :
    CachesOrdinaryInput input
      (modify fun cache : SplitHashCache =>
        Function.update cache (.ordinary input) (some answer)) := by
  intro state cache fuel finalState remaining value finalCache hresult
  simp [StateT.run_modify, LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  simp [Function.update]

theorem ordinaryEntryPreserving_probe (input : HashInput) (candidate : Probe) :
    OrdinaryEntryPreserving input (probe candidate) := by
  intro state cache fuel finalState remaining value finalCache output hcached hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate >>= fun result =>
        pure (result, cache))) at hresult
  rw [LazyRevealProbe.probeQuery, LazyRevealProbe.runRaw_probe_query_bind] at hresult
  cases fuel with
  | zero => simp at hresult
  | succ remainingFuel =>
      rw [show remainingFuel + 1 = Nat.succ remainingFuel by omega] at hresult
      simp only at hresult
      by_cases hrevealed : candidate.coordinate ∈ state.revealed
      · rw [if_pos hrevealed] at hresult
        simp [LazyRevealProbe.runRaw] at hresult
        rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
        exact hcached
      · rw [if_neg hrevealed] at hresult
        simp [LazyRevealProbe.runRaw] at hresult
        rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
        exact hcached

theorem ordinaryEntryPreserving_publishCoordinate
    (input : HashInput) (coordinate : Coordinate) :
    OrdinaryEntryPreserving input (publishCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache output hcached hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.publishQuery coordinate >>= fun result => pure (result, cache))) at hresult
  rw [LazyRevealProbe.publishQuery, LazyRevealProbe.runRaw_publish_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hcached

theorem ordinaryEntryPreserving_resolveKnownInput_of_ne
    (parameter : PublicParameter) (input query : HashInput) (coordinate : Coordinate)
    (hne : input ≠ query) :
    OrdinaryEntryPreserving input (resolveKnownInput parameter coordinate query) := by
  unfold resolveKnownInput
  exact (rawReadOnly_peekTableInput parameter coordinate).entryPreserving input |>.bind
    fun knownInput => match knownInput with
    | none => (ordinaryCacheIncreasing_splitHashQuery_ordinary query).entryPreserving input
    | some knownInput => by
        simp only
        by_cases hexact : knownInput = query
        · rw [if_pos hexact]
          exact (ordinaryEntryPreserving_revealCoordinateOutput input coordinate).bind fun answer =>
            (ordinaryEntryPreserving_publishCoordinate input coordinate).bind
              fun _ => (ordinaryEntryPreserving_modifyOrdinary_of_ne input query answer hne).bind
                fun _ => OrdinaryEntryPreserving.pure input answer
        · rw [if_neg hexact]
          exact (ordinaryCacheIncreasing_splitHashQuery_ordinary query).entryPreserving input

theorem cachesOrdinaryInput_resolveKnownInput
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput) :
    CachesOrdinaryInput input (resolveKnownInput parameter coordinate input) := by
  unfold resolveKnownInput
  apply CachesOrdinaryInput.bind_right
  intro knownInput
  cases knownInput with
  | none => exact cachesOrdinaryInput_splitHashQuery input
  | some knownInput =>
      simp only
      by_cases hexact : knownInput = input
      · rw [if_pos hexact]
        apply CachesOrdinaryInput.bind_right
        intro answer
        apply CachesOrdinaryInput.bind_right
        intro _
        exact (cachesOrdinaryInput_modifyOrdinary input answer).bind_preserving fun _ =>
          OrdinaryEntryPreserving.pure input answer
      · rw [if_neg hexact]
        exact cachesOrdinaryInput_splitHashQuery input

theorem cachesOrdinaryInput_probingHashQuery
    (parameter : PublicParameter) (input : HashInput) :
    CachesOrdinaryInput input (probingHashQuery parameter input) := by
  unfold probingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      exact CachesOrdinaryInput.bind_right fun _ =>
        cachesOrdinaryInput_resolveKnownInput parameter candidate.outputCoordinate input
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => exact cachesOrdinaryInput_splitHashQuery input
      | some position =>
          cases position with
          | chain lay tree leafIdx chainIdx step =>
              exact cachesOrdinaryInput_resolveKnownInput parameter
                (.position (.chain lay tree leafIdx chainIdx step)) input
          | leaf lay tree leafIdx =>
              exact cachesOrdinaryInput_resolveKnownInput parameter
                (.position (.leaf lay tree leafIdx)) input
          | node lay tree level nodeIdx =>
              exact cachesOrdinaryInput_resolveKnownInput parameter
                (.position (.node lay tree level nodeIdx)) input
          | ftsLeaf | ftsNode | ftsRoots => exact cachesOrdinaryInput_splitHashQuery input

theorem ordinaryEntryPreserving_probingHashQuery_self
    (parameter : PublicParameter) (input : HashInput)
    (hstable : StableOrdinaryInput parameter input) :
    OrdinaryEntryPreserving input (probingHashQuery parameter input) := by
  unfold probingHashQuery
  rw [hstable.1]
  cases hposition : decodePosition? parameter input with
  | none =>
      exact (ordinaryCacheIncreasing_splitHashQuery_ordinary input).entryPreserving input
  | some position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          exact (hstable.2 _ hposition (by trivial)).elim
      | leaf lay tree leafIdx =>
          exact (hstable.2 _ hposition (by trivial)).elim
      | node lay tree level nodeIdx =>
          exact (hstable.2 _ hposition (by trivial)).elim
      | ftsLeaf | ftsNode | ftsRoots =>
          exact (ordinaryCacheIncreasing_splitHashQuery_ordinary input).entryPreserving input

theorem ordinaryEntryPreserving_probingHashQuery_of_ne
    (parameter : PublicParameter) (input query : HashInput) (hne : input ≠ query) :
    OrdinaryEntryPreserving input (probingHashQuery parameter query) := by
  unfold probingHashQuery
  cases hprobe : decodeProbe? parameter query with
  | some candidate =>
      exact (ordinaryEntryPreserving_probe input candidate).bind fun _ =>
        ordinaryEntryPreserving_resolveKnownInput_of_ne parameter input query
          candidate.outputCoordinate hne
  | none =>
      cases hposition : decodePosition? parameter query with
      | none =>
          exact (ordinaryCacheIncreasing_splitHashQuery_ordinary query).entryPreserving input
      | some position =>
          cases position with
          | chain lay tree leafIdx chainIdx step =>
              exact ordinaryEntryPreserving_resolveKnownInput_of_ne parameter input query _ hne
          | leaf lay tree leafIdx =>
              exact ordinaryEntryPreserving_resolveKnownInput_of_ne parameter input query _ hne
          | node lay tree level nodeIdx =>
              exact ordinaryEntryPreserving_resolveKnownInput_of_ne parameter input query _ hne
          | ftsLeaf | ftsNode | ftsRoots =>
              exact (ordinaryCacheIncreasing_splitHashQuery_ordinary query).entryPreserving input

theorem ordinaryEntryPreserving_probingHashQuery
    (parameter : PublicParameter) (input query : HashInput)
    (hstable : StableOrdinaryInput parameter input) :
    OrdinaryEntryPreserving input (probingHashQuery parameter query) := by
  by_cases heq : input = query
  · subst query
    exact ordinaryEntryPreserving_probingHashQuery_self parameter input hstable
  · exact ordinaryEntryPreserving_probingHashQuery_of_ne parameter input query heq

def OrdinaryEntryPreservingImpl {spec : OracleSpec ι} (input : HashInput)
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))) : Prop :=
  ∀ query, OrdinaryEntryPreserving input (impl query)

theorem OrdinaryEntryPreservingImpl.simulateQ {spec : OracleSpec ι}
    {input : HashInput}
    {impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))}
    (himpl : OrdinaryEntryPreservingImpl input impl)
    (computation : OracleComp spec alpha) :
    OrdinaryEntryPreserving input (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact OrdinaryEntryPreserving.pure input value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (himpl query).bind ih

theorem ordinaryEntryPreservingImpl_splitUniformImpl (input : HashInput) :
    OrdinaryEntryPreservingImpl input splitUniformImpl := by
  intro n
  have hincreasing := ordinaryCacheIncreasing_simulateQ_splitUniformImpl
    (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
  simpa [splitUniformImpl] using hincreasing.entryPreserving input

theorem ordinaryEntryPreservingImpl_probingHashImpl
    (parameter : PublicParameter) (input : HashInput)
    (hstable : StableOrdinaryInput parameter input) :
    OrdinaryEntryPreservingImpl input (probingHashImpl parameter) :=
  fun query => ordinaryEntryPreserving_probingHashQuery parameter input query hstable

theorem ordinaryEntryPreservingImpl_probingRomImpl
    (parameter : PublicParameter) (input : HashInput)
    (hstable : StableOrdinaryInput parameter input) :
    OrdinaryEntryPreservingImpl input (probingRomImpl parameter) := by
  intro query
  cases query with
  | inl query => exact ordinaryEntryPreservingImpl_splitUniformImpl input query
  | inr query =>
      exact ordinaryEntryPreservingImpl_probingHashImpl parameter input hstable query

theorem chainInvariant_splitHashQuery_ordinary_of_decoded_secured
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (candidate : Probe) (input : HashInput)
    (hdecode : decodeProbe? parameter input = some candidate)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat)
    (finalState : LazyRevealProbe.State Coordinate) (remaining : Nat)
    (value : HashOutput) (finalCache : SplitHashCache)
    (hinvariant : ChainInvariant parameter allowed state cache)
    (hsecured : allowed candidate.coordinate ∨
      candidate.candidate ∈ state.pendingAt candidate.coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((splitHashQuery (.ordinary input)).run cache))) :
    ChainInvariant parameter allowed finalState finalCache := by
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache (.ordinary input) with
  | some output =>
      rw [hlookup] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact hinvariant
  | none =>
      rw [hlookup] at hresult
      dsimp only at hresult
      change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
        (LazyRevealProbe.runRaw state fuel
          (LazyRevealProbe.hashOutputQuery >>= fun output =>
            pure (output, Function.update cache (.ordinary input) (some output)))) at hresult
      rw [LazyRevealProbe.hashOutputQuery,
        LazyRevealProbe.runRaw_hashOutput_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨output, _, hdone⟩ := hresult
      simp [LazyRevealProbe.runRaw] at hdone
      rcases hdone with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨hinvariant.1,
        hinvariant.2.updateOrdinary_of_decoded_secured candidate input value hdecode hsecured⟩

theorem preservesChainInvariant_splitHashQuery_ordinary_of_decode_none
    (parameter : PublicParameter) (allowed : Coordinate → Prop) (input : HashInput)
    (hdecode : decodeProbe? parameter input = none) :
    PreservesChainInvariant parameter allowed (splitHashQuery (.ordinary input)) := by
  intro state cache fuel finalState remaining value finalCache hinvariant hresult
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache (.ordinary input) with
  | some output =>
      rw [hlookup] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact hinvariant
  | none =>
      rw [hlookup] at hresult
      dsimp only at hresult
      change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
        (LazyRevealProbe.runRaw state fuel
          (LazyRevealProbe.hashOutputQuery >>= fun output =>
            pure (output, Function.update cache (.ordinary input) (some output)))) at hresult
      rw [LazyRevealProbe.hashOutputQuery,
        LazyRevealProbe.runRaw_hashOutput_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨output, _, hdone⟩ := hresult
      simp [LazyRevealProbe.runRaw] at hdone
      rcases hdone with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨hinvariant.1,
        hinvariant.2.updateOrdinary_of_decode_none input value hdecode⟩

theorem ChainState.ValidFor.value_eq_none_of_not_allowed
    {allowed : Coordinate → Prop} {state : LazyRevealProbe.State Coordinate}
    (hvalid : ChainState.ValidFor allowed state) {coordinate : Coordinate}
    (hchain : IsChainCoordinate coordinate) (hnotAllowed : ¬allowed coordinate) :
    state.values coordinate = none := by
  by_contra hvalue
  exact hnotAllowed ((hvalid coordinate hchain).2.2 ((hvalid coordinate hchain).1 hvalue))

theorem ChainState.ValidFor.not_revealed_of_not_allowed
    {allowed : Coordinate → Prop} {state : LazyRevealProbe.State Coordinate}
    (hvalid : ChainState.ValidFor allowed state) {coordinate : Coordinate}
    (hchain : IsChainCoordinate coordinate) (hnotAllowed : ¬allowed coordinate) :
    coordinate ∉ state.revealed := by
  intro hrevealed
  exact hnotAllowed ((hvalid coordinate hchain).2.2 hrevealed)

theorem ChainState.validFor_empty (allowed : Coordinate → Prop) :
    ChainState.ValidFor allowed (LazyRevealProbe.State.empty :
      LazyRevealProbe.State Coordinate) := by
  intro coordinate hchain
  simp [LazyRevealProbe.State.empty]

theorem ChainState.ValidFor.ensure {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} (hvalid : ChainState.ValidFor allowed state)
    (coordinate : Coordinate) : ChainState.ValidFor allowed (state.ensure coordinate) := by
  simpa [ChainState.ValidFor, LazyRevealProbe.State.ensure] using hvalid

theorem ChainState.ValidFor.addPending {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} (hvalid : ChainState.ValidFor allowed state)
    (coordinate : Coordinate) (candidate : Digest) :
    ChainState.ValidFor allowed (state.addPending coordinate candidate) := by
  simpa [ChainState.ValidFor, LazyRevealProbe.State.addPending] using hvalid

theorem ChainState.ValidFor.clearPending {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} (hvalid : ChainState.ValidFor allowed state)
    (coordinate : Coordinate) : ChainState.ValidFor allowed (state.clearPending coordinate) := by
  simpa [ChainState.ValidFor, LazyRevealProbe.State.clearPending] using hvalid

theorem ChainState.ValidFor.materialize_of_not_chain {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} (hvalid : ChainState.ValidFor allowed state)
    (coordinate : Coordinate) (output : HashOutput) (hnotChain : ¬IsChainCoordinate coordinate) :
    ChainState.ValidFor allowed (state.materialize coordinate output) := by
  intro other hchain
  have hne : other ≠ coordinate := by
    intro heq
    exact hnotChain (heq ▸ hchain)
  simpa [LazyRevealProbe.State.materialize, Function.update, hne] using hvalid other hchain

theorem ChainState.ValidFor.publish {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} (hvalid : ChainState.ValidFor allowed state)
    (coordinate : Coordinate) (hvalue : state.values coordinate ≠ none)
    (hallowed : IsChainCoordinate coordinate → allowed coordinate) :
    ChainState.ValidFor allowed (state.publish coordinate) := by
  intro other hchain
  by_cases heq : other = coordinate
  · subst other
    have hrevealed : coordinate ∈ (state.publish coordinate).revealed := by
      simp [LazyRevealProbe.State.publish]
    exact ⟨fun _ => hrevealed, fun _ => hvalue, fun _ => hallowed hchain⟩
  · have hold := hvalid other hchain
    simpa [LazyRevealProbe.State.publish, heq] using hold

theorem ChainState.ValidFor.materialize_publish {allowed : Coordinate → Prop}
    {state : LazyRevealProbe.State Coordinate} (hvalid : ChainState.ValidFor allowed state)
    (coordinate : Coordinate) (output : HashOutput)
    (hallowed : IsChainCoordinate coordinate → allowed coordinate) :
    ChainState.ValidFor allowed ((state.materialize coordinate output).publish coordinate) := by
  intro other hchain
  by_cases heq : other = coordinate
  · subst other
    simp [LazyRevealProbe.State.materialize, LazyRevealProbe.State.publish, Function.update,
      hallowed hchain]
  · have hold := hvalid other hchain
    simpa [LazyRevealProbe.State.materialize, LazyRevealProbe.State.publish, Function.update,
      heq] using hold

def PreservesChainValid (allowed : Coordinate → Prop)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache,
    ChainState.ValidFor allowed state →
      LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
        support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
      ChainState.ValidFor allowed finalState

theorem PreservesChainValid.bind
    {allowed : Coordinate → Prop}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : PreservesChainValid allowed left)
    (hnext : ∀ value, PreservesChainValid allowed (next value)) :
    PreservesChainValid allowed (left >>= next) := by
  intro state cache fuel finalState remaining result finalCache hvalid hresult
  change LazyRevealProbe.RawResult.done finalState remaining (result, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun leftResult => (next leftResult.1).run leftResult.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining leftResult =>
      rcases leftResult with ⟨leftValue, middleCache⟩
      exact hnext leftValue middleState middleCache middleRemaining finalState remaining result
        finalCache (hleft state cache fuel middleState middleRemaining leftValue middleCache
          hvalid hraw) hrest

theorem preservesChainValid_pure (allowed : Coordinate → Prop) (value : alpha) :
    PreservesChainValid allowed
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro state cache fuel finalState remaining result finalCache hvalid hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hvalid

theorem preservesChainValid_splitHashQuery_ordinary (allowed : Coordinate → Prop)
    (input : HashInput) : PreservesChainValid allowed (splitHashQuery (.ordinary input)) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache (.ordinary input) with
  | some output =>
      rw [hlookup] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact hvalid
  | none =>
      rw [hlookup] at hresult
      dsimp only at hresult
      change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
        (LazyRevealProbe.runRaw state fuel
          (LazyRevealProbe.hashOutputQuery >>= fun output =>
            pure (output, Function.update cache (.ordinary input) (some output)))) at hresult
      rw [LazyRevealProbe.hashOutputQuery,
        LazyRevealProbe.runRaw_hashOutput_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨output, _, hdone⟩ := hresult
      simp [LazyRevealProbe.runRaw] at hdone
      rcases hdone with ⟨rfl, rfl, rfl, rfl⟩
      exact hvalid

theorem preservesChainValid_ensureCoordinate (allowed : Coordinate → Prop)
    (coordinate : Coordinate) : PreservesChainValid allowed (ensureCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.ensureQuery coordinate >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.ensureQuery, LazyRevealProbe.runRaw_ensure_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hvalid.ensure coordinate

theorem preservesChainValid_probe (allowed : Coordinate → Prop) (candidate : Probe) :
    PreservesChainValid allowed (probe candidate) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate >>= fun output =>
        pure (output, cache))) at hresult
  rw [LazyRevealProbe.probeQuery, LazyRevealProbe.runRaw_probe_query_bind] at hresult
  cases fuel with
  | zero => simp at hresult
  | succ remainingFuel =>
      simp only at hresult
      by_cases hrevealed : candidate.coordinate ∈ state.revealed
      · rw [if_pos hrevealed] at hresult
        simp [LazyRevealProbe.runRaw] at hresult
        rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
        exact hvalid
      · rw [if_neg hrevealed] at hresult
        simp [LazyRevealProbe.runRaw] at hresult
        rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
        exact hvalid.addPending candidate.coordinate candidate.candidate

theorem preservesChainValid_peekCoordinate (allowed : Coordinate → Prop)
    (coordinate : Coordinate) : PreservesChainValid allowed (peekCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.peekQuery coordinate >>= fun output =>
        pure (truncateHash <$> output, cache))) at hresult
  rw [LazyRevealProbe.peekQuery, LazyRevealProbe.runRaw_peek_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hvalid

theorem mem_runRaw_peekCoordinate_some
    (coordinate : Coordinate) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Digest)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (some value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((peekCoordinate coordinate).run cache))) :
    finalState = state ∧ remaining = fuel ∧ finalCache = cache ∧
      state.values coordinate ≠ none := by
  change LazyRevealProbe.RawResult.done finalState remaining (some value, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.peekQuery coordinate >>= fun output =>
        pure (truncateHash <$> output, cache))) at hresult
  rw [LazyRevealProbe.peekQuery, LazyRevealProbe.runRaw_peek_query_bind] at hresult
  cases hvalue : state.values coordinate with
  | none => simp [hvalue, LazyRevealProbe.runRaw] at hresult
  | some output =>
      simp [hvalue, LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl, by simp⟩

theorem preservesChainValid_peekPositionValues (allowed : Coordinate → Prop)
    (positions : List Position) : PreservesChainValid allowed (peekPositionValues positions) := by
  induction positions with
  | nil => exact preservesChainValid_pure allowed (some [])
  | cons position remaining ih =>
      rw [peekPositionValues]
      exact (preservesChainValid_peekCoordinate allowed (.position position)).bind fun value =>
        match value with
        | none => preservesChainValid_pure allowed none
        | some _ => ih.bind fun values =>
            match values with
            | none => preservesChainValid_pure allowed none
            | some _ => preservesChainValid_pure allowed _

theorem preservesChainValid_peekTableInput (allowed : Coordinate → Prop)
    (parameter : PublicParameter) (coordinate : Coordinate) :
    PreservesChainValid allowed (peekTableInput parameter coordinate) := by
  cases coordinate with
  | chainStart => exact preservesChainValid_pure allowed none
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero]
            exact (preservesChainValid_peekCoordinate allowed
              (.chainStart lay tree leafIdx chainIdx)).bind fun value =>
                match value with
                | none => preservesChainValid_pure allowed none
                | some _ => preservesChainValid_pure allowed _
          · rw [if_neg hzero]
            exact (preservesChainValid_peekPositionValues allowed
              (Position.chain lay tree leafIdx chainIdx step).children).bind fun values =>
                match values with
                | none => preservesChainValid_pure allowed none
                | some _ => preservesChainValid_pure allowed _
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp only [peekTableInput]
          exact (preservesChainValid_peekPositionValues allowed _).bind fun values =>
            match values with
            | none => preservesChainValid_pure allowed none
            | some _ => preservesChainValid_pure allowed _

theorem mem_runRaw_peekTableInput_chain_some_imp_source
    (parameter : PublicParameter) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (step : ChainStep) (knownInput : HashInput)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (some knownInput, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((peekTableInput parameter
          (.position (.chain lay tree leafIdx chainIdx step))).run cache))) :
    ∃ candidate : Probe,
      candidate.outputCoordinate = .position (.chain lay tree leafIdx chainIdx step) ∧
      IsChainCoordinate candidate.coordinate ∧ state.values candidate.coordinate ≠ none := by
  by_cases hzero : step.val = 0
  · rw [peekTableInput, if_pos hzero, StateT.run_bind, LazyRevealProbe.runRaw_bind,
      mem_support_bind_iff] at hresult
    obtain ⟨raw, hpeek, hrest⟩ := hresult
    cases raw with
    | stopped hit => simp at hrest
    | done peekState peekRemaining peekResult =>
        rcases peekResult with ⟨peekValue, peekCache⟩
        cases peekValue with
        | none => simp [LazyRevealProbe.runRaw] at hrest
        | some value =>
            have hvalue := mem_runRaw_peekCoordinate_some
              (.chainStart lay tree leafIdx chainIdx) state peekState cache peekCache fuel
                peekRemaining value hpeek
            refine ⟨⟨.chainStart lay tree leafIdx chainIdx, 0⟩, ?_, trivial,
              hvalue.2.2.2⟩
            have hstep : (⟨0, by norm_num [chainLength, winternitzBits]⟩ : ChainStep) = step :=
              Fin.ext hzero.symm
            simpa [Probe.outputCoordinate] using congrArg
              (fun nextStep => Coordinate.position
                (Position.chain lay tree leafIdx chainIdx nextStep)) hstep
  · have hpositive : 0 < step.val := Nat.pos_of_ne_zero hzero
    let previous : ChainStep := ⟨step.val - 1, by
      have := step.isLt
      omega⟩
    have hchildren : (Position.chain lay tree leafIdx chainIdx step).children =
        [.chain lay tree leafIdx chainIdx previous] := by
      rw [Position.children, dif_pos hpositive]
    rw [peekTableInput, if_neg hzero, hchildren] at hresult
    simp only [peekPositionValues] at hresult
    rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
    obtain ⟨raw, hvalues, hfinish⟩ := hresult
    cases raw with
    | stopped hit => simp at hfinish
    | done valuesState valuesRemaining valuesResult =>
        rcases valuesResult with ⟨values, valuesCache⟩
        cases values with
        | none => simp [LazyRevealProbe.runRaw] at hfinish
        | some values =>
            change LazyRevealProbe.RawResult.done valuesState valuesRemaining
                (some values, valuesCache) ∈ support
              (LazyRevealProbe.runRaw state fuel
                ((peekPositionValues
                  [.chain lay tree leafIdx chainIdx previous]).run cache)) at hvalues
            rw [peekPositionValues, StateT.run_bind, LazyRevealProbe.runRaw_bind,
              mem_support_bind_iff] at hvalues
            obtain ⟨peekRaw, hpeek, hvaluesRest⟩ := hvalues
            cases peekRaw with
            | stopped hit => simp at hvaluesRest
            | done peekState peekRemaining peekResult =>
                rcases peekResult with ⟨peekValue, peekCache⟩
                cases peekValue with
                | none => simp [LazyRevealProbe.runRaw] at hvaluesRest
                | some value =>
                    have hvalue := mem_runRaw_peekCoordinate_some
                      (.position (.chain lay tree leafIdx chainIdx previous)) state peekState
                        cache peekCache fuel peekRemaining value hpeek
                    refine ⟨⟨.position (.chain lay tree leafIdx chainIdx previous), 0⟩,
                      ?_, trivial, hvalue.2.2.2⟩
                    simp only [Probe.outputCoordinate]
                    rw [dif_pos (by dsimp [previous]; omega)]
                    congr 3
                    dsimp [previous]
                    omega

theorem preservesChainValid_revealPublishOrdinary
    (allowed : Coordinate → Prop) (coordinate : Coordinate) (input : HashInput)
    (hallowed : IsChainCoordinate coordinate → allowed coordinate) :
    PreservesChainValid allowed (do
      let output ← revealCoordinateOutput coordinate
      publishCoordinate coordinate
      modify fun cache : SplitHashCache =>
        Function.update cache (.ordinary input) (some output)
      pure output) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hreveal, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealedOutput, revealCache⟩
      have hrevealShape :
          (state.values coordinate ≠ none ∧ revealState = state) ∨
            ∃ output, revealState = state.materialize coordinate output := by
        rw [revealCoordinateOutput_run, LazyRevealProbe.revealQuery,
          LazyRevealProbe.runRaw_reveal_query_bind] at hreveal
        cases hvalue : state.values coordinate with
        | some existing =>
            rw [hvalue] at hreveal
            simp [LazyRevealProbe.runRaw] at hreveal
            rcases hreveal with ⟨rfl, rfl, rfl, rfl⟩
            exact Or.inl ⟨by simp, rfl⟩
        | none =>
            rw [hvalue, mem_support_bind_iff] at hreveal
            obtain ⟨output, _, hsampled⟩ := hreveal
            by_cases hhit : state.hitAt coordinate output
            · rw [if_pos hhit] at hsampled
              simp at hsampled
            · rw [if_neg hhit] at hsampled
              simp [LazyRevealProbe.runRaw] at hsampled
              rcases hsampled with ⟨rfl, rfl, rfl, rfl⟩
              exact Or.inr ⟨revealedOutput, rfl⟩
      simp only at hrest
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
      obtain ⟨publishRaw, hpublish, hfinish⟩ := hrest
      cases publishRaw with
      | stopped hit => simp at hfinish
      | done publishState publishRemaining publishResult =>
          rcases publishResult with ⟨publishedUnit, publishCache⟩
          change LazyRevealProbe.RawResult.done publishState publishRemaining
              (publishedUnit, publishCache) ∈ support
            (LazyRevealProbe.runRaw revealState revealRemaining
              (LazyRevealProbe.publishQuery coordinate >>= fun output =>
                pure (output, revealCache))) at hpublish
          rw [LazyRevealProbe.publishQuery,
            LazyRevealProbe.runRaw_publish_query_bind] at hpublish
          simp [LazyRevealProbe.runRaw] at hpublish
          rcases hpublish with ⟨rfl, rfl, rfl, rfl⟩
          simp [StateT.run_modify, LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
          rcases hrevealShape with ⟨hvalue, rfl⟩ | ⟨output, rfl⟩
          · exact hvalid.publish coordinate hvalue hallowed
          · exact hvalid.materialize_publish coordinate output hallowed

theorem chainInvariant_revealPublishOrdinary_of_decoded_secured
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (coordinate : Coordinate) (input : HashInput) (candidate : Probe)
    (hdecode : decodeProbe? parameter input = some candidate)
    (hallowed : IsChainCoordinate coordinate → allowed coordinate)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat)
    (finalState : LazyRevealProbe.State Coordinate) (remaining : Nat)
    (value : HashOutput) (finalCache : SplitHashCache)
    (hinvariant : ChainInvariant parameter allowed state cache)
    (hsecured : allowed candidate.coordinate ∨
      candidate.candidate ∈ state.pendingAt candidate.coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((do
        let output ← revealCoordinateOutput coordinate
        publishCoordinate coordinate
        modify fun workingCache : SplitHashCache =>
          Function.update workingCache (.ordinary input) (some output)
        pure output).run cache))) :
    ChainInvariant parameter allowed finalState finalCache := by
  have hfinalValid := preservesChainValid_revealPublishOrdinary allowed coordinate input hallowed
    state cache fuel finalState remaining value finalCache hinvariant.1 hresult
  have hcandidateMatches := (decodeProbe?_eq_some_iff parameter input candidate).1 hdecode
  have hsourceChain := candidate.isChainCoordinate_of_matchesInput hcandidateMatches
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hreveal, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealedOutput, revealCache⟩
      rw [revealCoordinateOutput_run, LazyRevealProbe.revealQuery,
        LazyRevealProbe.runRaw_reveal_query_bind] at hreveal
      cases hvalue : state.values coordinate with
      | some existing =>
          rw [hvalue] at hreveal
          simp [LazyRevealProbe.runRaw] at hreveal
          rcases hreveal with ⟨rfl, rfl, rfl, rfl⟩
          simp only at hrest
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
          obtain ⟨publishRaw, hpublish, hfinish⟩ := hrest
          cases publishRaw with
          | stopped hit => simp at hfinish
          | done publishState publishRemaining publishResult =>
              rcases publishResult with ⟨publishedUnit, publishCache⟩
              change LazyRevealProbe.RawResult.done publishState publishRemaining
                  (publishedUnit, publishCache) ∈ support
                (LazyRevealProbe.runRaw _ _
                  (LazyRevealProbe.publishQuery coordinate >>= fun output =>
                    pure (output, _)))
                  at hpublish
              rw [LazyRevealProbe.publishQuery,
                LazyRevealProbe.runRaw_publish_query_bind] at hpublish
              simp [LazyRevealProbe.runRaw] at hpublish
              rcases hpublish with ⟨rfl, rfl, rfl, rfl⟩
              simp [StateT.run_modify, LazyRevealProbe.runRaw] at hfinish
              rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
              refine ⟨hfinalValid, ?_⟩
              exact ((hinvariant.2.updateHidden coordinate value).publish coordinate).updateOrdinary_of_decoded_secured
                candidate input value hdecode hsecured
      | none =>
          rw [hvalue, mem_support_bind_iff] at hreveal
          obtain ⟨sampled, _, hsampled⟩ := hreveal
          by_cases hhit : state.hitAt coordinate sampled
          · rw [if_pos hhit] at hsampled
            simp at hsampled
          · rw [if_neg hhit] at hsampled
            simp [LazyRevealProbe.runRaw] at hsampled
            rcases hsampled with ⟨rfl, rfl, rfl, rfl⟩
            simp only at hrest
            rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
            obtain ⟨publishRaw, hpublish, hfinish⟩ := hrest
            cases publishRaw with
            | stopped hit => simp at hfinish
            | done publishState publishRemaining publishResult =>
                rcases publishResult with ⟨publishedUnit, publishCache⟩
                change LazyRevealProbe.RawResult.done publishState publishRemaining
                    (publishedUnit, publishCache) ∈ support
                  (LazyRevealProbe.runRaw _ _
                    (LazyRevealProbe.publishQuery coordinate >>= fun output =>
                      pure (output, _)))
                    at hpublish
                rw [LazyRevealProbe.publishQuery,
                  LazyRevealProbe.runRaw_publish_query_bind] at hpublish
                simp [LazyRevealProbe.runRaw] at hpublish
                rcases hpublish with ⟨rfl, rfl, rfl, rfl⟩
                simp [StateT.run_modify, LazyRevealProbe.runRaw] at hfinish
                rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
                refine ⟨hfinalValid, ?_⟩
                have haccounted := (hinvariant.2.updateHidden coordinate value).materialize_publish
                  coordinate value hallowed
                have hsecuredFinal := secured_materialize_publish candidate coordinate
                  value hsourceChain hallowed hsecured
                exact haccounted.updateOrdinary_of_decoded_secured candidate input
                  value hdecode hsecuredFinal

theorem chainInvariant_revealPublishOrdinary_of_decode_none
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (coordinate : Coordinate) (input : HashInput)
    (hdecode : decodeProbe? parameter input = none)
    (hallowed : IsChainCoordinate coordinate → allowed coordinate)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat)
    (finalState : LazyRevealProbe.State Coordinate) (remaining : Nat)
    (value : HashOutput) (finalCache : SplitHashCache)
    (hinvariant : ChainInvariant parameter allowed state cache)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((do
        let output ← revealCoordinateOutput coordinate
        publishCoordinate coordinate
        modify fun workingCache : SplitHashCache =>
          Function.update workingCache (.ordinary input) (some output)
        pure output).run cache))) :
    ChainInvariant parameter allowed finalState finalCache := by
  have hfinalValid := preservesChainValid_revealPublishOrdinary allowed coordinate input hallowed
    state cache fuel finalState remaining value finalCache hinvariant.1 hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hreveal, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealedOutput, revealCache⟩
      rw [revealCoordinateOutput_run, LazyRevealProbe.revealQuery,
        LazyRevealProbe.runRaw_reveal_query_bind] at hreveal
      cases hvalue : state.values coordinate with
      | some existing =>
          rw [hvalue] at hreveal
          simp [LazyRevealProbe.runRaw] at hreveal
          rcases hreveal with ⟨rfl, rfl, rfl, rfl⟩
          simp only at hrest
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
          obtain ⟨publishRaw, hpublish, hfinish⟩ := hrest
          cases publishRaw with
          | stopped hit => simp at hfinish
          | done publishState publishRemaining publishResult =>
              rcases publishResult with ⟨publishedUnit, publishCache⟩
              change LazyRevealProbe.RawResult.done publishState publishRemaining
                  (publishedUnit, publishCache) ∈ support
                (LazyRevealProbe.runRaw _ _
                  (LazyRevealProbe.publishQuery coordinate >>= fun output =>
                    pure (output, _)))
                  at hpublish
              rw [LazyRevealProbe.publishQuery,
                LazyRevealProbe.runRaw_publish_query_bind] at hpublish
              simp [LazyRevealProbe.runRaw] at hpublish
              rcases hpublish with ⟨rfl, rfl, rfl, rfl⟩
              simp [StateT.run_modify, LazyRevealProbe.runRaw] at hfinish
              rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
              refine ⟨hfinalValid, ?_⟩
              exact ChainProbeAccounted.updateOrdinary_of_decode_none
                ((hinvariant.2.updateHidden coordinate value).publish coordinate)
                input value hdecode
      | none =>
          rw [hvalue, mem_support_bind_iff] at hreveal
          obtain ⟨sampled, _, hsampled⟩ := hreveal
          by_cases hhit : state.hitAt coordinate sampled
          · rw [if_pos hhit] at hsampled
            simp at hsampled
          · rw [if_neg hhit] at hsampled
            simp [LazyRevealProbe.runRaw] at hsampled
            rcases hsampled with ⟨rfl, rfl, rfl, rfl⟩
            simp only at hrest
            rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
            obtain ⟨publishRaw, hpublish, hfinish⟩ := hrest
            cases publishRaw with
            | stopped hit => simp at hfinish
            | done publishState publishRemaining publishResult =>
                rcases publishResult with ⟨publishedUnit, publishCache⟩
                change LazyRevealProbe.RawResult.done publishState publishRemaining
                    (publishedUnit, publishCache) ∈ support
                  (LazyRevealProbe.runRaw _ _
                    (LazyRevealProbe.publishQuery coordinate >>= fun output =>
                      pure (output, _)))
                    at hpublish
                rw [LazyRevealProbe.publishQuery,
                  LazyRevealProbe.runRaw_publish_query_bind] at hpublish
                simp [LazyRevealProbe.runRaw] at hpublish
                rcases hpublish with ⟨rfl, rfl, rfl, rfl⟩
                simp [StateT.run_modify, LazyRevealProbe.runRaw] at hfinish
                rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
                refine ⟨hfinalValid, ?_⟩
                exact ((hinvariant.2.updateHidden coordinate value).materialize_publish
                  coordinate value hallowed).updateOrdinary_of_decode_none input value hdecode

theorem chainInvariant_resolveKnownInput_of_decoded_secured
    (allowed : Coordinate → Prop) (hclosed : ChainForwardClosed allowed)
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput)
    (candidate : Probe) (hdecode : decodeProbe? parameter input = some candidate)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat)
    (finalState : LazyRevealProbe.State Coordinate) (remaining : Nat)
    (value : HashOutput) (finalCache : SplitHashCache)
    (hinvariant : ChainInvariant parameter allowed state cache)
    (hsecured : allowed candidate.coordinate ∨
      candidate.candidate ∈ state.pendingAt candidate.coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((resolveKnownInput parameter coordinate input).run cache))) :
    ChainInvariant parameter allowed finalState finalCache := by
  unfold resolveKnownInput at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hpeek, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done peekState peekRemaining peekResult =>
      rcases peekResult with ⟨known, peekCache⟩
      simp only at hrest
      have hpeekInvariant := preservesChainInvariant_peekTableInput parameter allowed coordinate
        state cache fuel peekState peekRemaining known peekCache hinvariant hpeek
      obtain ⟨hpeekState, hpeekRemaining, hpeekCache⟩ :=
        rawReadOnly_peekTableInput parameter coordinate state cache fuel peekState peekRemaining
          known peekCache hpeek
      have hsecuredPeek : allowed candidate.coordinate ∨
          candidate.candidate ∈ peekState.pendingAt candidate.coordinate := by
        simpa [hpeekState] using hsecured
      cases known with
      | none =>
          simp only at hrest
          exact chainInvariant_splitHashQuery_ordinary_of_decoded_secured parameter allowed
            candidate input hdecode peekState peekCache peekRemaining finalState remaining value
              finalCache hpeekInvariant hsecuredPeek hrest
      | some knownInput =>
          simp only at hrest
          by_cases heq : knownInput = input
          · rw [if_pos heq] at hrest
            have hallowed : IsChainCoordinate coordinate → allowed coordinate := by
              intro hchain
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  simp [peekTableInput, LazyRevealProbe.runRaw] at hpeek
              | position position =>
                  cases position with
                  | chain lay tree leafIdx chainIdx step =>
                      obtain ⟨source, houtput, hsourceChain, hsourceValue⟩ :=
                        mem_runRaw_peekTableInput_chain_some_imp_source parameter state peekState
                          cache peekCache fuel peekRemaining lay tree leafIdx chainIdx step
                            knownInput hpeek
                      have hsourceValid := hinvariant.1 source.coordinate hsourceChain
                      have hsourceAllowed := hsourceValid.2.2 (hsourceValid.1 hsourceValue)
                      exact houtput ▸ hclosed source hsourceAllowed (houtput.symm ▸ hchain)
                  | leaf => simp [IsChainCoordinate] at hchain
                  | node => simp [IsChainCoordinate] at hchain
                  | ftsLeaf => simp [IsChainCoordinate] at hchain
                  | ftsNode => simp [IsChainCoordinate] at hchain
                  | ftsRoots => simp [IsChainCoordinate] at hchain
            exact chainInvariant_revealPublishOrdinary_of_decoded_secured parameter allowed
              coordinate input candidate hdecode hallowed peekState peekCache peekRemaining
                finalState remaining value finalCache hpeekInvariant hsecuredPeek hrest
          · rw [if_neg heq] at hrest
            exact chainInvariant_splitHashQuery_ordinary_of_decoded_secured parameter allowed
              candidate input hdecode peekState peekCache peekRemaining finalState remaining value
                finalCache hpeekInvariant hsecuredPeek hrest

theorem preservesChainInvariant_resolveKnownInput_of_decode_none
    (allowed : Coordinate → Prop) (hclosed : ChainForwardClosed allowed)
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput)
    (hdecode : decodeProbe? parameter input = none) :
    PreservesChainInvariant parameter allowed
      (resolveKnownInput parameter coordinate input) := by
  intro state cache fuel finalState remaining value finalCache hinvariant hresult
  unfold resolveKnownInput at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hpeek, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done peekState peekRemaining peekResult =>
      rcases peekResult with ⟨known, peekCache⟩
      simp only at hrest
      have hpeekInvariant := preservesChainInvariant_peekTableInput parameter allowed coordinate
        state cache fuel peekState peekRemaining known peekCache hinvariant hpeek
      cases known with
      | none =>
          simp only at hrest
          exact preservesChainInvariant_splitHashQuery_ordinary_of_decode_none parameter allowed
            input hdecode peekState peekCache peekRemaining finalState remaining value finalCache
              hpeekInvariant hrest
      | some knownInput =>
          simp only at hrest
          by_cases heq : knownInput = input
          · rw [if_pos heq] at hrest
            have hallowed : IsChainCoordinate coordinate → allowed coordinate := by
              intro hchain
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  simp [peekTableInput, LazyRevealProbe.runRaw] at hpeek
              | position position =>
                  cases position with
                  | chain lay tree leafIdx chainIdx step =>
                      obtain ⟨source, houtput, hsourceChain, hsourceValue⟩ :=
                        mem_runRaw_peekTableInput_chain_some_imp_source parameter state peekState
                          cache peekCache fuel peekRemaining lay tree leafIdx chainIdx step
                            knownInput hpeek
                      have hsourceValid := hinvariant.1 source.coordinate hsourceChain
                      have hsourceAllowed := hsourceValid.2.2 (hsourceValid.1 hsourceValue)
                      exact houtput ▸ hclosed source hsourceAllowed (houtput.symm ▸ hchain)
                  | leaf => simp [IsChainCoordinate] at hchain
                  | node => simp [IsChainCoordinate] at hchain
                  | ftsLeaf => simp [IsChainCoordinate] at hchain
                  | ftsNode => simp [IsChainCoordinate] at hchain
                  | ftsRoots => simp [IsChainCoordinate] at hchain
            exact chainInvariant_revealPublishOrdinary_of_decode_none parameter allowed
              coordinate input hdecode hallowed peekState peekCache peekRemaining finalState
                remaining value finalCache hpeekInvariant hrest
          · rw [if_neg heq] at hrest
            exact preservesChainInvariant_splitHashQuery_ordinary_of_decode_none parameter allowed
              input hdecode peekState peekCache peekRemaining finalState remaining value finalCache
                hpeekInvariant hrest

theorem preservesChainInvariant_probe_resolveKnownInput
    (allowed : Coordinate → Prop) (hclosed : ChainForwardClosed allowed)
    (parameter : PublicParameter) (input : HashInput) (candidate : Probe)
    (hdecode : decodeProbe? parameter input = some candidate) :
    PreservesChainInvariant parameter allowed (do
      probe candidate
      resolveKnownInput parameter candidate.outputCoordinate input) := by
  intro state cache fuel finalState remaining value finalCache hinvariant hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel
      ((probe candidate).run cache >>= fun probeResult =>
        (resolveKnownInput parameter candidate.outputCoordinate input).run probeResult.2))
    at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hprobe, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done probeState probeRemaining probeResult =>
      rcases probeResult with ⟨probedUnit, probeCache⟩
      cases probedUnit
      have hprobeInvariant := preservesChainInvariant_probe parameter allowed candidate state cache
        fuel probeState probeRemaining () probeCache hinvariant hprobe
      have hmatches := (decodeProbe?_eq_some_iff parameter input candidate).1 hdecode
      have hchain := candidate.isChainCoordinate_of_matchesInput hmatches
      have hsecured : allowed candidate.coordinate ∨
          candidate.candidate ∈ probeState.pendingAt candidate.coordinate := by
        have hprobe' := hprobe
        change LazyRevealProbe.RawResult.done probeState probeRemaining ((), probeCache) ∈
          support (LazyRevealProbe.runRaw state fuel
            (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate >>= fun output =>
              pure (output, cache))) at hprobe'
        rw [LazyRevealProbe.probeQuery, LazyRevealProbe.runRaw_probe_query_bind] at hprobe'
        cases fuel with
        | zero => simp at hprobe'
        | succ remainingFuel =>
            simp only at hprobe'
            by_cases hrevealed : candidate.coordinate ∈ state.revealed
            · rw [if_pos hrevealed] at hprobe'
              simp [LazyRevealProbe.runRaw] at hprobe'
              rcases hprobe' with ⟨rfl, rfl, rfl⟩
              exact Or.inl ((hinvariant.1 candidate.coordinate hchain).2.2 hrevealed)
            · rw [if_neg hrevealed] at hprobe'
              simp [LazyRevealProbe.runRaw] at hprobe'
              rcases hprobe' with ⟨rfl, rfl, rfl⟩
              exact Or.inr (LazyRevealProbe.State.pendingAt_addPending_self state
                candidate.coordinate candidate.candidate)
      exact chainInvariant_resolveKnownInput_of_decoded_secured allowed hclosed parameter
        candidate.outputCoordinate input candidate hdecode probeState probeCache probeRemaining
          finalState remaining value finalCache hprobeInvariant hsecured hrest

theorem preservesChainInvariant_probingHashQuery
    (allowed : Coordinate → Prop) (hclosed : ChainForwardClosed allowed)
    (parameter : PublicParameter) (input : HashInput) :
    PreservesChainInvariant parameter allowed (probingHashQuery parameter input) := by
  unfold probingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      exact preservesChainInvariant_probe_resolveKnownInput allowed hclosed parameter input
        candidate hprobe
  | none =>
      cases hposition : decodePosition? parameter input with
      | none =>
          exact preservesChainInvariant_splitHashQuery_ordinary_of_decode_none parameter allowed
            input hprobe
      | some position =>
          cases position with
          | chain lay tree leafIdx chainIdx step =>
              exact preservesChainInvariant_resolveKnownInput_of_decode_none allowed hclosed
                parameter (.position (.chain lay tree leafIdx chainIdx step)) input hprobe
          | leaf lay tree leafIdx =>
              exact preservesChainInvariant_resolveKnownInput_of_decode_none allowed hclosed
                parameter (.position (.leaf lay tree leafIdx)) input hprobe
          | node lay tree level nodeIdx =>
              exact preservesChainInvariant_resolveKnownInput_of_decode_none allowed hclosed
                parameter (.position (.node lay tree level nodeIdx)) input hprobe
          | ftsLeaf | ftsNode | ftsRoots =>
              exact preservesChainInvariant_splitHashQuery_ordinary_of_decode_none parameter
                allowed input hprobe

theorem preservesChainInvariant_splitUniformImpl
    (parameter : PublicParameter) (allowed : Coordinate → Prop) (n : Nat) :
    PreservesChainInvariant parameter allowed (splitUniformImpl n) := by
  intro state cache fuel finalState remaining value finalCache hinvariant hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.uniformQuery n >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.uniformQuery, LazyRevealProbe.runRaw_uniform_query_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨output, _, hdone⟩ := hresult
  simp [LazyRevealProbe.runRaw] at hdone
  rcases hdone with ⟨rfl, rfl, rfl, rfl⟩
  exact hinvariant

def PreservesChainInvariantImpl {spec : OracleSpec ι} (parameter : PublicParameter)
    (allowed : Coordinate → Prop)
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))) : Prop :=
  ∀ query, PreservesChainInvariant parameter allowed (impl query)

theorem PreservesChainInvariantImpl.simulateQ {spec : OracleSpec ι}
    {parameter : PublicParameter} {allowed : Coordinate → Prop}
    {impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))}
    (himpl : PreservesChainInvariantImpl parameter allowed impl)
    (computation : OracleComp spec alpha) :
    PreservesChainInvariant parameter allowed (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact preservesChainInvariant_pure parameter allowed value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (himpl query).bind ih

theorem preservesChainInvariantImpl_ordinaryHashImpl
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (hdecode : ∀ input, decodeProbe? parameter input = none) :
    PreservesChainInvariantImpl parameter allowed ordinaryHashImpl := by
  intro input
  exact preservesChainInvariant_splitHashQuery_ordinary_of_decode_none parameter allowed input
    (hdecode input)

theorem preservesChainInvariant_ordinaryTweakableHash_of_decode_none
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (domain : HashDomain) (payload : HashInput)
    (hdecode : decodeProbe? parameter (tweakableHashInput parameter domain payload) = none) :
    PreservesChainInvariant parameter allowed
      (simulateQ ordinaryHashImpl (tweakableHash parameter domain payload)) := by
  change PreservesChainInvariant parameter allowed (do
    let output ← splitHashQuery
      (.ordinary (tweakableHashInput parameter domain payload))
    pure (truncateHash output))
  exact (preservesChainInvariant_splitHashQuery_ordinary_of_decode_none parameter allowed _
    hdecode).bind fun _ => preservesChainInvariant_pure parameter allowed _

theorem preservesChainInvariant_ordinaryTweakableHash
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (domain : HashDomain) (payload : HashInput) (hinRange : domain.InRange)
    (hchain : ∀ lay tree leafIdx chainIdx step,
      domain ≠ .chain lay tree leafIdx chainIdx step)
    (hleaf : ∀ lay tree leafIdx, domain ≠ .leaf lay tree leafIdx) :
    PreservesChainInvariant parameter allowed
      (simulateQ ordinaryHashImpl (tweakableHash parameter domain payload)) := by
  exact preservesChainInvariant_ordinaryTweakableHash_of_decode_none parameter allowed domain
    payload (decodeProbe?_tweakableHashInput_of_not_chain_leaf parameter domain payload hinRange
      hchain hleaf)

theorem preservesChainInvariantImpl_splitUniformImpl
    (parameter : PublicParameter) (allowed : Coordinate → Prop) :
    PreservesChainInvariantImpl parameter allowed splitUniformImpl :=
  preservesChainInvariant_splitUniformImpl parameter allowed

theorem preservesChainInvariantImpl_probingHashImpl
    (allowed : Coordinate → Prop) (hclosed : ChainForwardClosed allowed)
    (parameter : PublicParameter) :
    PreservesChainInvariantImpl parameter allowed (probingHashImpl parameter) :=
  preservesChainInvariant_probingHashQuery allowed hclosed parameter

theorem preservesChainInvariantImpl_probingRomImpl
    (allowed : Coordinate → Prop) (hclosed : ChainForwardClosed allowed)
    (parameter : PublicParameter) :
    PreservesChainInvariantImpl parameter allowed (probingRomImpl parameter) := by
  intro query
  cases query with
  | inl query => exact preservesChainInvariantImpl_splitUniformImpl parameter allowed query
  | inr query => exact preservesChainInvariantImpl_probingHashImpl allowed hclosed parameter query

theorem preservesChainInvariant_sequenceFin
    (parameter : PublicParameter) (allowed : Coordinate → Prop) {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomputation : ∀ index, PreservesChainInvariant parameter allowed (computation index)) :
    PreservesChainInvariant parameter allowed (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact preservesChainInvariant_pure parameter allowed Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomputation 0).bind fun head =>
        (ih (fun index => computation index.succ)
          (fun index => hcomputation index.succ)).bind fun tail =>
            preservesChainInvariant_pure parameter allowed
              (Fin.cases head tail : Fin (n + 1) → alpha)

theorem chainInvariant_sequenceFin_of_done
    (parameter : PublicParameter) (allowed : Coordinate → Prop) {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomputation : ∀ index state cache fuel finalState remaining value finalCache,
      ChainInvariant parameter allowed state cache →
      LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
        support (LazyRevealProbe.runRaw state fuel ((computation index).run cache)) →
      ChainInvariant parameter allowed finalState finalCache)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (values : Fin n → alpha)
    (hinvariant : ChainInvariant parameter allowed state cache)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (values, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((sequenceFin computation).run cache))) :
    ChainInvariant parameter allowed finalState finalCache := by
  induction n generalizing state finalState cache finalCache fuel remaining with
  | zero =>
      simp [sequenceFin, LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact hinvariant
  | succ n ih =>
      rw [sequenceFin, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨headRaw, hhead, hafterHead⟩ := hresult
      cases headRaw with
      | stopped stoppedHit => simp at hafterHead
      | done headState headRemaining headResult =>
          rcases headResult with ⟨head, headCache⟩
          simp only at hafterHead
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hafterHead
          obtain ⟨tailRaw, htail, hfinish⟩ := hafterHead
          cases tailRaw with
          | stopped stoppedHit => simp at hfinish
          | done tailState tailRemaining tailResult =>
              rcases tailResult with ⟨tail, tailCache⟩
              have hheadInvariant := hcomputation 0 state cache fuel headState headRemaining
                head headCache hinvariant hhead
              have htailInvariant := ih
                (computation := fun index => computation index.succ)
                (hcomputation := fun index => hcomputation index.succ)
                (values := tail) (state := headState) (finalState := tailState)
                (cache := headCache) (finalCache := tailCache) (fuel := headRemaining)
                (remaining := tailRemaining) hheadInvariant htail
              simp [LazyRevealProbe.runRaw] at hfinish
              rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
              exact htailInvariant

theorem chainInvariant_layerSequence_of_done
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (computation : Layer → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomputation : ∀ index state cache fuel finalState remaining value finalCache,
      ChainInvariant parameter allowed state cache →
      LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
        support (LazyRevealProbe.runRaw state fuel ((computation index).run cache)) →
      ChainInvariant parameter allowed finalState finalCache)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (values : Layer → alpha)
    (hinvariant : ChainInvariant parameter allowed state cache)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (values, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((sequenceFin computation).run cache))) :
    ChainInvariant parameter allowed finalState finalCache :=
  chainInvariant_sequenceFin_of_done (n := numLayers) parameter allowed computation hcomputation
    state finalState cache finalCache fuel remaining values hinvariant hresult

theorem sequenceFin_component_run_of_done {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hincreasing : ∀ index, OrdinaryCacheIncreasing (computation index))
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (values : Fin n → alpha)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (values, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((sequenceFin computation).run cache)))
    (position : Fin n) :
    ∃ (componentState componentFinalState : LazyRevealProbe.State Coordinate)
        (componentCache componentFinalCache : SplitHashCache)
        (componentFuel componentRemaining : Nat) (componentValue : alpha),
      LazyRevealProbe.RawResult.done componentFinalState componentRemaining
          (componentValue, componentFinalCache) ∈ support
        (LazyRevealProbe.runRaw componentState componentFuel
          ((computation position).run componentCache))
        ∧ values position = componentValue
        ∧ LazyRevealProbe.ValuesLE componentFinalState finalState
        ∧ ordinaryQueryCache componentFinalCache ≤ ordinaryQueryCache finalCache := by
  induction n generalizing state finalState cache finalCache fuel remaining with
  | zero => exact position.elim0
  | succ n ih =>
      rw [sequenceFin, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨headRaw, hhead, hafterHead⟩ := hresult
      cases headRaw with
      | stopped stoppedHit => simp at hafterHead
      | done headState headRemaining headResult =>
          rcases headResult with ⟨head, headCache⟩
          simp only at hafterHead
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hafterHead
          obtain ⟨tailRaw, htail, hfinish⟩ := hafterHead
          cases tailRaw with
          | stopped stoppedHit => simp at hfinish
          | done tailState tailRemaining tailResult =>
              rcases tailResult with ⟨tail, tailCache⟩
              have htailValues := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                ((sequenceFin fun tailPosition => computation tailPosition.succ).run headCache)
                headState tailState headRemaining tailRemaining (tail, tailCache) htail
              have htailCache := ordinaryCacheIncreasing_sequenceFin
                (fun tailPosition => computation tailPosition.succ)
                (fun tailPosition => hincreasing tailPosition.succ)
                headState headCache headRemaining tailState tailRemaining tail tailCache htail
              simp [LazyRevealProbe.runRaw] at hfinish
              rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
              cases position using Fin.cases with
              | zero =>
                  exact ⟨state, headState, cache, headCache, fuel, headRemaining, head,
                    hhead, rfl, htailValues, htailCache⟩
              | succ tailPosition =>
                  exact ih
                    (computation := fun position => computation position.succ)
                    (hincreasing := fun position => hincreasing position.succ)
                    (values := tail) (state := headState) (finalState := finalState)
                    (cache := headCache) (finalCache := finalCache) (fuel := headRemaining)
                    (remaining := remaining) htail tailPosition

theorem preservesChainInvariant_ordinaryEncode
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) :
    PreservesChainInvariant parameter allowed
      (simulateQ ordinaryHashImpl (encode parameter lay tree leafIdx message counter)) := by
  rw [encode, simulateQ_bind]
  exact (preservesChainInvariant_ordinaryTweakableHash parameter allowed
    (.encoding lay tree leafIdx) _ (by trivial) (by simp) (by simp)).bind fun _ =>
      preservesChainInvariant_pure parameter allowed _

theorem preservesChainInvariant_ordinaryMessageDigest
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (root : Digest) (message : Message) (randomness : Randomness) :
    PreservesChainInvariant parameter allowed
      (simulateQ ordinaryHashImpl (messageDigest parameter root message randomness)) := by
  rw [messageDigest, simulateQ_bind]
  have hquery : simulateQ ordinaryHashImpl
      (oracleHash (tweakableHashInput parameter .message
        (messageDigestPayload root message randomness))) =
      splitHashQuery (.ordinary (tweakableHashInput parameter .message
        (messageDigestPayload root message randomness))) := by
    simp [oracleHash, ordinaryHashImpl]
  rw [hquery]
  change PreservesChainInvariant parameter allowed
    (splitHashQuery (.ordinary (tweakableHashInput parameter .message
      (messageDigestPayload root message randomness))) >>= fun output => pure _)
  exact (preservesChainInvariant_splitHashQuery_ordinary_of_decode_none parameter allowed _
    (decodeProbe?_tweakableHashInput_of_not_chain_leaf parameter .message _ (by trivial)
      (by simp) (by simp))).bind fun _ => preservesChainInvariant_pure parameter allowed _

theorem preservesChainInvariant_ordinarySignAttempt
    (allowed : Coordinate → Prop) (secretKey : SecretKey)
    (message : Message) (randomness : Randomness) :
    PreservesChainInvariant secretKey.parameter allowed
      (simulateQ ordinaryHashImpl (signAttempt secretKey message randomness)) := by
  rw [signAttempt, simulateQ_bind]
  exact (preservesChainInvariant_ordinaryMessageDigest secretKey.parameter allowed secretKey.root message
    randomness).bind fun digest => by
      split <;> simpa only [simulateQ_pure] using
        (preservesChainInvariant_pure secretKey.parameter allowed _)

theorem preservesChainInvariant_ordinarySignDigestLoop
    (allowed : Coordinate → Prop) (attempts : Nat)
    (secretKey : SecretKey) (message : Message) :
    PreservesChainInvariant secretKey.parameter allowed
      (simulateQ ordinaryRomImpl (signDigestLoop attempts secretKey message)) := by
  induction attempts with
  | zero =>
      rw [signDigestLoop, simulateQ_pure]
      exact preservesChainInvariant_pure secretKey.parameter allowed none
  | succ attempts ih =>
      rw [signDigestLoop, simulateQ_bind]
      have hrandomness : PreservesChainInvariant secretKey.parameter allowed
          (simulateQ ordinaryRomImpl (liftM sampleRandomness)) := by
        rw [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_left]
        exact (preservesChainInvariantImpl_splitUniformImpl secretKey.parameter allowed).simulateQ
          sampleRandomness
      exact hrandomness.bind fun randomness => by
        rw [simulateQ_bind]
        have hattempt : PreservesChainInvariant secretKey.parameter allowed
            (simulateQ ordinaryRomImpl
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))))) := by
          rw [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_right]
          exact preservesChainInvariant_ordinarySignAttempt allowed secretKey message randomness
        exact hattempt.bind fun attempt => by
          cases attempt with
          | none => exact ih
          | some selected => exact preservesChainInvariant_pure secretKey.parameter allowed _

theorem ordinaryCacheIncreasing_ordinarySignDigestLoop
    (attempts : Nat) (secretKey : SecretKey) (message : Message) :
    OrdinaryCacheIncreasing
      (simulateQ ordinaryRomImpl (signDigestLoop attempts secretKey message)) := by
  induction attempts with
  | zero =>
      rw [signDigestLoop, simulateQ_pure]
      exact OrdinaryCacheIncreasing.pure none
  | succ attempts ih =>
      rw [signDigestLoop, simulateQ_bind]
      have hrandomness : OrdinaryCacheIncreasing
          (simulateQ ordinaryRomImpl (liftM sampleRandomness)) := by
        rw [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_left]
        exact ordinaryCacheIncreasing_simulateQ_splitUniformImpl sampleRandomness
      exact hrandomness.bind fun randomness => by
        rw [simulateQ_bind]
        have hattempt : OrdinaryCacheIncreasing
            (simulateQ ordinaryRomImpl
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))))) := by
          rw [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_right]
          exact ordinaryCacheIncreasing_simulateQ_ordinaryHashImpl
            (signAttempt secretKey message randomness)
        exact hattempt.bind fun attempt => by
          cases attempt with
          | none => exact ih
          | some selected => exact OrdinaryCacheIncreasing.pure _

theorem successfulDigestLoop_of_mem_runRaw_ordinaryRomImpl
    (f : QueryImpl HashSpec Id) (secretKey : SecretKey) (message : Message)
    (attempts : Nat) (randomness : Randomness) (index : Index)
    (leaves : DigestTree → FtsLeaf)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (targetCache : SplitHashCache)
    (hleFinal : ordinaryQueryCache finalCache ≤ ordinaryQueryCache targetCache)
    (hf : StableCacheAgreesWithFn secretKey.parameter targetCache f)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some (randomness, index, leaves), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryRomImpl
          (signDigestLoop attempts secretKey message)).run cache))) :
    SuccessfulDigestRun f (ordinaryQueryCache targetCache) secretKey message randomness index
      leaves := by
  induction attempts generalizing state cache finalState finalCache fuel remaining randomness
      index leaves with
  | zero =>
      simp [signDigestLoop, LazyRevealProbe.runRaw] at hresult
  | succ attempts ih =>
      rw [signDigestLoop, simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨randomnessRaw, hsample, hrest⟩ := hresult
      cases randomnessRaw with
      | stopped hit => simp at hrest
      | done randomnessState randomnessRemaining randomnessResult =>
          rcases randomnessResult with ⟨sampledRandomness, randomnessCache⟩
          have hsample' : LazyRevealProbe.RawResult.done randomnessState randomnessRemaining
              (sampledRandomness, randomnessCache) ∈ support
            (LazyRevealProbe.runRaw state fuel
              ((simulateQ splitUniformImpl sampleRandomness).run cache)) := by
            simpa only [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_left] using hsample
          obtain ⟨_, _, _, hsampled⟩ :=
            mem_runRaw_simulateQ_splitUniformImpl_projects sampleRandomness state
              randomnessState cache randomnessCache fuel randomnessRemaining sampledRandomness
                hsample'
          simp only at hrest
          rw [simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hrest
          obtain ⟨attemptRaw, hattempt, hfinish⟩ := hrest
          cases attemptRaw with
          | stopped hit => simp at hfinish
          | done attemptState attemptRemaining attemptResult =>
              rcases attemptResult with ⟨attempt, attemptCache⟩
              have hattempt' : LazyRevealProbe.RawResult.done attemptState attemptRemaining
                    (attempt, attemptCache) ∈ support
                  (LazyRevealProbe.runRaw randomnessState randomnessRemaining
                    ((simulateQ ordinaryHashImpl
                      (signAttempt secretKey message sampledRandomness)).run randomnessCache)) := by
                simpa only [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_right] using hattempt
              have hattemptProjection := mem_runRaw_simulateQ_ordinaryHashImpl_projects
                (signAttempt secretKey message sampledRandomness) randomnessState attemptState
                  randomnessCache attemptCache randomnessRemaining attemptRemaining attempt
                    hattempt'
              obtain ⟨_, _, hattemptSupport⟩ := hattemptProjection
              cases attempt with
              | none =>
                  exact ih randomness index leaves attemptState finalState attemptCache finalCache
                    attemptRemaining remaining hleFinal hfinish
              | some selected =>
                  obtain ⟨selectedIndex, selectedLeaves⟩ := selected
                  simp [LazyRevealProbe.runRaw] at hfinish
                  rcases hfinish with ⟨hfinalState, hfinalRemaining, hselected, hfinalCache⟩
                  subst finalState
                  subst remaining
                  subst finalCache
                  obtain ⟨hrandomness, hindex, hleaves⟩ := hselected
                  subst randomness
                  subst index
                  subst leaves
                  have hfAttempt : StableCacheAgreesWithFn secretKey.parameter attemptCache f :=
                    fun input output hstable hcached =>
                      hf input output hstable (hleFinal hcached)
                  have hreplay := replay_of_mem_runRaw_ordinaryHashImpl_of_stable f
                    secretKey.parameter (signAttempt secretKey message sampledRandomness)
                      randomnessState attemptState randomnessCache attemptCache randomnessRemaining
                        attemptRemaining (some (selectedIndex, selectedLeaves)) hfAttempt
                          (queriesStable_signAttempt f secretKey message sampledRandomness) hattempt'
                  exact ⟨hsampled, hreplay.1, CachedRun.mono hleFinal hreplay.2⟩

theorem preservesChainInvariant_simulateQ_sequenceFin {spec : OracleSpec ι}
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    {n : Nat} (computation : Fin n → OracleComp spec alpha)
    (hcomputation : ∀ index,
      PreservesChainInvariant parameter allowed (simulateQ impl (computation index))) :
    PreservesChainInvariant parameter allowed (simulateQ impl (sequenceFin computation)) := by
  induction n with
  | zero =>
      simp only [sequenceFin, simulateQ_pure]
      exact preservesChainInvariant_pure parameter allowed Fin.elim0
  | succ n ih =>
      rw [sequenceFin, simulateQ_bind]
      exact (hcomputation 0).bind fun head => by
        rw [simulateQ_bind]
        exact (ih (fun index => computation index.succ)
          (fun index => hcomputation index.succ)).bind fun tail => by
            simp only [simulateQ_pure]
            exact preservesChainInvariant_pure parameter allowed
              (Fin.cases head tail : Fin (n + 1) → alpha)

theorem preservesChainInvariant_ordinaryFtsLeafHash
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf) (secret : Digest) :
    PreservesChainInvariant parameter allowed
      (simulateQ ordinaryHashImpl (ftsLeafHash parameter index tree leafIdx secret)) := by
  unfold ftsLeafHash
  exact preservesChainInvariant_ordinaryTweakableHash parameter allowed
    (.ftsLeaf index tree leafIdx) _ (by trivial) (by simp) (by simp)

theorem preservesChainInvariant_ordinaryFtsNode
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (index : Index) (tree : FtsTree) (secret : FtsLeaf → Digest) :
    ∀ level nodeIdx, PreservesChainInvariant parameter allowed
      (simulateQ ordinaryHashImpl (ftsNode parameter index tree secret level nodeIdx))
  | 0, nodeIdx => by
      rw [ftsNode_zero_eq]
      exact preservesChainInvariant_ordinaryFtsLeafHash parameter allowed index tree
        (ftsLeafOfNat nodeIdx) (secret (ftsLeafOfNat nodeIdx))
  | level + 1, nodeIdx => by
      rw [ftsNode_succ_eq, simulateQ_bind]
      exact (preservesChainInvariant_ordinaryFtsNode parameter allowed index tree secret level
        (2 * nodeIdx)).bind fun left => by
          rw [simulateQ_bind]
          exact (preservesChainInvariant_ordinaryFtsNode parameter allowed index tree secret level
            (2 * nodeIdx + 1)).bind fun right =>
              preservesChainInvariant_ordinaryTweakableHash_of_decode_none parameter allowed
                (.ftsNode index tree (level + 1) nodeIdx) (nodePayload left right)
                  (decodeProbe?_tweakableHashInput_ftsNode parameter index tree (level + 1)
                    nodeIdx (nodePayload left right))

theorem preservesChainInvariant_ordinaryFtsKey
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    PreservesChainInvariant parameter allowed
      (simulateQ ordinaryHashImpl (ftsKey parameter index secret)) := by
  rw [ftsKey, simulateQ_bind]
  exact (preservesChainInvariant_simulateQ_sequenceFin parameter allowed ordinaryHashImpl
    (fun tree => ftsNode parameter index tree (secret tree) ftsTreeHeight 0)
    (fun tree => preservesChainInvariant_ordinaryFtsNode parameter allowed index tree
      (secret tree) ftsTreeHeight 0)).bind fun roots =>
        preservesChainInvariant_ordinaryTweakableHash parameter allowed (.ftsRoots index)
          (ftsRootsPayload roots) (by trivial) (by simp) (by simp)

theorem preservesChainInvariant_ordinaryFtsOpen
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (index : Index) (leaves : DigestTree → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) :
    PreservesChainInvariant parameter allowed
      (simulateQ ordinaryHashImpl (ftsOpen parameter index leaves secret)) := by
  unfold ftsOpen
  exact preservesChainInvariant_simulateQ_sequenceFin parameter allowed ordinaryHashImpl _
    fun tree => preservesChainInvariant_simulateQ_sequenceFin parameter allowed ordinaryHashImpl _
      fun level => preservesChainInvariant_ordinaryFtsNode parameter allowed index tree
        (secret tree) level.val
          (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)

theorem preservesChainValid_resolveKnownInput
    (allowed : Coordinate → Prop) (hclosed : ChainForwardClosed allowed)
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput) :
    PreservesChainValid allowed (resolveKnownInput parameter coordinate input) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  unfold resolveKnownInput at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hpeek, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done peekState peekRemaining peekResult =>
      rcases peekResult with ⟨known, peekCache⟩
      simp only at hrest
      have hpeekValid := preservesChainValid_peekTableInput allowed parameter coordinate state cache
        fuel peekState peekRemaining known peekCache hvalid hpeek
      cases known with
      | none =>
          simp only at hrest
          exact preservesChainValid_splitHashQuery_ordinary allowed input peekState peekCache
            peekRemaining finalState remaining value finalCache hpeekValid hrest
      | some knownInput =>
          simp only at hrest
          by_cases heq : knownInput = input
          · rw [if_pos heq] at hrest
            have hallowed : IsChainCoordinate coordinate → allowed coordinate := by
              intro hchain
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  simp [peekTableInput, LazyRevealProbe.runRaw] at hpeek
              | position position =>
                  cases position with
                  | chain lay tree leafIdx chainIdx step =>
                      obtain ⟨candidate, houtput, hsourceChain, hsourceValue⟩ :=
                        mem_runRaw_peekTableInput_chain_some_imp_source parameter state peekState
                          cache peekCache fuel peekRemaining lay tree leafIdx chainIdx step
                            knownInput hpeek
                      have hsourceValid := hvalid candidate.coordinate hsourceChain
                      have hsourceAllowed := hsourceValid.2.2 (hsourceValid.1 hsourceValue)
                      exact houtput ▸ hclosed candidate hsourceAllowed (houtput.symm ▸ hchain)
                  | leaf => simp [IsChainCoordinate] at hchain
                  | node => simp [IsChainCoordinate] at hchain
                  | ftsLeaf => simp [IsChainCoordinate] at hchain
                  | ftsNode => simp [IsChainCoordinate] at hchain
                  | ftsRoots => simp [IsChainCoordinate] at hchain
            exact preservesChainValid_revealPublishOrdinary allowed coordinate input hallowed
              peekState peekCache peekRemaining finalState remaining value finalCache hpeekValid hrest
          · rw [if_neg heq] at hrest
            exact preservesChainValid_splitHashQuery_ordinary allowed input peekState peekCache
              peekRemaining finalState remaining value finalCache hpeekValid hrest

theorem preservesChainValid_probingHashQuery
    (allowed : Coordinate → Prop) (hclosed : ChainForwardClosed allowed)
    (parameter : PublicParameter) (input : HashInput) :
    PreservesChainValid allowed (probingHashQuery parameter input) := by
  unfold probingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      exact (preservesChainValid_probe allowed candidate).bind fun _ =>
        preservesChainValid_resolveKnownInput allowed hclosed parameter
          candidate.outputCoordinate input
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => exact preservesChainValid_splitHashQuery_ordinary allowed input
      | some position =>
          cases position with
          | chain lay tree leafIdx chainIdx step =>
              exact preservesChainValid_resolveKnownInput allowed hclosed parameter
                (.position (.chain lay tree leafIdx chainIdx step)) input
          | leaf lay tree leafIdx =>
              exact preservesChainValid_resolveKnownInput allowed hclosed parameter
                (.position (.leaf lay tree leafIdx)) input
          | node lay tree level nodeIdx =>
              exact preservesChainValid_resolveKnownInput allowed hclosed parameter
                (.position (.node lay tree level nodeIdx)) input
          | ftsLeaf | ftsNode | ftsRoots =>
              exact preservesChainValid_splitHashQuery_ordinary allowed input

theorem preservesChainValid_splitUniformImpl (allowed : Coordinate → Prop) (n : Nat) :
    PreservesChainValid allowed (splitUniformImpl n) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.uniformQuery n >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.uniformQuery, LazyRevealProbe.runRaw_uniform_query_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨output, _, hdone⟩ := hresult
  simp [LazyRevealProbe.runRaw] at hdone
  rcases hdone with ⟨rfl, rfl, rfl, rfl⟩
  exact hvalid

def PreservesChainValidImpl {spec : OracleSpec ι} (allowed : Coordinate → Prop)
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))) : Prop :=
  ∀ query, PreservesChainValid allowed (impl query)

theorem PreservesChainValidImpl.simulateQ {spec : OracleSpec ι}
    {allowed : Coordinate → Prop}
    {impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))}
    (himpl : PreservesChainValidImpl allowed impl) (computation : OracleComp spec alpha) :
    PreservesChainValid allowed (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact preservesChainValid_pure allowed value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (himpl query).bind ih

theorem preservesChainValidImpl_ordinaryHashImpl (allowed : Coordinate → Prop) :
    PreservesChainValidImpl allowed ordinaryHashImpl := by
  intro input
  exact preservesChainValid_splitHashQuery_ordinary allowed input

theorem preservesChainValidImpl_splitUniformImpl (allowed : Coordinate → Prop) :
    PreservesChainValidImpl allowed splitUniformImpl :=
  preservesChainValid_splitUniformImpl allowed

theorem preservesChainValidImpl_ordinaryRomImpl (allowed : Coordinate → Prop) :
    PreservesChainValidImpl allowed ordinaryRomImpl := by
  intro query
  cases query with
  | inl query => exact preservesChainValidImpl_splitUniformImpl allowed query
  | inr query => exact preservesChainValidImpl_ordinaryHashImpl allowed query

theorem preservesChainValidImpl_probingHashImpl
    (allowed : Coordinate → Prop) (hclosed : ChainForwardClosed allowed)
    (parameter : PublicParameter) :
    PreservesChainValidImpl allowed (probingHashImpl parameter) :=
  preservesChainValid_probingHashQuery allowed hclosed parameter

theorem preservesChainValidImpl_probingRomImpl
    (allowed : Coordinate → Prop) (hclosed : ChainForwardClosed allowed)
    (parameter : PublicParameter) :
    PreservesChainValidImpl allowed (probingRomImpl parameter) := by
  intro query
  cases query with
  | inl query => exact preservesChainValidImpl_splitUniformImpl allowed query
  | inr query => exact preservesChainValidImpl_probingHashImpl allowed hclosed parameter query

theorem preservesChainValid_sequenceFin (allowed : Coordinate → Prop) {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomputation : ∀ index, PreservesChainValid allowed (computation index)) :
    PreservesChainValid allowed (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact preservesChainValid_pure allowed Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomputation 0).bind fun head =>
        (ih (fun index => computation index.succ)
          (fun index => hcomputation index.succ)).bind fun tail =>
            preservesChainValid_pure allowed (Fin.cases head tail : Fin (n + 1) → alpha)

theorem mem_runRaw_revealCoordinate_state
    (coordinate : Coordinate) (state finalState : LazyRevealProbe.State Coordinate)
    (fuel remaining : Nat) (cache finalCache : SplitHashCache) (value : Digest)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((revealCoordinate coordinate).run cache))) :
    (state.values coordinate ≠ none ∧ finalState = state) ∨
      ∃ output, finalState = state.materialize coordinate output := by
  rw [revealCoordinate_run, LazyRevealProbe.revealQuery,
    LazyRevealProbe.runRaw_reveal_query_bind] at hresult
  cases hvalue : state.values coordinate with
  | some existing =>
      rw [hvalue] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact Or.inl ⟨by simp, rfl⟩
  | none =>
      rw [hvalue, mem_support_bind_iff] at hresult
      obtain ⟨sampled, _, hsampled⟩ := hresult
      by_cases hhit : state.hitAt coordinate sampled
      · rw [if_pos hhit] at hsampled
        simp at hsampled
      · rw [if_neg hhit] at hsampled
        simp [LazyRevealProbe.runRaw] at hsampled
        rcases hsampled with ⟨rfl, rfl, rfl, rfl⟩
        exact Or.inr ⟨sampled, rfl⟩

theorem ordinaryCacheIncreasing_revealCoordinate (coordinate : Coordinate) :
    OrdinaryCacheIncreasing (revealCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hresult
  rw [revealCoordinate_run, LazyRevealProbe.revealQuery,
    LazyRevealProbe.runRaw_reveal_query_bind] at hresult
  cases hvalue : state.values coordinate with
  | some existing =>
      rw [hvalue] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      rw [ordinaryQueryCache_update_hidden]
  | none =>
      rw [hvalue, mem_support_bind_iff] at hresult
      obtain ⟨output, _, hsampled⟩ := hresult
      by_cases hhit : state.hitAt coordinate output
      · rw [if_pos hhit] at hsampled
        simp at hsampled
      · rw [if_neg hhit] at hsampled
        simp [LazyRevealProbe.runRaw] at hsampled
        rcases hsampled with ⟨rfl, rfl, rfl, rfl⟩
        rw [ordinaryQueryCache_update_hidden]

theorem splitCachePreserving_publishCoordinate (coordinate : Coordinate) :
    SplitCachePreserving (publishCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.publishQuery coordinate >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.publishQuery, LazyRevealProbe.runRaw_publish_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  exact hresult.2.2

theorem ordinaryCacheIncreasing_revealPublishedCoordinate (coordinate : Coordinate) :
    OrdinaryCacheIncreasing (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (ordinaryCacheIncreasing_revealCoordinate coordinate).bind fun _ =>
    (splitCachePreserving_publishCoordinate coordinate).ordinaryCacheIncreasing.bind fun _ =>
      OrdinaryCacheIncreasing.pure _

theorem preservesChainValid_revealCoordinate_of_not_chain
    (allowed : Coordinate → Prop) (coordinate : Coordinate)
    (hnotChain : ¬IsChainCoordinate coordinate) :
    PreservesChainValid allowed (revealCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  rcases mem_runRaw_revealCoordinate_state coordinate state finalState fuel remaining cache
    finalCache value hresult with ⟨hvalue, rfl⟩ | ⟨output, rfl⟩
  · exact hvalid
  · exact hvalid.materialize_of_not_chain coordinate output hnotChain

theorem preservesChainInvariant_revealCoordinate_of_not_chain
    (parameter : PublicParameter) (allowed : Coordinate → Prop) (coordinate : Coordinate)
    (hnotChain : ¬IsChainCoordinate coordinate) :
    PreservesChainInvariant parameter allowed (revealCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hinvariant hresult
  have hfinalValid := preservesChainValid_revealCoordinate_of_not_chain allowed coordinate
    hnotChain state cache fuel finalState remaining value finalCache hinvariant.1 hresult
  rw [revealCoordinate_run, LazyRevealProbe.revealQuery,
    LazyRevealProbe.runRaw_reveal_query_bind] at hresult
  cases hvalue : state.values coordinate with
  | some existing =>
      rw [hvalue] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨hfinalValid, hinvariant.2.updateHidden coordinate existing⟩
  | none =>
      rw [hvalue, mem_support_bind_iff] at hresult
      obtain ⟨output, _, hsampled⟩ := hresult
      by_cases hhit : state.hitAt coordinate output
      · rw [if_pos hhit] at hsampled
        simp at hsampled
      · rw [if_neg hhit] at hsampled
        simp [LazyRevealProbe.runRaw] at hsampled
        rcases hsampled with ⟨rfl, rfl, rfl, rfl⟩
        refine ⟨hfinalValid, ?_⟩
        exact (hinvariant.2.updateHidden coordinate output).materialize coordinate output
          (fun hchain => (hnotChain hchain).elim)

theorem preservesChainValid_ensureFullChain (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    PreservesChainValid allowed (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (preservesChainValid_sequenceFin allowed _ fun step =>
    preservesChainValid_ensureCoordinate allowed
      (.position (.chain lay tree leafIdx chainIdx step))).bind fun _ =>
        preservesChainValid_pure allowed ()

theorem preservesChainValid_ensureChainPrefix (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (digit : Digit) :
    PreservesChainValid allowed (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (preservesChainValid_sequenceFin allowed _ fun step => by
    split
    · exact preservesChainValid_ensureCoordinate allowed
        (.position (.chain lay tree leafIdx chainIdx step))
    · exact preservesChainValid_pure allowed ()).bind fun _ =>
      preservesChainValid_pure allowed ()

theorem preservesChainValid_ensureOtsLeaf (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    PreservesChainValid allowed (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (preservesChainValid_sequenceFin allowed _ fun chainIdx =>
    preservesChainValid_ensureFullChain allowed lay tree leafIdx chainIdx).bind fun _ =>
      preservesChainValid_ensureCoordinate allowed (.position (.leaf lay tree leafIdx))

theorem preservesChainValid_ensureTreeNode (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx, PreservesChainValid allowed (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => preservesChainValid_ensureOtsLeaf allowed lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (preservesChainValid_ensureTreeNode allowed lay tree level (2 * nodeIdx)).bind
        fun _ =>
          (preservesChainValid_ensureTreeNode allowed lay tree level
            (2 * nodeIdx + 1)).bind fun _ => by
              split
              · exact preservesChainValid_ensureCoordinate allowed _
              · exact preservesChainValid_pure allowed ()

theorem preservesChainValid_maskedTreeNode (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat) :
    PreservesChainValid allowed (maskedTreeNode lay tree level nodeIdx) := by
  cases level with
  | zero =>
      rw [maskedTreeNode]
      exact (preservesChainValid_ensureTreeNode allowed lay tree 0 nodeIdx).bind fun _ =>
        preservesChainValid_revealCoordinate_of_not_chain allowed
          (.position (.leaf lay tree (leafOfNat nodeIdx))) (by simp [IsChainCoordinate])
  | succ current =>
      rw [maskedTreeNode]
      exact (preservesChainValid_ensureTreeNode allowed lay tree (current + 1) nodeIdx).bind
        fun _ => by
          by_cases hlevel : current < maxLayerHeight
          · rw [dif_pos hlevel]
            exact preservesChainValid_revealCoordinate_of_not_chain allowed
              (.position (.node lay tree ⟨current, hlevel⟩ (leafOfNat nodeIdx)))
                (by simp [IsChainCoordinate])
          · rw [dif_neg hlevel]
            exact preservesChainValid_pure allowed 0

theorem preservesChainValid_maskedTreeRoot (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) :
    PreservesChainValid allowed (maskedTreeRoot lay tree) :=
  preservesChainValid_maskedTreeNode allowed lay tree (layerHeight lay) 0

theorem preservesChainValid_ensureTreePath (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    PreservesChainValid allowed (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (preservesChainValid_sequenceFin allowed _ fun level => by
    split
    · exact preservesChainValid_ensureTreeNode allowed lay tree level.val
        (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
    · exact preservesChainValid_pure allowed ()).bind fun _ =>
      preservesChainValid_pure allowed ()

theorem preservesChainValid_maskedOtsSignFrom (allowed : Coordinate → Prop)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) : ∀ attempts counter,
    PreservesChainValid allowed
      (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => preservesChainValid_pure allowed none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      exact ((preservesChainValidImpl_ordinaryHashImpl allowed).simulateQ
        (encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))).bind fun encoded =>
            match encoded with
            | none => preservesChainValid_maskedOtsSignFrom allowed parameter lay tree leafIdx
                message attempts (counter + 1)
            | some encoding =>
                (preservesChainValid_sequenceFin allowed _ fun chainIdx =>
                  preservesChainValid_ensureChainPrefix allowed lay tree leafIdx chainIdx
                    (encoding chainIdx)).bind fun _ =>
                      preservesChainValid_pure allowed
                        (some (BitVec.ofNat counterBits counter, encoding))

theorem preservesChainValid_maskedOtsSign (allowed : Coordinate → Prop)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) :
    PreservesChainValid allowed (maskedOtsSign parameter lay tree leafIdx message) :=
  preservesChainValid_maskedOtsSignFrom allowed parameter lay tree leafIdx message
    encodingAttemptLimit 0

theorem preservesChainValid_maskedLayerMessage (allowed : Coordinate → Prop)
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    PreservesChainValid allowed (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split
  · exact preservesChainValid_maskedTreeRoot allowed _ _
  · exact (preservesChainValidImpl_ordinaryHashImpl allowed).simulateQ
      (ftsKey parameter index (ftsSecret index))

theorem preservesChainValid_maskedSignLayer (allowed : Coordinate → Prop)
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    PreservesChainValid allowed (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (preservesChainValid_maskedLayerMessage allowed parameter ftsSecret index lay).bind
    fun message =>
      (preservesChainValid_maskedOtsSign allowed parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) message).bind fun result =>
          match result with
          | none => preservesChainValid_pure allowed none
          | some part =>
              (preservesChainValid_ensureTreePath allowed lay (treeIndexAt index lay)
                (leafIndexAt index lay)).bind fun _ =>
                  preservesChainValid_pure allowed (some part)

theorem preservesChainInvariant_ensureFullChain
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    PreservesChainInvariant parameter allowed (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (preservesChainInvariant_sequenceFin parameter allowed _ fun step =>
    preservesChainInvariant_ensureCoordinate parameter allowed
      (.position (.chain lay tree leafIdx chainIdx step))).bind fun _ =>
        preservesChainInvariant_pure parameter allowed ()

theorem preservesChainInvariant_ensureChainPrefix
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (digit : Digit) :
    PreservesChainInvariant parameter allowed
      (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (preservesChainInvariant_sequenceFin parameter allowed _ fun step => by
    split
    · exact preservesChainInvariant_ensureCoordinate parameter allowed
        (.position (.chain lay tree leafIdx chainIdx step))
    · exact preservesChainInvariant_pure parameter allowed ()).bind fun _ =>
      preservesChainInvariant_pure parameter allowed ()

theorem preservesChainInvariant_ensureOtsLeaf
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    PreservesChainInvariant parameter allowed (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (preservesChainInvariant_sequenceFin parameter allowed _ fun chainIdx =>
    preservesChainInvariant_ensureFullChain parameter allowed lay tree leafIdx chainIdx).bind
      fun _ => preservesChainInvariant_ensureCoordinate parameter allowed
        (.position (.leaf lay tree leafIdx))

theorem preservesChainInvariant_ensureTreeNode
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx,
      PreservesChainInvariant parameter allowed (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => preservesChainInvariant_ensureOtsLeaf parameter allowed lay tree
      (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (preservesChainInvariant_ensureTreeNode parameter allowed lay tree level
        (2 * nodeIdx)).bind fun _ =>
          (preservesChainInvariant_ensureTreeNode parameter allowed lay tree level
            (2 * nodeIdx + 1)).bind fun _ => by
              split
              · exact preservesChainInvariant_ensureCoordinate parameter allowed _
              · exact preservesChainInvariant_pure parameter allowed ()

theorem preservesChainInvariant_maskedTreeNode
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat) :
    PreservesChainInvariant parameter allowed (maskedTreeNode lay tree level nodeIdx) := by
  cases level with
  | zero =>
      rw [maskedTreeNode]
      exact (preservesChainInvariant_ensureTreeNode parameter allowed lay tree 0 nodeIdx).bind
        fun _ => preservesChainInvariant_revealCoordinate_of_not_chain parameter allowed
          (.position (.leaf lay tree (leafOfNat nodeIdx))) (by simp [IsChainCoordinate])
  | succ current =>
      rw [maskedTreeNode]
      exact (preservesChainInvariant_ensureTreeNode parameter allowed lay tree (current + 1)
        nodeIdx).bind fun _ => by
          by_cases hlevel : current < maxLayerHeight
          · rw [dif_pos hlevel]
            exact preservesChainInvariant_revealCoordinate_of_not_chain parameter allowed
              (.position (.node lay tree ⟨current, hlevel⟩ (leafOfNat nodeIdx)))
                (by simp [IsChainCoordinate])
          · rw [dif_neg hlevel]
            exact preservesChainInvariant_pure parameter allowed 0

theorem preservesChainInvariant_maskedTreeRoot
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) :
    PreservesChainInvariant parameter allowed (maskedTreeRoot lay tree) :=
  preservesChainInvariant_maskedTreeNode parameter allowed lay tree (layerHeight lay) 0

theorem chainInvariant_maskedTreeRoot_empty
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (fuel remaining : Nat)
    (finalState : LazyRevealProbe.State Coordinate) (value : Digest)
    (finalCache : SplitHashCache)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (value, finalCache) ∈ support
      (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty :
          LazyRevealProbe.State Coordinate) fuel
        ((maskedTreeRoot lay tree).run emptySplitHashCache))) :
    ChainInvariant parameter allowed finalState finalCache := by
  have hpreserves : PreservesChainInvariant parameter allowed (maskedTreeRoot lay tree) :=
    preservesChainInvariant_maskedTreeRoot parameter allowed lay tree
  exact hpreserves (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
    emptySplitHashCache fuel finalState remaining value finalCache
      ⟨ChainState.validFor_empty allowed, chainProbeAccounted_empty parameter allowed⟩ hresult

theorem preservesChainInvariant_ensureTreePath
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    PreservesChainInvariant parameter allowed (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (preservesChainInvariant_sequenceFin parameter allowed _ fun level => by
    split
    · exact preservesChainInvariant_ensureTreeNode parameter allowed lay tree level.val
        (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
    · exact preservesChainInvariant_pure parameter allowed ()).bind fun _ =>
      preservesChainInvariant_pure parameter allowed ()

theorem preservesChainInvariant_maskedOtsSignFrom
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter,
      PreservesChainInvariant parameter allowed
        (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => preservesChainInvariant_pure parameter allowed none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      exact (preservesChainInvariant_ordinaryEncode parameter allowed lay tree leafIdx message
        (BitVec.ofNat counterBits counter)).bind fun encoded =>
          match encoded with
          | none => preservesChainInvariant_maskedOtsSignFrom parameter allowed lay tree leafIdx
              message attempts (counter + 1)
          | some encoding =>
              (preservesChainInvariant_sequenceFin parameter allowed _ fun chainIdx =>
                preservesChainInvariant_ensureChainPrefix parameter allowed lay tree leafIdx
                  chainIdx (encoding chainIdx)).bind fun _ =>
                    preservesChainInvariant_pure parameter allowed
                      (some (BitVec.ofNat counterBits counter, encoding))

theorem preservesChainInvariant_maskedOtsSign
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    PreservesChainInvariant parameter allowed
      (maskedOtsSign parameter lay tree leafIdx message) :=
  preservesChainInvariant_maskedOtsSignFrom parameter allowed lay tree leafIdx message
    encodingAttemptLimit 0

theorem preservesChainInvariant_maskedLayerMessage
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    PreservesChainInvariant parameter allowed
      (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split
  · exact preservesChainInvariant_maskedTreeRoot parameter allowed _ _
  · exact preservesChainInvariant_ordinaryFtsKey parameter allowed index (ftsSecret index)

theorem preservesChainInvariant_maskedSignLayer
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    PreservesChainInvariant parameter allowed
      (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (preservesChainInvariant_maskedLayerMessage parameter allowed ftsSecret index lay).bind
    fun message =>
      (preservesChainInvariant_maskedOtsSign parameter allowed lay (treeIndexAt index lay)
        (leafIndexAt index lay) message).bind fun result =>
          match result with
          | none => preservesChainInvariant_pure parameter allowed none
          | some part =>
              (preservesChainInvariant_ensureTreePath parameter allowed lay
                (treeIndexAt index lay) (leafIndexAt index lay)).bind fun _ =>
                  preservesChainInvariant_pure parameter allowed (some part)

theorem chainInvariant_of_mem_runRaw_maskedSignLayer
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (part : Option (Counter × (ChainIndex → Digit)))
    (hinvariant : ChainInvariant parameter allowed state cache)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (part, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((maskedSignLayer parameter ftsSecret index lay).run cache))) :
    ChainInvariant parameter allowed finalState finalCache :=
  preservesChainInvariant_maskedSignLayer parameter allowed ftsSecret index lay state cache fuel
    finalState remaining part finalCache hinvariant hresult

@[irreducible] noncomputable def maskedSignLayerAt
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))
      (Option (Counter × (ChainIndex → Digit))) :=
  maskedSignLayer parameter ftsSecret index lay

theorem maskedSignLayerAt_eq
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    maskedSignLayerAt parameter ftsSecret index lay =
      maskedSignLayer parameter ftsSecret index lay := by
  unfold maskedSignLayerAt
  rfl

@[irreducible] noncomputable def maskedSignLayers
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))
      (Layer → Option (Counter × (ChainIndex → Digit))) :=
  sequenceFin (maskedSignLayerAt parameter ftsSecret index)

theorem maskedSignLayers_eq
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) :
    maskedSignLayers parameter ftsSecret index =
      sequenceFin (maskedSignLayerAt parameter ftsSecret index) := by
  unfold maskedSignLayers
  rfl

theorem maskedSignLayers_eq_sequenceFin
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) :
    maskedSignLayers parameter ftsSecret index =
      sequenceFin fun lay => maskedSignLayer parameter ftsSecret index lay := by
  rw [maskedSignLayers_eq]
  congr 1
  funext lay
  exact maskedSignLayerAt_eq parameter ftsSecret index lay

theorem preservesChainInvariant_maskedSignLayerAt
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    PreservesChainInvariant parameter allowed
      (maskedSignLayerAt parameter ftsSecret index lay) := by
  rw [maskedSignLayerAt_eq]
  exact preservesChainInvariant_maskedSignLayer parameter allowed ftsSecret index lay

theorem preservesChainInvariant_maskedSignLayers
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) :
    PreservesChainInvariant parameter allowed
      (maskedSignLayers parameter ftsSecret index) := by
  rw [maskedSignLayers_eq]
  exact preservesChainInvariant_sequenceFin parameter allowed _
    (preservesChainInvariant_maskedSignLayerAt parameter allowed ftsSecret index)

theorem chainInvariant_of_mem_runRaw_maskedSignLayers
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (layers : Layer → Option (Counter × (ChainIndex → Digit)))
    (hinvariant : ChainInvariant parameter allowed state cache)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (layers, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((maskedSignLayers parameter ftsSecret index).run cache))) :
    ChainInvariant parameter allowed finalState finalCache := by
  have hpreserves := preservesChainInvariant_maskedSignLayers parameter allowed ftsSecret index
  unfold PreservesChainInvariant at hpreserves
  exact hpreserves state cache fuel finalState remaining layers finalCache hinvariant hresult

theorem ordinaryCacheIncreasing_maskedTreeNode
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat) :
    OrdinaryCacheIncreasing (maskedTreeNode lay tree level nodeIdx) := by
  cases level with
  | zero =>
      rw [maskedTreeNode]
      exact (SplitCachePreserving.ordinaryCacheIncreasing
        (splitCachePreserving_ensureTreeNode lay tree 0 nodeIdx)).bind fun _ =>
          ordinaryCacheIncreasing_revealCoordinate _
  | succ current =>
      rw [maskedTreeNode]
      exact (SplitCachePreserving.ordinaryCacheIncreasing
        (splitCachePreserving_ensureTreeNode lay tree (current + 1) nodeIdx)).bind fun _ => by
          by_cases hlevel : current < maxLayerHeight
          · rw [dif_pos hlevel]
            exact ordinaryCacheIncreasing_revealCoordinate _
          · rw [dif_neg hlevel]
            exact OrdinaryCacheIncreasing.pure 0

theorem ordinaryCacheIncreasing_maskedTreeRoot (lay : Layer) (tree : TreeIndex) :
    OrdinaryCacheIncreasing (maskedTreeRoot lay tree) :=
  ordinaryCacheIncreasing_maskedTreeNode lay tree (layerHeight lay) 0

def maskedTreeRootLevel (lay : Layer) : Fin maxLayerHeight :=
  ⟨layerHeight lay - 1, by
    have hpos : 0 < layerHeight lay := by
      unfold layerHeight
      split <;> norm_num [maxLayerHeight]
    have hle := layerHeight_le lay
    omega⟩

def maskedTreeRootCoordinate (lay : Layer) (tree : TreeIndex) : Coordinate :=
  .position (.node lay tree (maskedTreeRootLevel lay) 0)

theorem mem_runRaw_maskedTreeRoot_hidden
    (lay : Layer) (tree : TreeIndex)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Digest)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((maskedTreeRoot lay tree).run cache))) :
    ∃ output : HashOutput,
      value = truncateHash output ∧
        finalState.values (maskedTreeRootCoordinate lay tree) = some output ∧
        finalCache (.hidden (maskedTreeRootCoordinate lay tree)) = some output := by
  have hpos : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  have hlevel : layerHeight lay - 1 < maxLayerHeight := by
    have hle := layerHeight_le lay
    omega
  unfold maskedTreeRoot at hresult
  rw [show layerHeight lay = (layerHeight lay - 1) + 1 by omega, maskedTreeNode,
    dif_pos hlevel] at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hensured, hreveal⟩ := hresult
  cases raw with
  | stopped hit => simp at hreveal
  | done ensuredState ensuredRemaining ensuredResult =>
      rcases ensuredResult with ⟨ensuredUnit, ensuredCache⟩
      have hcache := splitCachePreserving_ensureTreeNode lay tree (layerHeight lay - 1 + 1) 0
        state cache fuel ensuredState ensuredRemaining ensuredUnit ensuredCache hensured
      subst ensuredCache
      simp only at hreveal
      rw [revealPosition_run, LazyRevealProbe.revealQuery,
        LazyRevealProbe.runRaw_reveal_query_bind] at hreveal
      let coordinate : Coordinate :=
        .position (.node lay tree ⟨layerHeight lay - 1, hlevel⟩ (leafOfNat 0))
      cases hvalue : ensuredState.values coordinate with
      | some output =>
          rw [hvalue] at hreveal
          simp [LazyRevealProbe.runRaw] at hreveal
          rcases hreveal with ⟨rfl, rfl, rfl, rfl⟩
          have hleaf : leafOfNat 0 = (0 : LeafIndex) := by
            apply Fin.ext
            simp [leafOfNat]
          exact ⟨output, rfl, by
            change finalState.values coordinate = some output
            exact hvalue, by
            simp [Function.update, maskedTreeRootCoordinate, maskedTreeRootLevel, hleaf]⟩
      | none =>
          rw [hvalue, mem_support_bind_iff] at hreveal
          obtain ⟨output, _, hsampled⟩ := hreveal
          by_cases hhit : ensuredState.hitAt coordinate output
          · rw [if_pos hhit] at hsampled
            simp at hsampled
          · rw [if_neg hhit] at hsampled
            simp [LazyRevealProbe.runRaw] at hsampled
            rcases hsampled with ⟨rfl, rfl, rfl, rfl⟩
            have hleaf : leafOfNat 0 = (0 : LeafIndex) := by
              apply Fin.ext
              simp [leafOfNat]
            exact ⟨output, rfl, by
              simp [LazyRevealProbe.State.materialize, Function.update,
                maskedTreeRootCoordinate, maskedTreeRootLevel, hleaf], by
              simp [Function.update, maskedTreeRootCoordinate, maskedTreeRootLevel, hleaf]⟩

theorem maskedTreeRoot_eq_actual
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Digest)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((maskedTreeRoot lay tree).run cache))) :
    value = evalWithAnswerFn f
      (treeRoot parameter lay tree (tableOtsSecret table lay tree)) := by
  obtain ⟨output, hvalue, hstateValue, _⟩ := mem_runRaw_maskedTreeRoot_hidden lay tree state
    finalState cache finalCache fuel remaining value hresult
  have houtput := htable _ output hstateValue
  have hpositive : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  have hlevel : layerHeight lay - 1 < maxLayerHeight := by
    have hle := layerHeight_le lay
    omega
  have hspan : 2 ^ ((layerHeight lay - 1) + 1) * (0 + 1) ≤
      2 ^ maxLayerHeight := by
    rw [show layerHeight lay - 1 + 1 = layerHeight lay by omega]
    simpa only [Nat.zero_add, Nat.mul_one] using
      Nat.pow_le_pow_right (by omega : 0 < 2) (layerHeight_le lay)
  have hnode := honestNode_eq_table_succ f parameter table lay tree hrealizes
    (layerHeight lay - 1) 0 hlevel hspan
  rw [show layerHeight lay - 1 + 1 = layerHeight lay by omega] at hnode
  change value = honestNode f parameter lay tree (tableOtsSecret table lay tree)
    (layerHeight lay) 0
  rw [hvalue, houtput]
  simpa [tableValue, maskedTreeRootCoordinate, maskedTreeRootLevel, leafOfNat] using hnode.symm

theorem ordinaryCacheIncreasing_maskedOtsSignFrom
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) : ∀ attempts counter,
    OrdinaryCacheIncreasing
      (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => OrdinaryCacheIncreasing.pure none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      exact (ordinaryCacheIncreasing_simulateQ_ordinaryHashImpl
        (encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))).bind fun encoded =>
            match encoded with
            | none => ordinaryCacheIncreasing_maskedOtsSignFrom parameter lay tree leafIdx
                message attempts (counter + 1)
            | some encoding =>
                (ordinaryCacheIncreasing_sequenceFin _ fun chainIdx =>
                  (splitCachePreserving_ensureChainPrefix lay tree leafIdx chainIdx
                    (encoding chainIdx)).ordinaryCacheIncreasing).bind fun _ =>
                      OrdinaryCacheIncreasing.pure _

theorem ordinaryCacheIncreasing_maskedOtsSign
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) :
    OrdinaryCacheIncreasing (maskedOtsSign parameter lay tree leafIdx message) :=
  ordinaryCacheIncreasing_maskedOtsSignFrom parameter lay tree leafIdx message
    encodingAttemptLimit 0

theorem ordinaryCacheIncreasing_maskedLayerMessage
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    OrdinaryCacheIncreasing (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split
  · exact ordinaryCacheIncreasing_maskedTreeRoot _ _
  · exact ordinaryCacheIncreasing_simulateQ_ordinaryHashImpl
      (ftsKey parameter index (ftsSecret index))

theorem ordinaryCacheIncreasing_maskedSignLayer
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    OrdinaryCacheIncreasing (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (ordinaryCacheIncreasing_maskedLayerMessage parameter ftsSecret index lay).bind
    fun _ => (ordinaryCacheIncreasing_maskedOtsSign parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) _).bind fun result =>
        match result with
        | none => OrdinaryCacheIncreasing.pure none
        | some part =>
            ((splitCachePreserving_ensureTreePath lay (treeIndexAt index lay)
              (leafIndexAt index lay)).ordinaryCacheIncreasing).bind fun _ =>
                OrdinaryCacheIncreasing.pure (some part)

theorem ordinaryCacheIncreasing_maskedSignLayers
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) : OrdinaryCacheIncreasing (maskedSignLayers parameter ftsSecret index) := by
  rw [maskedSignLayers_eq]
  exact ordinaryCacheIncreasing_sequenceFin _ fun lay => by
    rw [maskedSignLayerAt_eq]
    exact ordinaryCacheIncreasing_maskedSignLayer parameter ftsSecret index lay

theorem maskedSignLayers_component_run
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (layers : Layer → Option (Counter × (ChainIndex → Digit)))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (layers, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((maskedSignLayers parameter ftsSecret index).run cache)))
    (lay : Layer) :
    ∃ (componentState componentFinalState : LazyRevealProbe.State Coordinate)
        (componentCache componentFinalCache : SplitHashCache)
        (componentFuel componentRemaining : Nat)
        (part : Option (Counter × (ChainIndex → Digit))),
      LazyRevealProbe.RawResult.done componentFinalState componentRemaining
          (part, componentFinalCache) ∈ support
        (LazyRevealProbe.runRaw componentState componentFuel
          ((maskedSignLayerAt parameter ftsSecret index lay).run componentCache))
        ∧ layers lay = part
        ∧ LazyRevealProbe.ValuesLE componentFinalState finalState
        ∧ ordinaryQueryCache componentFinalCache ≤ ordinaryQueryCache finalCache := by
  rw [maskedSignLayers_eq] at hresult
  exact sequenceFin_component_run_of_done
    (computation := maskedSignLayerAt parameter ftsSecret index)
    (hincreasing := fun position => by
      rw [maskedSignLayerAt_eq]
      exact ordinaryCacheIncreasing_maskedSignLayer parameter ftsSecret index position)
    (state := state) (finalState := finalState) (cache := cache) (finalCache := finalCache)
    (fuel := fuel) (remaining := remaining) (values := layers) hresult lay

noncomputable def maskedOtsLayerAfterMessage
    (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))
      (Option (Counter × (ChainIndex → Digit))) := do
  let result ← maskedOtsSign parameter lay (treeIndexAt index lay)
    (leafIndexAt index lay) message
  match result with
  | none => pure none
  | some (counter, encoding) => do
      ensureTreePath lay (treeIndexAt index lay) (leafIndexAt index lay)
      pure (some (counter, encoding))

theorem ordinaryCacheIncreasing_maskedSignLayerAfterMessage
    (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest) :
    OrdinaryCacheIncreasing (maskedOtsLayerAfterMessage parameter index lay message) := by
  unfold maskedOtsLayerAfterMessage
  exact
  (ordinaryCacheIncreasing_maskedOtsSign parameter lay (treeIndexAt index lay)
    (leafIndexAt index lay) message).bind fun result =>
      match result with
      | none => OrdinaryCacheIncreasing.pure none
      | some (counter, encoding) =>
          ((splitCachePreserving_ensureTreePath lay (treeIndexAt index lay)
            (leafIndexAt index lay)).ordinaryCacheIncreasing).bind fun _ =>
              OrdinaryCacheIncreasing.pure (some (counter, encoding))

theorem maskedTreeRoot_eq_layerMessage_of_lt
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay below : Layer) (hbelow : lay.val + 1 < numLayers)
    (hbelowEq : below = ⟨lay.val + 1, hbelow⟩)
    (state finalState referenceState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Digest)
    (hle : LazyRevealProbe.ValuesLE finalState referenceState)
    (htable : ∀ coordinate output, referenceState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((maskedTreeRoot below (treeIndexAt index below)).run cache))) :
    value = evalWithAnswerFn f
      (layerMessage (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
        index lay) := by
  have htableFinal : ∀ coordinate output,
      finalState.values coordinate = some output → output = table coordinate :=
    fun coordinate output hvalue => htable coordinate output (hle coordinate output hvalue)
  have hroot := maskedTreeRoot_eq_actual
    (f := f) (parameter := parameter) (table := table) (lay := below)
    (tree := treeIndexAt index below) (state := state) (finalState := finalState)
    (cache := cache) (finalCache := finalCache) (fuel := fuel) (remaining := remaining)
    (value := value) htableFinal hrealizes hresult
  rw [layerMessage_of_lt _ _ _ hbelow]
  rw [← hbelowEq]
  exact hroot

theorem maskedLayerMessage_eq_actual_of_not_lt
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) (hbelow : ¬lay.val + 1 < numLayers)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Digest)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((maskedLayerMessage parameter ftsSecret index lay).run cache))) :
    value = evalWithAnswerFn f
      (layerMessage (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
        index lay) := by
  unfold maskedLayerMessage at hresult
  rw [dif_neg hbelow] at hresult
  have heval := replay_of_mem_runRaw_ordinaryHashImpl_of_stable f parameter
    (ftsKey parameter index (ftsSecret index)) state finalState cache finalCache fuel remaining
      value hf (queriesStable_ftsKey f parameter index (ftsSecret index)) hresult
  rw [layerMessage, dif_neg hbelow]
  exact heval.1.symm

theorem maskedSignLayerAfterMessage_some_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (lay : Layer)
    (message actualMessage : Digest)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (counter : Counter) (encoding : ChainIndex → Digit)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (hmessage : message = actualMessage)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some (counter, encoding), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedOtsLayerAfterMessage parameter index lay message).run cache))) :
    evalWithAnswerFn f
      (encode parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        actualMessage counter) = some encoding := by
  unfold maskedOtsLayerAfterMessage at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨otsRaw, hots, hafterOts⟩ := hresult
  cases otsRaw with
  | stopped stoppedHit => simp at hafterOts
  | done otsState otsRemaining otsResult =>
      rcases otsResult with ⟨part, otsCache⟩
      cases part with
      | none => simp [LazyRevealProbe.runRaw] at hafterOts
      | some selectedPart =>
          rcases selectedPart with ⟨selectedCounter, selectedEncoding⟩
          simp only at hafterOts
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hafterOts
          obtain ⟨pathRaw, hpath, hfinish⟩ := hafterOts
          cases pathRaw with
          | stopped stoppedHit => simp at hfinish
          | done pathState pathRemaining pathResult =>
              rcases pathResult with ⟨pathUnit, pathCache⟩
              have hpathCache := splitCachePreserving_ensureTreePath lay
                (treeIndexAt index lay) (leafIndexAt index lay) otsState otsCache otsRemaining
                  pathState pathRemaining pathUnit pathCache hpath
              simp [LazyRevealProbe.runRaw] at hfinish
              rcases hfinish with ⟨rfl, rfl, hpart, rfl⟩
              obtain ⟨hcounter, hencoding⟩ := hpart
              subst selectedCounter
              subst selectedEncoding
              rw [hpathCache] at hf
              have hencoded := maskedOtsSign_some_eval f parameter lay
                (treeIndexAt index lay) (leafIndexAt index lay) message state otsState cache
                  otsCache fuel otsRemaining counter encoding hf hots
              rw [hmessage] at hencoded
              exact hencoded

theorem maskedLayerMessage_eq_of_lt
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) (hbelow : lay.val + 1 < numLayers) :
    maskedLayerMessage parameter ftsSecret index lay =
      maskedTreeRoot ⟨lay.val + 1, hbelow⟩
        (treeIndexAt index ⟨lay.val + 1, hbelow⟩) := by
  unfold maskedLayerMessage
  rw [dif_pos hbelow]

theorem maskedLayerMessage_eq_of_lt'
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay below : Layer) (hbelow : lay.val + 1 < numLayers)
    (hbelowEq : below = ⟨lay.val + 1, hbelow⟩) :
    maskedLayerMessage parameter ftsSecret index lay =
      maskedTreeRoot below (treeIndexAt index below) := by
  subst below
  exact maskedLayerMessage_eq_of_lt parameter ftsSecret index lay hbelow

theorem maskedLayerMessage_eq_actual_of_lt
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay below : Layer) (hbelow : lay.val + 1 < numLayers)
    (hbelowEq : below = ⟨lay.val + 1, hbelow⟩)
    (state messageState referenceState : LazyRevealProbe.State Coordinate)
    (cache messageCache : SplitHashCache) (fuel messageRemaining : Nat)
    (message : Digest)
    (hle : LazyRevealProbe.ValuesLE messageState referenceState)
    (htable : ∀ coordinate output, referenceState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hmessage : LazyRevealProbe.RawResult.done messageState messageRemaining
        (message, messageCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedLayerMessage parameter ftsSecret index lay).run cache))) :
    message = evalWithAnswerFn f
      (layerMessage (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
        index lay) := by
  rw [maskedLayerMessage_eq_of_lt' parameter ftsSecret index lay below hbelow hbelowEq] at hmessage
  exact maskedTreeRoot_eq_layerMessage_of_lt
    (f := f) (parameter := parameter) (root := root) (table := table)
    (ftsSecret := ftsSecret) (index := index) (lay := lay) (below := below)
    (hbelow := hbelow) (hbelowEq := hbelowEq) (state := state)
    (finalState := messageState) (referenceState := referenceState) (cache := cache)
    (finalCache := messageCache) (fuel := fuel) (remaining := messageRemaining)
    (value := message) hle htable hrealizes hmessage

theorem maskedSignLayerParts_some_eval_of_lt
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay below : Layer) (hbelow : lay.val + 1 < numLayers)
    (hbelowEq : below = ⟨lay.val + 1, hbelow⟩)
    (state messageState finalState : LazyRevealProbe.State Coordinate)
    (cache messageCache finalCache : SplitHashCache) (fuel messageRemaining remaining : Nat)
    (message : Digest) (counter : Counter) (encoding : ChainIndex → Digit)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hmessage : LazyRevealProbe.RawResult.done messageState messageRemaining
        (message, messageCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedLayerMessage parameter ftsSecret index lay).run cache)))
    (hafter : LazyRevealProbe.RawResult.done finalState remaining
        (some (counter, encoding), finalCache) ∈ support
      (LazyRevealProbe.runRaw messageState messageRemaining
        ((maskedOtsLayerAfterMessage parameter index lay message).run messageCache))) :
    evalWithAnswerFn f
      (encode parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f
          (layerMessage (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
            index lay)) counter) = some encoding := by
  have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
    ((maskedOtsLayerAfterMessage parameter index lay message).run messageCache)
      messageState finalState messageRemaining remaining
        (some (counter, encoding), finalCache) hafter
  have hmessageActual := maskedLayerMessage_eq_actual_of_lt
    (f := f) (parameter := parameter) (root := root) (table := table)
    (ftsSecret := ftsSecret) (index := index) (lay := lay) (below := below)
    (hbelow := hbelow) (hbelowEq := hbelowEq) (state := state)
    (messageState := messageState) (referenceState := finalState)
    (cache := cache) (messageCache := messageCache) (fuel := fuel)
    (messageRemaining := messageRemaining) (message := message) hvaluesLE htable hrealizes hmessage
  exact maskedSignLayerAfterMessage_some_eval
    (f := f) (parameter := parameter) (index := index) (lay := lay) (message := message)
    (actualMessage := _) (state := messageState) (finalState := finalState)
    (cache := messageCache) (finalCache := finalCache) (fuel := messageRemaining)
    (remaining := remaining) (counter := counter) (encoding := encoding) hf hmessageActual hafter

theorem maskedSignLayer_some_eval_of_lt
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) (hbelow : lay.val + 1 < numLayers)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (counter : Counter) (encoding : ChainIndex → Digit)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some (counter, encoding), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedSignLayer parameter ftsSecret index lay).run cache))) :
    evalWithAnswerFn f
      (encode parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f
          (layerMessage (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
            index lay)) counter) = some encoding := by
  unfold maskedSignLayer at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨messageRaw, hmessage, hafterMessage⟩ := hresult
  cases messageRaw with
  | stopped stoppedHit => simp at hafterMessage
  | done messageState messageRemaining messageResult =>
      rcases messageResult with ⟨message, messageCache⟩
      simp only at hafterMessage
      change LazyRevealProbe.RawResult.done finalState remaining
          (some (counter, encoding), finalCache) ∈ support
        (LazyRevealProbe.runRaw messageState messageRemaining
          ((maskedOtsLayerAfterMessage parameter index lay message).run messageCache)) at hafterMessage
      let below : Layer := ⟨lay.val + 1, hbelow⟩
      exact maskedSignLayerParts_some_eval_of_lt
        (f := f) (parameter := parameter) (root := root) (table := table)
        (ftsSecret := ftsSecret) (index := index) (lay := lay) (below := below)
        (hbelow := hbelow) (hbelowEq := rfl)
        (state := state) (messageState := messageState) (finalState := finalState)
        (cache := cache) (messageCache := messageCache) (finalCache := finalCache)
        (fuel := fuel) (messageRemaining := messageRemaining) (remaining := remaining)
        (message := message) (counter := counter) (encoding := encoding) hf htable hrealizes
          hmessage hafterMessage

theorem maskedSignLayer_some_eval_of_not_lt
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) (hbelow : ¬lay.val + 1 < numLayers)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (counter : Counter) (encoding : ChainIndex → Digit)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some (counter, encoding), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedSignLayer parameter ftsSecret index lay).run cache))) :
    evalWithAnswerFn f
      (encode parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f
          (layerMessage (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
            index lay)) counter) = some encoding := by
  unfold maskedSignLayer at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨messageRaw, hmessage, hafterMessage⟩ := hresult
  cases messageRaw with
  | stopped stoppedHit => simp at hafterMessage
  | done messageState messageRemaining messageResult =>
      rcases messageResult with ⟨message, messageCache⟩
      simp only at hafterMessage
      change LazyRevealProbe.RawResult.done finalState remaining
          (some (counter, encoding), finalCache) ∈ support
        (LazyRevealProbe.runRaw messageState messageRemaining
          ((maskedOtsLayerAfterMessage parameter index lay message).run messageCache)) at hafterMessage
      have hordinaryLE := ordinaryCacheIncreasing_maskedSignLayerAfterMessage parameter index lay
        message messageState messageCache messageRemaining finalState remaining
          (some (counter, encoding)) finalCache hafterMessage
      have hfMessage : StableCacheAgreesWithFn parameter messageCache f :=
        fun input output hstable hcached => hf input output hstable (hordinaryLE hcached)
      have hmessageActual := maskedLayerMessage_eq_actual_of_not_lt f parameter root table
        ftsSecret index lay hbelow state messageState cache messageCache fuel messageRemaining
          message hfMessage hmessage
      exact maskedSignLayerAfterMessage_some_eval f parameter index lay message _ messageState
        finalState messageCache finalCache messageRemaining remaining counter encoding hf
          hmessageActual hafterMessage

def HonestLayerParts (f : QueryImpl HashSpec Id) (secretKey : SecretKey) (index : Index)
    (parts : Layer → Counter × (ChainIndex → Digit)) : Prop :=
  ∀ lay, evalWithAnswerFn f
    (encode secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn f (layerMessage secretKey index lay)) (parts lay).1) =
        some (parts lay).2

theorem maskedSignLayers_parts_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (layers : Layer → Option (Counter × (ChainIndex → Digit)))
    (parts : Layer → Counter × (ChainIndex → Digit))
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (layers, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((maskedSignLayers parameter ftsSecret index).run cache)))
    (hparts : traverseOption layers = some parts) :
    HonestLayerParts f
      (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index parts := by
  intro lay
  obtain ⟨componentState, componentFinalState, componentCache, componentFinalCache,
    componentFuel, componentRemaining, part, hcomponent, hselected, hvaluesLE, hcacheLE⟩ :=
      maskedSignLayers_component_run parameter ftsSecret index state finalState cache finalCache
        fuel remaining layers hresult lay
  have hpartsAt := traverseOption_eq_some_apply layers parts hparts lay
  have hpart : part = some (parts lay) := hselected.symm.trans hpartsAt
  have hcomponent' := hcomponent
  rw [hpart, maskedSignLayerAt_eq] at hcomponent'
  have hfComponent : StableCacheAgreesWithFn parameter componentFinalCache f :=
    fun input output hstable hcached => hf input output hstable (hcacheLE hcached)
  have htableComponent : ∀ coordinate output,
      componentFinalState.values coordinate = some output → output = table coordinate :=
    fun coordinate output hvalue => htable coordinate output
      (hvaluesLE coordinate output hvalue)
  by_cases hbelow : lay.val + 1 < numLayers
  · exact maskedSignLayer_some_eval_of_lt f parameter root table ftsSecret index lay hbelow
      componentState componentFinalState componentCache componentFinalCache componentFuel
        componentRemaining (parts lay).1 (parts lay).2 hfComponent htableComponent hrealizes
          hcomponent'
  · exact maskedSignLayer_some_eval_of_not_lt f parameter root table ftsSecret index lay hbelow
      componentState componentFinalState componentCache componentFinalCache componentFuel
        componentRemaining (parts lay).1 (parts lay).2 hfComponent hcomponent'

theorem ordinaryCacheIncreasing_revealLayerValues
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    OrdinaryCacheIncreasing (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (ordinaryCacheIncreasing_sequenceFin _ fun chainIdx =>
    ordinaryCacheIncreasing_revealPublishedCoordinate
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx (encoding chainIdx))).bind fun _ =>
      (ordinaryCacheIncreasing_sequenceFin _ fun level => by
        split
        · cases hlevelValue : level.val with
          | zero => exact ordinaryCacheIncreasing_revealPublishedCoordinate _
          | succ current =>
              rw [show current + 1 = Nat.succ current by omega]
              change OrdinaryCacheIncreasing
                (if hlevel : current < maxLayerHeight then
                  revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
                    ⟨current, hlevel⟩ (leafOfNat
                      (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
                else pure 0)
              by_cases hlevel : current < maxLayerHeight
              · rw [dif_pos hlevel]
                exact ordinaryCacheIncreasing_revealPublishedCoordinate _
              · rw [dif_neg hlevel]
                exact OrdinaryCacheIncreasing.pure 0
        · exact OrdinaryCacheIncreasing.pure 0).bind fun _ => OrdinaryCacheIncreasing.pure _

theorem ordinaryCacheIncreasing_maskedSignAfterDigest
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    OrdinaryCacheIncreasing
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest
  exact (ordinaryCacheIncreasing_simulateQ_ordinaryHashImpl
    (ftsOpen parameter index leaves (ftsSecret index))).bind fun _ =>
      (ordinaryCacheIncreasing_sequenceFin _ fun lay =>
        ordinaryCacheIncreasing_maskedSignLayer parameter ftsSecret index lay).bind fun layers =>
          match hparts : traverseOption layers with
          | none => OrdinaryCacheIncreasing.pure none
          | some parts =>
              (ordinaryCacheIncreasing_sequenceFin _ fun lay =>
                ordinaryCacheIncreasing_revealLayerValues index lay (parts lay).2).bind fun _ =>
                  OrdinaryCacheIncreasing.pure _

theorem ordinaryCacheIncreasing_maskedSign
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    OrdinaryCacheIncreasing (maskedSign parameter root ftsSecret message) := by
  unfold maskedSign
  exact (ordinaryCacheIncreasing_ordinarySignDigestLoop digestAttemptLimit
    (⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ : SecretKey) message).bind fun selected =>
      match selected with
      | none => OrdinaryCacheIncreasing.pure none
      | some data => ordinaryCacheIncreasing_maskedSignAfterDigest parameter ftsSecret
          data.1 data.2.1 data.2.2

theorem ordinaryEntryPreservingImpl_maskedSigningImpl
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : HashInput) :
    OrdinaryEntryPreservingImpl input (maskedSigningImpl parameter root ftsSecret) := by
  intro message
  exact (ordinaryCacheIncreasing_maskedSign parameter root ftsSecret message).entryPreserving
    input

theorem ordinaryEntryPreservingImpl_maskedExpandedAdversaryImpl
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : HashInput)
    (hstable : StableOrdinaryInput parameter input) :
    OrdinaryEntryPreservingImpl input
      (maskedExpandedAdversaryImpl parameter root ftsSecret) := by
  intro query
  cases query with
  | inl query => exact ordinaryEntryPreservingImpl_probingRomImpl parameter input hstable query
  | inr query =>
      exact ordinaryEntryPreservingImpl_maskedSigningImpl parameter root ftsSecret input query

theorem preservesChainValid_revealPublishedCoordinate
    (allowed : Coordinate → Prop) (coordinate : Coordinate)
    (hallowed : IsChainCoordinate coordinate → allowed coordinate) :
    PreservesChainValid allowed (revealPublishedCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  unfold revealPublishedCoordinate at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hreveal, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done revealState revealRemaining revealResult =>
    rcases revealResult with ⟨revealedValue, revealCache⟩
    have hrevealShape :
        (state.values coordinate ≠ none ∧ revealState = state) ∨
          ∃ output, revealState = state.materialize coordinate output := by
      change LazyRevealProbe.RawResult.done revealState revealRemaining
          (revealedValue, revealCache) ∈ support
        (LazyRevealProbe.runRaw state fuel ((revealCoordinate coordinate).run cache)) at hreveal
      rw [revealCoordinate_run, LazyRevealProbe.revealQuery,
        LazyRevealProbe.runRaw_reveal_query_bind] at hreveal
      cases hvalue : state.values coordinate with
      | some existing =>
          rw [hvalue] at hreveal
          simp [LazyRevealProbe.runRaw] at hreveal
          rcases hreveal with ⟨rfl, rfl, rfl, rfl⟩
          exact Or.inl ⟨by simp, rfl⟩
      | none =>
          rw [hvalue, mem_support_bind_iff] at hreveal
          obtain ⟨sampled, _, hsampled⟩ := hreveal
          by_cases hhit : state.hitAt coordinate sampled
          · rw [if_pos hhit] at hsampled
            simp at hsampled
          · rw [if_neg hhit] at hsampled
            simp [LazyRevealProbe.runRaw] at hsampled
            rcases hsampled with ⟨rfl, rfl, rfl, rfl⟩
            exact Or.inr ⟨sampled, rfl⟩
    simp only at hrest
    rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
    obtain ⟨publishRaw, hpublish, hfinish⟩ := hrest
    cases publishRaw with
    | stopped hit => simp at hfinish
    | done publishState publishRemaining publishResult =>
      rcases publishResult with ⟨publishedUnit, publishCache⟩
      change LazyRevealProbe.RawResult.done publishState publishRemaining
          (publishedUnit, publishCache) ∈ support
        (LazyRevealProbe.runRaw revealState revealRemaining
          (LazyRevealProbe.publishQuery coordinate >>= fun output =>
            pure (output, revealCache))) at hpublish
      rw [LazyRevealProbe.publishQuery,
        LazyRevealProbe.runRaw_publish_query_bind] at hpublish
      simp [LazyRevealProbe.runRaw] at hpublish
      rcases hpublish with ⟨rfl, rfl, rfl, rfl⟩
      simp [LazyRevealProbe.runRaw] at hfinish
      rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
      rcases hrevealShape with ⟨hvalue, rfl⟩ | ⟨output, rfl⟩
      · exact hvalid.publish coordinate hvalue hallowed
      · exact hvalid.materialize_publish coordinate output hallowed

theorem preservesChainInvariant_revealPublishedCoordinate
    (parameter : PublicParameter) (allowed : Coordinate → Prop) (coordinate : Coordinate)
    (hallowed : IsChainCoordinate coordinate → allowed coordinate) :
    PreservesChainInvariant parameter allowed (revealPublishedCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hinvariant hresult
  have hfinalValid := preservesChainValid_revealPublishedCoordinate allowed coordinate hallowed
    state cache fuel finalState remaining value finalCache hinvariant.1 hresult
  unfold revealPublishedCoordinate at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hreveal, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealedValue, revealCache⟩
      have hrevealShape :
          (∃ output, state.values coordinate = some output ∧
              revealedValue = truncateHash output ∧ revealState = state ∧
              revealCache = Function.update cache (.hidden coordinate) (some output)) ∨
            ∃ output, revealedValue = truncateHash output ∧
              revealState = state.materialize coordinate output ∧
              revealCache = Function.update cache (.hidden coordinate) (some output) := by
        rw [revealCoordinate_run, LazyRevealProbe.revealQuery,
          LazyRevealProbe.runRaw_reveal_query_bind] at hreveal
        cases hvalue : state.values coordinate with
        | some existing =>
            rw [hvalue] at hreveal
            simp [LazyRevealProbe.runRaw] at hreveal
            rcases hreveal with ⟨rfl, rfl, rfl, rfl⟩
            exact Or.inl ⟨existing, rfl, rfl, rfl, rfl⟩
        | none =>
            rw [hvalue, mem_support_bind_iff] at hreveal
            obtain ⟨output, _, hsampled⟩ := hreveal
            by_cases hhit : state.hitAt coordinate output
            · rw [if_pos hhit] at hsampled
              simp at hsampled
            · rw [if_neg hhit] at hsampled
              simp [LazyRevealProbe.runRaw] at hsampled
              rcases hsampled with ⟨rfl, rfl, rfl, rfl⟩
              exact Or.inr ⟨output, rfl, rfl, rfl⟩
      simp only at hrest
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
      obtain ⟨publishRaw, hpublish, hfinish⟩ := hrest
      cases publishRaw with
      | stopped hit => simp at hfinish
      | done publishState publishRemaining publishResult =>
          rcases publishResult with ⟨publishedUnit, publishCache⟩
          change LazyRevealProbe.RawResult.done publishState publishRemaining
              (publishedUnit, publishCache) ∈ support
            (LazyRevealProbe.runRaw revealState revealRemaining
              (LazyRevealProbe.publishQuery coordinate >>= fun output =>
                pure (output, revealCache))) at hpublish
          rw [LazyRevealProbe.publishQuery,
            LazyRevealProbe.runRaw_publish_query_bind] at hpublish
          simp [LazyRevealProbe.runRaw] at hpublish
          rcases hpublish with ⟨rfl, rfl, rfl, rfl⟩
          simp [LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
          refine ⟨hfinalValid, ?_⟩
          rcases hrevealShape with ⟨output, hvalue, rfl, rfl, rfl⟩ |
              ⟨output, rfl, rfl, rfl⟩
          · exact (hinvariant.2.updateHidden coordinate output).publish coordinate
          · exact (hinvariant.2.updateHidden coordinate output).materialize_publish
              coordinate output hallowed

def PublishedByParts (index : Index)
    (parts : Layer → Counter × (ChainIndex → Digit))
    (coordinate : Coordinate) : Prop :=
  ∃ lay chainIdx,
    coordinate = chainValueCoordinate lay (treeIndexAt index lay)
      (leafIndexAt index lay) chainIdx ((parts lay).2 chainIdx)

theorem publishedByParts_selected (index : Index)
    (parts : Layer → Counter × (ChainIndex → Digit))
    (lay : Layer) (chainIdx : ChainIndex) :
    PublishedByParts index parts
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx ((parts lay).2 chainIdx)) :=
  ⟨lay, chainIdx, rfl⟩

theorem preservesChainValid_revealLayerValues (allowed : Coordinate → Prop)
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit)
    (hallowed : ∀ chainIdx, allowed (chainValueCoordinate lay (treeIndexAt index lay)
      (leafIndexAt index lay) chainIdx (encoding chainIdx))) :
    PreservesChainValid allowed (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (preservesChainValid_sequenceFin allowed _ fun chainIdx =>
    preservesChainValid_revealPublishedCoordinate allowed
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx (encoding chainIdx)) (fun _ => hallowed chainIdx)).bind fun values =>
      (preservesChainValid_sequenceFin allowed _ fun level => by
        split
        · cases hlevelValue : level.val with
          | zero =>
              exact preservesChainValid_revealPublishedCoordinate allowed _
                (by simp [IsChainCoordinate])
          | succ current =>
              rw [show current + 1 = Nat.succ current by omega]
              change PreservesChainValid allowed
                (if hlevel : current < maxLayerHeight then
                  revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
                    ⟨current, hlevel⟩ (leafOfNat
                      (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
                else pure 0)
              by_cases hlevel : current < maxLayerHeight
              · rw [dif_pos hlevel]
                exact preservesChainValid_revealPublishedCoordinate allowed _
                  (by simp [IsChainCoordinate])
              · rw [dif_neg hlevel]
                exact preservesChainValid_pure allowed 0
        · exact preservesChainValid_pure allowed 0).bind fun path =>
          preservesChainValid_pure allowed (values, path)

theorem preservesChainInvariant_revealLayerValues
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit)
    (hallowed : ∀ chainIdx, allowed (chainValueCoordinate lay (treeIndexAt index lay)
      (leafIndexAt index lay) chainIdx (encoding chainIdx))) :
    PreservesChainInvariant parameter allowed (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (preservesChainInvariant_sequenceFin parameter allowed _ fun chainIdx =>
    preservesChainInvariant_revealPublishedCoordinate parameter allowed
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx (encoding chainIdx)) (fun _ => hallowed chainIdx)).bind fun values =>
      (preservesChainInvariant_sequenceFin parameter allowed _ fun level => by
        split
        · cases hlevelValue : level.val with
          | zero =>
              exact preservesChainInvariant_revealPublishedCoordinate parameter allowed _
                (by simp [IsChainCoordinate])
          | succ current =>
              rw [show current + 1 = Nat.succ current by omega]
              change PreservesChainInvariant parameter allowed
                (if hlevel : current < maxLayerHeight then
                  revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
                    ⟨current, hlevel⟩ (leafOfNat
                      (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
                else pure 0)
              by_cases hlevel : current < maxLayerHeight
              · rw [dif_pos hlevel]
                exact preservesChainInvariant_revealPublishedCoordinate parameter allowed _
                  (by simp [IsChainCoordinate])
              · rw [dif_neg hlevel]
                exact preservesChainInvariant_pure parameter allowed 0
        · exact preservesChainInvariant_pure parameter allowed 0).bind fun path =>
          preservesChainInvariant_pure parameter allowed (values, path)

theorem chainInvariant_revealLayersForParts
    (parameter : PublicParameter) (initial : Coordinate → Prop)
    (index : Index) (parts : Layer → Counter × (ChainIndex → Digit))
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (values : Layer → (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))
    (hinvariant : ChainInvariant parameter initial state cache)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (values, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((sequenceFin fun lay => revealLayerValues index lay (parts lay).2).run cache))) :
    ChainInvariant parameter
      (fun coordinate => initial coordinate ∨ PublishedByParts index parts coordinate)
      finalState finalCache := by
  let allowed := fun coordinate => initial coordinate ∨ PublishedByParts index parts coordinate
  have hinvariantAllowed : ChainInvariant parameter allowed state cache :=
    hinvariant.mono fun coordinate hcoordinate => Or.inl hcoordinate
  exact preservesChainInvariant_sequenceFin parameter allowed _
    (fun lay => preservesChainInvariant_revealLayerValues parameter allowed index lay
      (parts lay).2 fun chainIdx => Or.inr (publishedByParts_selected index parts lay chainIdx))
    state cache fuel finalState remaining values finalCache hinvariantAllowed hresult

set_option linter.constructorNameAsVariable false in
theorem chainInvariant_maskedSignAfterDigest
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (initial : Coordinate → Prop)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (result : Option Signature)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hinvariant : ChainInvariant parameter initial state cache)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (result, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((maskedSignAfterDigest parameter ftsSecret randomness index leaves).run cache))) :
    (result = none ∧ ChainInvariant parameter initial finalState finalCache) ∨
      ∃ (signature : Signature) (parts : Layer → Counter × (ChainIndex → Digit)),
        result = some signature
          ∧ signature.randomness = randomness
          ∧ signature.counter = (fun lay => (parts lay).1)
          ∧ HonestLayerParts f
            (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index parts
          ∧ ChainInvariant parameter
            (fun coordinate => initial coordinate ∨ PublishedByParts index parts coordinate)
            finalState finalCache := by
  unfold maskedSignAfterDigest at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨pathRaw, hpath, hafterPath⟩ := hresult
  cases pathRaw with
  | stopped stoppedHit => simp at hafterPath
  | done pathState pathRemaining pathResult =>
      rcases pathResult with ⟨ftsPath, pathCache⟩
      have hpathInvariant := preservesChainInvariant_ordinaryFtsOpen parameter initial index leaves
        (ftsSecret index) state cache fuel pathState pathRemaining ftsPath pathCache hinvariant hpath
      simp only at hafterPath
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hafterPath
      obtain ⟨layersRaw, hlayers, hafterLayers⟩ := hafterPath
      cases layersRaw with
      | stopped stoppedHit => simp at hafterLayers
      | done layersState layersRemaining layersResult =>
          rcases layersResult with ⟨layers, layersCache⟩
          rw [← maskedSignLayers_eq_sequenceFin parameter ftsSecret index] at hlayers
          have hlayersInvariant := chainInvariant_of_mem_runRaw_maskedSignLayers
            (parameter := parameter) (allowed := initial) (ftsSecret := ftsSecret)
            (index := index) (state := pathState) (finalState := layersState)
            (cache := pathCache) (finalCache := layersCache) (fuel := pathRemaining)
            (remaining := layersRemaining) (layers := layers) hpathInvariant hlayers
          simp only at hafterLayers
          cases hparts : traverseOption layers with
          | none =>
              rw [hparts] at hafterLayers
              simp [LazyRevealProbe.runRaw] at hafterLayers
              rcases hafterLayers with ⟨rfl, rfl, rfl, rfl⟩
              exact Or.inl ⟨rfl, hlayersInvariant⟩
          | some parts =>
              rw [hparts, StateT.run_bind, LazyRevealProbe.runRaw_bind,
                mem_support_bind_iff] at hafterLayers
              obtain ⟨revealedRaw, hrevealed, hfinish⟩ := hafterLayers
              cases revealedRaw with
              | stopped stoppedHit => simp at hfinish
              | done revealedState revealedRemaining revealedResult =>
                  rcases revealedResult with ⟨revealed, revealedCache⟩
                  have hrevealedValues := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                    ((sequenceFin fun lay => revealLayerValues index lay (parts lay).2).run
                      layersCache) layersState revealedState layersRemaining revealedRemaining
                        (revealed, revealedCache) hrevealed
                  have hrevealedCache := ordinaryCacheIncreasing_sequenceFin
                    (fun lay => revealLayerValues index lay (parts lay).2)
                    (fun lay => ordinaryCacheIncreasing_revealLayerValues index lay (parts lay).2)
                    layersState layersCache layersRemaining revealedState revealedRemaining
                      revealed revealedCache hrevealed
                  have hrevealedInvariant := chainInvariant_revealLayersForParts parameter initial
                    index parts layersState revealedState layersCache revealedCache layersRemaining
                      revealedRemaining revealed hlayersInvariant hrevealed
                  simp [LazyRevealProbe.runRaw] at hfinish
                  rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
                  have hfLayers : StableCacheAgreesWithFn parameter layersCache f :=
                    fun input output hstable hcached =>
                      hf input output hstable (hrevealedCache hcached)
                  have htableLayers : ∀ coordinate output,
                      layersState.values coordinate = some output → output = table coordinate :=
                    fun coordinate output hvalue => htable coordinate output
                      (hrevealedValues coordinate output hvalue)
                  have hhonestParts := maskedSignLayers_parts_eval f parameter root table ftsSecret
                    index pathState layersState pathCache layersCache pathRemaining layersRemaining
                      layers parts hfLayers htableLayers hrealizes hlayers hparts
                  exact Or.inr ⟨_, parts, rfl, rfl, rfl, hhonestParts, hrevealedInvariant⟩

theorem chainInvariant_maskedSign
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (message : Message) (initial : Coordinate → Prop)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (result : Option Signature)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hinvariant : ChainInvariant parameter initial state cache)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (result, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((maskedSign parameter root ftsSecret message).run cache))) :
    (result = none ∧ ChainInvariant parameter initial finalState finalCache) ∨
      ∃ (signature : Signature) (index : Index) (leaves : DigestTree → FtsLeaf)
          (parts : Layer → Counter × (ChainIndex → Digit)),
        result = some signature
          ∧ SuccessfulDigestRun f (ordinaryQueryCache finalCache)
            (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
              message signature.randomness index leaves
          ∧ signature.counter = (fun lay => (parts lay).1)
          ∧ HonestLayerParts f
            (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index parts
          ∧ ChainInvariant parameter
            (fun coordinate => initial coordinate ∨ PublishedByParts index parts coordinate)
            finalState finalCache := by
  let secretKey : SecretKey :=
    ⟨parameter, root, tableOtsSecret table, ftsSecret⟩
  let digestSecretKey : SecretKey :=
    ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩
  unfold maskedSign at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨loopRaw, hloop, hrest⟩ := hresult
  cases loopRaw with
  | stopped stoppedHit => simp at hrest
  | done loopState loopRemaining loopResult =>
      rcases loopResult with ⟨selected, loopCache⟩
      have hloopInvariant := preservesChainInvariant_ordinarySignDigestLoop initial
        digestAttemptLimit digestSecretKey message state cache fuel loopState loopRemaining
          selected loopCache hinvariant hloop
      simp only at hrest
      cases selected with
      | none =>
          simp [LazyRevealProbe.runRaw] at hrest
          rcases hrest with ⟨rfl, rfl, rfl, rfl⟩
          exact Or.inl ⟨rfl, hloopInvariant⟩
      | some selected =>
          obtain ⟨randomness, index, leaves⟩ := selected
          have hcacheLE := ordinaryCacheIncreasing_maskedSignAfterDigest parameter ftsSecret
            randomness index leaves loopState loopCache loopRemaining finalState remaining result
              finalCache hrest
          have hdigestLoop := successfulDigestLoop_of_mem_runRaw_ordinaryRomImpl f
            digestSecretKey message digestAttemptLimit randomness index leaves state loopState
              cache loopCache fuel loopRemaining finalCache hcacheLE hf hloop
          have hdigest : SuccessfulDigestRun f (ordinaryQueryCache finalCache) secretKey message
              randomness index leaves := by
            simpa only [SuccessfulDigestRun, signAttempt, digestSecretKey, secretKey] using
              hdigestLoop
          have hafter := chainInvariant_maskedSignAfterDigest f parameter root table ftsSecret
            randomness index leaves initial loopState finalState loopCache finalCache loopRemaining
              remaining result hf htable hrealizes hloopInvariant hrest
          rcases hafter with ⟨rfl, hfinalInvariant⟩ |
              ⟨signature, parts, hsignature, hrandomness, hcounter, hhonest,
                hfinalInvariant⟩
          · exact Or.inl ⟨rfl, hfinalInvariant⟩
          · subst result
            have hdigestSignature : SuccessfulDigestRun f (ordinaryQueryCache finalCache)
                secretKey message signature.randomness index leaves := by
              rw [hrandomness]
              exact hdigest
            exact Or.inr ⟨signature, index, leaves, parts, rfl, hdigestSignature, hcounter,
              hhonest, hfinalInvariant⟩

theorem chainInvariant_maskedSign_of_published
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (message : Message) (allowed : Coordinate → Prop)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (result : Option Signature)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hinvariant : ChainInvariant parameter allowed state cache)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (result, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((maskedSign parameter root ftsSecret message).run cache)))
    (hpublished : ∀ signature index leaves parts,
      result = some signature →
      SuccessfulDigestRun f (ordinaryQueryCache finalCache)
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
          message signature.randomness index leaves →
      signature.counter = (fun lay => (parts lay).1) →
      HonestLayerParts f
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index parts →
      ∀ coordinate, PublishedByParts index parts coordinate → allowed coordinate) :
    ChainInvariant parameter allowed finalState finalCache := by
  rcases chainInvariant_maskedSign f parameter root table ftsSecret message allowed state
    finalState cache finalCache fuel remaining result hf htable hrealizes hinvariant hresult with
    ⟨_, hfinal⟩ | ⟨signature, index, leaves, parts, hsignature, hdigest, hcounter,
      hhonest, hfinal⟩
  · exact hfinal
  · exact hfinal.mono fun coordinate hcoordinate =>
      hcoordinate.elim id (hpublished signature index leaves parts hsignature hdigest hcounter
        hhonest coordinate)

def PublishedChainCoordinate (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (coordinate : Coordinate) : Prop :=
  ∃ (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
      (index : Index) (leaves : DigestTree → FtsLeaf) (lay : Layer) (chainIdx : ChainIndex)
      (codeword : Encoding),
    entry ∈ signingLog
      ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ SuccessfulDigestRun f cache secretKey entry.1 signature.randomness index leaves
      ∧ evalWithAnswerFn f (encode secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (evalWithAnswerFn f (layerMessage secretKey index lay))
        (signature.counter lay)) = some codeword
      ∧ coordinate = chainValueCoordinate lay (treeIndexAt index lay)
        (leafIndexAt index lay) chainIdx (codeword chainIdx)

theorem PublishedByParts.toPublishedChainCoordinate
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {parts : Layer → Counter × (ChainIndex → Digit)} {coordinate : Coordinate}
    (entry : (request : SignRequest) × SigningSpec.Range request)
    (signature : Signature) (leaves : DigestTree → FtsLeaf)
    (hentry : entry ∈ signingLog) (hresponse : entry.2 = some signature)
    (hrun : SuccessfulSignRun f cache secretKey entry.1 signature)
    (hdigest : SuccessfulDigestRun f cache secretKey entry.1 signature.randomness index leaves)
    (hcounter : signature.counter = fun lay => (parts lay).1)
    (hhonest : HonestLayerParts f secretKey index parts)
    (hpublished : PublishedByParts index parts coordinate) :
    PublishedChainCoordinate f cache secretKey signingLog coordinate := by
  obtain ⟨lay, chainIdx, hcoordinate⟩ := hpublished
  have hcounterAt := congrFun hcounter lay
  have hencode := hhonest lay
  rw [← hcounterAt] at hencode
  exact ⟨entry, signature, index, leaves, lay, chainIdx, (parts lay).2, hentry, hresponse,
    hrun, hdigest, hencode, hcoordinate⟩

theorem successfulDigestRun_mono_cache
    {f : QueryImpl HashSpec Id} {initial final : QueryCache HashSpec}
    {secretKey : SecretKey} {message : Message} {randomness : Randomness}
    {index : Index} {leaves : DigestTree → FtsLeaf}
    (hrun : SuccessfulDigestRun f initial secretKey message randomness index leaves)
    (hle : initial ≤ final) :
    SuccessfulDigestRun f final secretKey message randomness index leaves :=
  ⟨hrun.1, hrun.2.1, hrun.2.2.mono hle⟩

theorem successfulSignRun_mono_cache
    {f : QueryImpl HashSpec Id} {initial final : QueryCache HashSpec}
    {secretKey : SecretKey} {message : Message} {signature : Signature}
    (hrun : SuccessfulSignRun f initial secretKey message signature)
    (hle : initial ≤ final) : SuccessfulSignRun f final secretKey message signature := by
  obtain ⟨index, leaves, parts, hdigest, hftsSecret, hftsPath, hcounter, hvalues,
    hauthPath, hftsCached, hlayers, hlayersCached⟩ := hrun
  exact ⟨index, leaves, parts, successfulDigestRun_mono_cache hdigest hle, hftsSecret,
    hftsPath, hcounter, hvalues, hauthPath, hftsCached.mono hle, hlayers,
    fun lay => (hlayersCached lay).mono hle⟩

def CoveredChainCoordinate (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (coordinate : Coordinate) : Prop :=
  ∃ (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
      (index : Index) (leaves : DigestTree → FtsLeaf) (lay : Layer) (chainIdx : ChainIndex)
      (codeword : Encoding) (targetDigit : Digit),
    entry ∈ signingLog
      ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ SuccessfulDigestRun f cache secretKey entry.1 signature.randomness index leaves
      ∧ evalWithAnswerFn f (encode secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (evalWithAnswerFn f (layerMessage secretKey index lay))
        (signature.counter lay)) = some codeword
      ∧ (codeword chainIdx).val ≤ targetDigit.val
      ∧ coordinate = chainValueCoordinate lay (treeIndexAt index lay)
        (leafIndexAt index lay) chainIdx targetDigit

theorem CoveredChainCoordinate.mono_cache
    {f : QueryImpl HashSpec Id} {initial final : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {coordinate : Coordinate}
    (hcovered : CoveredChainCoordinate f initial secretKey signingLog coordinate)
    (hle : initial ≤ final) : CoveredChainCoordinate f final secretKey signingLog coordinate := by
  obtain ⟨entry, signature, index, leaves, lay, chainIdx, codeword, targetDigit, hentry,
    hresponse, hrun, hdigest, hencode, hleDigit, hcoordinate⟩ := hcovered
  exact ⟨entry, signature, index, leaves, lay, chainIdx, codeword, targetDigit, hentry,
    hresponse, successfulSignRun_mono_cache hrun hle,
    successfulDigestRun_mono_cache hdigest hle, hencode, hleDigit, hcoordinate⟩

theorem CoveredChainCoordinate.mono_log
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {left right : QueryLog SigningSpec} {coordinate : Coordinate}
    (hcovered : CoveredChainCoordinate f cache secretKey right coordinate) :
    CoveredChainCoordinate f cache secretKey (left ++ right) coordinate := by
  obtain ⟨entry, signature, index, leaves, lay, chainIdx, codeword, targetDigit, hentry,
    hresponse, hrun, hdigest, hencode, hleDigit, hcoordinate⟩ := hcovered
  exact ⟨entry, signature, index, leaves, lay, chainIdx, codeword, targetDigit,
    List.mem_append_right left hentry, hresponse, hrun, hdigest, hencode, hleDigit, hcoordinate⟩

theorem PublishedChainCoordinate.covered
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {coordinate : Coordinate}
    (hpublished : PublishedChainCoordinate f cache secretKey signingLog coordinate) :
    CoveredChainCoordinate f cache secretKey signingLog coordinate := by
  obtain ⟨entry, signature, index, leaves, lay, chainIdx, codeword, hentry, hresponse,
    hrun, hdigest, hencode, hcoordinate⟩ := hpublished
  exact ⟨entry, signature, index, leaves, lay, chainIdx, codeword, codeword chainIdx,
    hentry, hresponse, hrun, hdigest, hencode, le_rfl, hcoordinate⟩

theorem chainInvariant_maskedSign_covered
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (message : Message) (targetCache : QueryCache HashSpec)
    (signingLog : QueryLog SigningSpec)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (result : Option Signature)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hinvariant : ChainInvariant parameter
      (CoveredChainCoordinate f targetCache
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
      state cache)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (result, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((maskedSign parameter root ftsSecret message).run cache)))
    (hentry : (⟨message, result⟩ : (request : SignRequest) × SigningSpec.Range request) ∈
      signingLog)
    (hrun : ∀ signature, result = some signature →
      SuccessfulSignRun f targetCache
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
          message signature) :
    ChainInvariant parameter
      (CoveredChainCoordinate f targetCache
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
      finalState finalCache := by
  apply chainInvariant_maskedSign_of_published f parameter root table ftsSecret message
    (CoveredChainCoordinate f targetCache
      (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
    state finalState cache finalCache fuel remaining result hf htable hrealizes hinvariant hresult
  intro signature index leaves parts hsignature hdigest hcounter hhonest coordinate hpublished
  have hrun' := hrun signature hsignature
  obtain ⟨runIndex, runLeaves, runParts, hrunDigest, hftsSecret, hftsPath, hrunCounter,
    hrunValues, hrunPath, hftsCached, hlayers, hlayersCached⟩ := hrun'
  have hselected : (index, leaves) = (runIndex, runLeaves) :=
    Option.some.inj (hdigest.2.1.symm.trans hrunDigest.2.1)
  obtain ⟨hindex, hleaves⟩ := Prod.mk.inj hselected
  subst runIndex
  subst runLeaves
  exact (hpublished.toPublishedChainCoordinate ⟨message, result⟩ signature leaves hentry
    hsignature (hrun signature hsignature) hrunDigest hcounter hhonest).covered

theorem CoveredChainCoordinate.forward
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {lay : Layer} {tree : TreeIndex}
    {leafIdx : LeafIndex} {chainIdx : ChainIndex} {digit later : Digit}
    (hcovered : CoveredChainCoordinate f cache secretKey signingLog
      (chainValueCoordinate lay tree leafIdx chainIdx digit))
    (hle : digit.val ≤ later.val) :
    CoveredChainCoordinate f cache secretKey signingLog
      (chainValueCoordinate lay tree leafIdx chainIdx later) := by
  obtain ⟨entry, signature, index, leaves, publishedLay, publishedChain, codeword,
    targetDigit, hentry, hresponse, hrun, hdigest, hencode, hpublishedLe,
    hcoordinate⟩ := hcovered
  have hparts := chainValueCoordinate_injective hcoordinate
  obtain ⟨rfl, htree, hleaf, rfl, hdigit⟩ := hparts
  subst targetDigit
  exact ⟨entry, signature, index, leaves, lay, chainIdx, codeword, later, hentry, hresponse,
    hrun, hdigest, hencode, hpublishedLe.trans hle, by rw [htree, hleaf]⟩

theorem CoveredChainCoordinate.outputCoordinate
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {probe : Probe}
    (hcovered : CoveredChainCoordinate f cache secretKey signingLog probe.coordinate)
    (hchain : IsChainCoordinate probe.outputCoordinate) :
    CoveredChainCoordinate f cache secretKey signingLog probe.outputCoordinate := by
  rcases probe with ⟨coordinate, candidate⟩
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      let digit : Digit := ⟨0, by norm_num [chainLength, winternitzBits]⟩
      let later : Digit := ⟨1, by norm_num [chainLength, winternitzBits]⟩
      have hstart : chainValueCoordinate lay tree leafIdx chainIdx digit =
          .chainStart lay tree leafIdx chainIdx := by
        simp [chainValueCoordinate, digit]
      have hnext : chainValueCoordinate lay tree leafIdx chainIdx later =
          .position (.chain lay tree leafIdx chainIdx
            ⟨0, by norm_num [chainLength, winternitzBits]⟩) := by
        simp [chainValueCoordinate, later]
      change CoveredChainCoordinate f cache secretKey signingLog
        (.chainStart lay tree leafIdx chainIdx) at hcovered
      rw [← hstart] at hcovered
      have hforward := CoveredChainCoordinate.forward (digit := digit) (later := later)
        hcovered (by norm_num [digit, later])
      change CoveredChainCoordinate f cache secretKey signingLog
        (.position (.chain lay tree leafIdx chainIdx
          ⟨0, by norm_num [chainLength, winternitzBits]⟩))
      rw [← hnext]
      exact hforward
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hnext : step.val + 1 < chainLength - 1
          · let digit : Digit := ⟨step.val + 1, by
                have := step.isLt
                omega⟩
            let later : Digit := ⟨step.val + 2, by omega⟩
            have hcurrent : chainValueCoordinate lay tree leafIdx chainIdx digit =
                .position (.chain lay tree leafIdx chainIdx step) := by
              unfold chainValueCoordinate
              rw [dif_neg (by simp [digit])]
              congr 3
            have houtput : chainValueCoordinate lay tree leafIdx chainIdx later =
                .position (.chain lay tree leafIdx chainIdx
                  ⟨step.val + 1, hnext⟩) := by
              unfold chainValueCoordinate
              rw [dif_neg (by simp [later])]
              congr 3
            change CoveredChainCoordinate f cache secretKey signingLog
              (.position (.chain lay tree leafIdx chainIdx step)) at hcovered
            rw [← hcurrent] at hcovered
            have hforward := CoveredChainCoordinate.forward (digit := digit) (later := later)
              hcovered (by norm_num [digit, later])
            change CoveredChainCoordinate f cache secretKey signingLog
              (if _hnext : step.val + 1 < chainLength - 1 then
                .position (.chain lay tree leafIdx chainIdx ⟨step.val + 1, _hnext⟩)
              else .position (.leaf lay tree leafIdx))
            rw [dif_pos hnext, ← houtput]
            exact hforward
          · simp [Probe.outputCoordinate, hnext, IsChainCoordinate] at hchain
      | leaf => simp [Probe.outputCoordinate, IsChainCoordinate] at hchain
      | node => simp [Probe.outputCoordinate, IsChainCoordinate] at hchain
      | ftsLeaf => simp [Probe.outputCoordinate, IsChainCoordinate] at hchain
      | ftsNode => simp [Probe.outputCoordinate, IsChainCoordinate] at hchain
      | ftsRoots => simp [Probe.outputCoordinate, IsChainCoordinate] at hchain

theorem coveredChainCoordinate_forwardClosed
    (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (signingLog : QueryLog SigningSpec) :
    ChainForwardClosed (CoveredChainCoordinate f cache secretKey signingLog) := by
  intro candidate hcovered hchain
  exact hcovered.outputCoordinate hchain

theorem PublishedChainCoordinate.signedLayerAt
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {coordinate : Coordinate}
    (hpublished : PublishedChainCoordinate f cache secretKey signingLog coordinate) :
    ∃ lay tree leafIdx, SignedLayerAt f cache secretKey signingLog lay tree leafIdx := by
  obtain ⟨entry, signature, index, leaves, lay, chainIdx, codeword, hentry, hresponse,
    hrun, hdigest, hencode, hcoordinate⟩ := hpublished
  obtain ⟨hmessage, hopening⟩ := hrun.honest_layer_at_of_digest hdigest lay
  have hcached := hrun.signed_encode_cached_of_digest hdigest lay
  exact ⟨lay, treeIndexAt index lay, leafIndexAt index lay, entry, signature, index, leaves,
    hentry, hresponse, hrun, hdigest, rfl, rfl, hmessage, hcached, hopening⟩

theorem ForgedFreshLayerOpening.exists_uncovered_matching_probe
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index} {signature : Signature}
    (hfresh : ForgedFreshLayerOpening f cache secretKey signingLog index signature) :
    ∃ (probe : Probe) (input : HashInput),
      probe.Hits f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        ∧ probe.MatchesInput secretKey.parameter input
        ∧ cache input ≠ none
        ∧ ¬CoveredChainCoordinate f cache secretKey signingLog probe.coordinate := by
  obtain ⟨valueProbe, input, hhit, hnotSigned, hmatch, hcached⟩ :=
    hfresh.toFreshLayerOpening.exists_hit_probe_cached
  refine ⟨toProbe valueProbe, input, toProbe_hits hhit,
    toProbe_matchesInput secretKey.parameter valueProbe input hmatch, hcached, ?_⟩
  intro hcovered
  obtain ⟨entry, publishedSignature, publishedIndex, leaves, publishedLay, chainIdx,
    codeword, targetDigit, hentry, hresponse, hrun, hdigest, hencode, hle,
    hcoordinate⟩ := hcovered
  obtain ⟨hmessage, hopening⟩ := hrun.honest_layer_at_of_digest hdigest publishedLay
  have hcachedEncode := hrun.signed_encode_cached_of_digest hdigest publishedLay
  have hsigned : SignedLayerAt f cache secretKey signingLog publishedLay
      (treeIndexAt publishedIndex publishedLay) (leafIndexAt publishedIndex publishedLay) :=
    ⟨entry, publishedSignature, publishedIndex, leaves, hentry, hresponse, hrun, hdigest,
      rfl, rfl, hmessage, hcachedEncode, hopening⟩
  have hparts := chainValueCoordinate_injective
    (hcoordinate.symm.trans (toProbe_coordinate valueProbe))
  exact hnotSigned (hparts.1 ▸ hparts.2.1 ▸ hparts.2.2.1 ▸ hsigned)

theorem ForgedBackwardChainOpening.exists_uncovered_matching_probe
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {forgedIndex : Index}
    {forgedSignature : Signature}
    (hbackward : ForgedBackwardChainOpening f cache secretKey signingLog forgedIndex
      forgedSignature) :
    ∃ (probe : Probe) (input : HashInput),
      probe.Hits f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        ∧ probe.MatchesInput secretKey.parameter input
        ∧ cache input ≠ none
        ∧ ¬CoveredChainCoordinate f cache secretKey signingLog probe.coordinate := by
  obtain ⟨lay, forgedMessage, entry, signedSignature, signedIndex, leaves, signedCodeword,
    forgedCodeword, hforgedOpening, hforgedRun, hentry, hresponse, hsignRun, hdigest,
    htree, hleaf, hmessage, hsignedOpening, hsignedCached, hsigned, hforged,
    chainIdx, hlt⟩ := hbackward
  obtain ⟨openingCodeword, hopeningEncode, hforgedValues, hpath⟩ := hforgedOpening
  have hopeningCodeword : openingCodeword = forgedCodeword :=
    Option.some.inj (hopeningEncode.symm.trans hforged)
  let valueProbe : OtsValueProbe :=
    ⟨lay, treeIndexAt forgedIndex lay, leafIndexAt forgedIndex lay, chainIdx,
      forgedCodeword chainIdx, forgedSignature.chainValue lay chainIdx⟩
  have hhit : valueProbe.Hits f secretKey.parameter secretKey.otsSecret := by
    simpa only [OtsValueProbe.Hits, OtsValueProbe.target, valueProbe,
      hopeningCodeword] using hforgedValues chainIdx
  have hdigit : (forgedCodeword chainIdx).val < chainLength - 1 := by
    have hsignedLt := (signedCodeword chainIdx).isLt
    omega
  have hopeningDigit : (openingCodeword chainIdx).val < chainLength - 1 := by
    rw [hopeningCodeword]
    exact hdigit
  let step : ChainStep := ⟨(openingCodeword chainIdx).val, hopeningDigit⟩
  let input := tweakableHashInput secretKey.parameter
    (.chain lay (treeIndexAt forgedIndex lay) (leafIndexAt forgedIndex lay) chainIdx step)
    (digestBytes (forgedSignature.chainValue lay chainIdx))
  have hquery : input ∈ queriedInputs f
      (otsLeaf secretKey.parameter lay (treeIndexAt forgedIndex lay)
        (leafIndexAt forgedIndex lay) forgedMessage (forgedSignature.counter lay)
        (forgedSignature.chainValue lay)) := by
    simpa only [input, step, Nat.add_zero, walkValue, chainWalk,
      evalWithAnswerFn_pure] using
      otsLeaf_chain_query_mem f secretKey.parameter lay (treeIndexAt forgedIndex lay)
        (leafIndexAt forgedIndex lay) forgedMessage (forgedSignature.counter lay)
        (forgedSignature.chainValue lay) openingCodeword hopeningEncode chainIdx 0
        (by omega) hopeningDigit
  have hmatch : (toProbe valueProbe).MatchesInput secretKey.parameter input := by
    apply toProbe_matchesInput secretKey.parameter valueProbe input
    exact Or.inl ⟨step, by simp [valueProbe, step, hopeningCodeword], rfl⟩
  refine ⟨toProbe valueProbe, input, toProbe_hits hhit, hmatch, hforgedRun input hquery, ?_⟩
  intro hcovered
  obtain ⟨publishedEntry, publishedSignature, publishedIndex, publishedLeaves, publishedLay,
    publishedChain, publishedCodeword, targetDigit, hpublishedEntry, hpublishedResponse,
    hpublishedRun, hpublishedDigest, hpublishedEncode, hcoveredDigit, hcoordinate⟩ := hcovered
  have hparts := chainValueCoordinate_injective
    (hcoordinate.symm.trans (toProbe_coordinate valueProbe))
  dsimp only [valueProbe] at hparts
  obtain ⟨hlay, htreePublished, hleafPublished, hchainPublished, htargetDigit⟩ := hparts
  subst publishedLay
  have htreeSame : treeIndexAt publishedIndex lay = treeIndexAt signedIndex lay :=
    htreePublished.trans htree.symm
  have hleafSame : leafIndexAt publishedIndex lay = leafIndexAt signedIndex lay :=
    hleafPublished.trans hleaf.symm
  have hpartsSame := successfulSignRun_layer_ots_eq_of_position_eq hpublishedRun hsignRun
    hpublishedDigest hdigest lay htreeSame hleafSame
  have hlayerMessage := congrArg (evalWithAnswerFn f)
    (layerMessage_eq_of_position_eq secretKey publishedIndex signedIndex lay
      htreeSame hleafSame)
  have hpublishedEncode' := hpublishedEncode
  rw [htreePublished, hleafPublished, hlayerMessage, hpartsSame.1] at hpublishedEncode'
  have hcodeword : publishedCodeword = signedCodeword :=
    Option.some.inj (hpublishedEncode'.symm.trans hsigned)
  subst publishedChain
  rw [hcodeword] at hcoveredDigit
  have hdigitValue := congrArg Fin.val htargetDigit
  omega

theorem signingTraceComputation_query_bind
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input →
      OracleComp (OracleWorld + SigningSpec) alpha) :
    signingTraceComputation
        ((liftM ((OracleWorld + SigningSpec).query input) :
          OracleComp (OracleWorld + SigningSpec) _) >>= next) = (do
      let output ← liftM ((OracleWorld + SigningSpec).query input)
      (fun result => (result.1, signingLogFragment input output ++ result.2)) <$>
        signingTraceComputation (next output)) := by
  simp [signingTraceComputation]

theorem chainInvariant_maskedExpandedAdversaryQuery
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (targetCache : QueryCache HashSpec) (allowedLog : QueryLog SigningSpec)
    (hlogRuns : ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ allowedLog → entry.2 = some signature →
        SuccessfulSignRun f targetCache
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
            entry.1 signature) :
    ∀ (input : (OracleWorld + SigningSpec).Domain)
      (state finalState : LazyRevealProbe.State Coordinate)
      (cache finalCache : SplitHashCache) (fuel remaining : Nat)
      (output : (OracleWorld + SigningSpec).Range input),
      StableCacheAgreesWithFn parameter finalCache f →
      (∀ coordinate cached, finalState.values coordinate = some cached →
        cached = table coordinate) →
      (∀ position : Position, IsOtsPosition position →
        f (tableInput parameter table (.position position)) = table (.position position)) →
      ChainInvariant parameter
        (CoveredChainCoordinate f targetCache
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) allowedLog)
        state cache →
      (∀ entry, entry ∈ signingLogFragment input output → entry ∈ allowedLog) →
      LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈ support
        (LazyRevealProbe.runRaw state fuel
          ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run cache)) →
      ChainInvariant parameter
        (CoveredChainCoordinate f targetCache
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) allowedLog)
        finalState finalCache := by
  intro input
  cases input with
  | inl oracleQuery =>
      intro state finalState cache finalCache fuel remaining output hf htable hrealizes
        hinvariant hfragment hresult
      change LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
        (support (LazyRevealProbe.runRaw state fuel
          ((probingRomImpl parameter oracleQuery).run cache)) :
            Set (LazyRevealProbe.RawResult Coordinate
              (OracleWorld.Range oracleQuery × SplitHashCache))) at hresult
      exact (preservesChainInvariantImpl_probingRomImpl
        (CoveredChainCoordinate f targetCache
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) allowedLog)
        (coveredChainCoordinate_forwardClosed f targetCache
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) allowedLog)
        parameter oracleQuery) state cache fuel finalState remaining output finalCache hinvariant
          hresult
  | inr message =>
      intro state finalState cache finalCache fuel remaining output hf htable hrealizes
        hinvariant hfragment hresult
      change LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
        (support (LazyRevealProbe.runRaw state fuel
          ((maskedSign parameter root ftsSecret message).run cache)) :
            Set (LazyRevealProbe.RawResult Coordinate
              (SigningSpec.Range message × SplitHashCache))) at hresult
      apply chainInvariant_maskedSign_covered f parameter root table ftsSecret message targetCache
        allowedLog state finalState cache finalCache fuel remaining output hf htable hrealizes
          hinvariant
      · exact hresult
      · exact hfragment ⟨message, output⟩ (by simp [signingLogFragment])
      · intro signature hsignature
        exact hlogRuns ⟨message, output⟩ signature
          (hfragment _ (by simp [signingLogFragment])) hsignature

theorem chainInvariant_signingTraceComputation
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (targetCache : QueryCache HashSpec) (allowedLog signingLog : QueryLog SigningSpec)
    (hlogRuns : ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ allowedLog → entry.2 = some signature →
        SuccessfulSignRun f targetCache
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
            entry.1 signature)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (value : alpha)
    (hsub : ∀ entry, entry ∈ signingLog → entry ∈ allowedLog)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hinvariant : ChainInvariant parameter
      (CoveredChainCoordinate f targetCache
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) allowedLog)
      state cache)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        ((value, signingLog), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
          (signingTraceComputation computation)).run cache))) :
    ChainInvariant parameter
      (CoveredChainCoordinate f targetCache
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) allowedLog)
      finalState finalCache := by
  induction computation using OracleComp.inductionOn generalizing signingLog state cache fuel with
  | pure result =>
      simp [signingTraceComputation, LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, hvalue, rfl⟩
      exact hinvariant
  | query_bind input next ih =>
      rw [signingTraceComputation_query_bind, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
      obtain ⟨queryRaw, hquery, hrest⟩ := hresult
      cases queryRaw with
      | stopped hit => simp at hrest
      | done queryState queryRemaining queryResult =>
          rcases queryResult with ⟨output, queryCache⟩
          simp only at hrest
          rw [map_eq_bind_pure_comp, simulateQ_bind, StateT.run_bind,
            LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
          obtain ⟨tailRaw, htail, hfinish⟩ := hrest
          cases tailRaw with
          | stopped hit => simp at hfinish
          | done tailState tailRemaining tailResult =>
              rcases tailResult with ⟨⟨tailValue, tailLog⟩, tailCache⟩
              simp [LazyRevealProbe.runRaw] at hfinish
              rcases hfinish with ⟨rfl, rfl, houtputs, rfl⟩
              rcases houtputs with ⟨rfl, rfl⟩
              have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
                  (signingTraceComputation (next output))).run queryCache)
                    queryState finalState queryRemaining remaining
                      ((value, tailLog), finalCache) htail
              have htableQuery : ∀ coordinate cached,
                  queryState.values coordinate = some cached → cached = table coordinate :=
                fun coordinate cached hcached =>
                  htable coordinate cached (hvaluesLE coordinate cached hcached)
              have hfQuery : StableCacheAgreesWithFn parameter queryCache f :=
                StableCacheAgreesWithFn.of_run
                  (fun stableInput hstable =>
                    (ordinaryEntryPreservingImpl_maskedExpandedAdversaryImpl parameter root
                      ftsSecret stableInput hstable).simulateQ
                        (signingTraceComputation (next output)))
                  queryState finalState queryCache finalCache queryRemaining remaining
                    (value, tailLog) hf htail
              have hqueryInvariant := chainInvariant_maskedExpandedAdversaryQuery f parameter
                root table ftsSecret targetCache allowedLog hlogRuns input state queryState cache
                  queryCache fuel queryRemaining output hfQuery htableQuery hrealizes hinvariant
                    (fun entry hentry => hsub entry
                      (List.mem_append_left tailLog hentry)) hquery
              apply ih output tailLog queryState queryCache queryRemaining
              · intro entry hentry
                exact hsub entry (List.mem_append_right _ hentry)
              · exact hqueryInvariant
              · exact htail

theorem chainInvariant_retainedGameRestComputation
    (adversary : Adversary) (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (targetCache : QueryCache HashSpec)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (forgery : Forgery) (signingLog : QueryLog SigningSpec) (verified : Bool)
    (hlogRuns : ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ signingLog → entry.2 = some signature →
        SuccessfulSignRun f targetCache
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
            entry.1 signature)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hinvariant : ChainInvariant parameter
      (CoveredChainCoordinate f targetCache
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
      state cache)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (((forgery, signingLog), verified), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
          (retainedGameRestComputation adversary ⟨root, parameter⟩)).run cache))) :
    ChainInvariant parameter
      (CoveredChainCoordinate f targetCache
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
      finalState finalCache := by
  rw [simulateQ_maskedExpanded_retainedGameRestComputation, StateT.run_bind,
    LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨prefixRaw, hprefix, hrest⟩ := hresult
  cases prefixRaw with
  | stopped hit => simp at hrest
  | done prefixState prefixRemaining prefixResult =>
      rcases prefixResult with ⟨⟨prefixForgery, prefixLog⟩, prefixCache⟩
      simp only at hrest
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
      obtain ⟨verifyRaw, hverify, hfinish⟩ := hrest
      cases verifyRaw with
      | stopped hit => simp at hfinish
      | done verifyState verifyRemaining verifyResult =>
          rcases verifyResult with ⟨prefixVerified, verifyCache⟩
          simp [LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨rfl, rfl, houtputs, rfl⟩
          rcases houtputs with ⟨hprefixOutput, rfl⟩
          rcases hprefixOutput with ⟨rfl, rfl⟩
          have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
            ((simulateQ (probingRomImpl parameter)
              (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run
                prefixCache) prefixState finalState prefixRemaining remaining
                  (verified, finalCache) hverify
          have htablePrefix : ∀ coordinate output,
              prefixState.values coordinate = some output → output = table coordinate :=
            fun coordinate output hcached =>
              htable coordinate output (hvaluesLE coordinate output hcached)
          have hfPrefix : StableCacheAgreesWithFn parameter prefixCache f :=
            StableCacheAgreesWithFn.of_run
              (fun input hstable =>
                (ordinaryEntryPreservingImpl_probingRomImpl parameter input hstable).simulateQ
                  (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature))
              prefixState finalState prefixCache finalCache prefixRemaining remaining verified hf
                hverify
          have hprefixInvariant := chainInvariant_signingTraceComputation f parameter root table
            ftsSecret targetCache signingLog signingLog hlogRuns
              (adversary.main ⟨root, parameter⟩) state prefixState cache prefixCache fuel
                prefixRemaining forgery (fun entry => id) hfPrefix htablePrefix hrealizes
                  hinvariant hprefix
          exact (preservesChainInvariantImpl_probingRomImpl
            (CoveredChainCoordinate f targetCache
              (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
            (coveredChainCoordinate_forwardClosed f targetCache
              (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
            parameter).simulateQ
              (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)
                prefixState prefixCache prefixRemaining finalState remaining verified finalCache
                  hprefixInvariant hverify

theorem preservesChainInvariant_publishCoordinate_of_not_chain
    (parameter : PublicParameter) (allowed : Coordinate → Prop) (coordinate : Coordinate)
    (hnotChain : ¬IsChainCoordinate coordinate) :
    PreservesChainInvariant parameter allowed (publishCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hinvariant hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.publishQuery coordinate >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.publishQuery, LazyRevealProbe.runRaw_publish_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨?_, hinvariant.2.publish coordinate⟩
  intro other hchain
  have hne : other ≠ coordinate := by
    intro heq
    exact hnotChain (heq ▸ hchain)
  simpa [LazyRevealProbe.State.publish, hne] using hinvariant.1 other hchain

theorem finalizeDetailedFrom_preserves_value
    (coordinates : List Coordinate) :
    ∀ (state finalState : LazyRevealProbe.State Coordinate) (coordinate : Coordinate)
      (output : HashOutput), state.values coordinate = some output →
      (false, finalState) ∈ support
        (LazyRevealProbe.finalizeDetailedFrom coordinates state) →
      finalState.values coordinate = some output := by
  induction coordinates with
  | nil =>
      intro state finalState coordinate output hvalue hresult
      simp [LazyRevealProbe.finalizeDetailedFrom] at hresult
      subst finalState
      exact hvalue
  | cons current remaining ih =>
      intro state finalState coordinate output hvalue hresult
      rw [LazyRevealProbe.finalizeDetailedFrom] at hresult
      cases hcurrent : state.values current with
      | some currentOutput =>
          rw [hcurrent] at hresult
          apply ih (state.clearPending current) finalState coordinate output
          · exact hvalue
          · exact hresult
      | none =>
          rw [hcurrent, mem_support_bind_iff] at hresult
          obtain ⟨sampled, _, hrest⟩ := hresult
          by_cases hhit : state.hitAt current sampled
          · rw [if_pos hhit] at hrest
            simp at hrest
          · rw [if_neg hhit] at hrest
            apply ih (state.complete current sampled) finalState coordinate output
            · have hne : coordinate ≠ current := by
                intro heq
                subst current
                rw [hcurrent] at hvalue
                simp at hvalue
              simpa [LazyRevealProbe.State.complete, Function.update, hne] using hvalue
            · exact hrest

theorem finalizeDetailedFrom_false_of_pending_hit
    (table : Coordinate → HashOutput) :
    ∀ (coordinates : List Coordinate) (state finalState : LazyRevealProbe.State Coordinate)
      (coordinate : Coordinate), coordinate ∈ coordinates →
      state.values coordinate = none → state.hitAt coordinate (table coordinate) →
      (∀ output, finalState.values coordinate = some output → output = table coordinate) →
      (false, finalState) ∈ support
        (LazyRevealProbe.finalizeDetailedFrom coordinates state) → False := by
  intro coordinates
  induction coordinates with
  | nil =>
      intro state finalState coordinate hmem
      simp at hmem
  | cons current remaining ih =>
      intro state finalState coordinate hmem hvalue hhit htable hresult
      rw [LazyRevealProbe.finalizeDetailedFrom] at hresult
      by_cases heq : current = coordinate
      · subst current
        rw [hvalue, mem_support_bind_iff] at hresult
        obtain ⟨sampled, _, hrest⟩ := hresult
        by_cases hsampledHit : state.hitAt coordinate sampled
        · rw [if_pos hsampledHit] at hrest
          simp at hrest
        · rw [if_neg hsampledHit] at hrest
          have hcompleted : (state.complete coordinate sampled).values coordinate =
              some sampled := by
            simp [LazyRevealProbe.State.complete]
          have hfinalValue := finalizeDetailedFrom_preserves_value remaining
            (state.complete coordinate sampled) finalState coordinate sampled hcompleted hrest
          have hsampled := htable sampled hfinalValue
          subst sampled
          exact hsampledHit hhit
      · have htailMem : coordinate ∈ remaining := by
          simp only [List.mem_cons] at hmem
          rcases hmem with hcurrentEq | htail
          · exact (heq hcurrentEq.symm).elim
          · exact htail
        have hne : coordinate ≠ current := fun hcoordinate => heq hcoordinate.symm
        have hpending : (coordinate, truncateHash (table coordinate)) ∈ state.pending := by
          simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] using hhit
        cases hcurrent : state.values current with
        | some currentOutput =>
            rw [hcurrent] at hresult
            apply ih (state.clearPending current) finalState coordinate htailMem
            · exact hvalue
            · simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt,
                LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway,
                hne] using And.intro hpending hne
            · exact htable
            · exact hresult
        | none =>
            rw [hcurrent, mem_support_bind_iff] at hresult
            obtain ⟨sampled, _, hrest⟩ := hresult
            by_cases hsampledHit : state.hitAt current sampled
            · rw [if_pos hsampledHit] at hrest
              simp at hrest
            · rw [if_neg hsampledHit] at hrest
              apply ih (state.complete current sampled) finalState coordinate htailMem
              · simp [LazyRevealProbe.State.complete, Function.update, hne, hvalue]
              · simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt,
                  LazyRevealProbe.State.complete, LazyRevealProbe.State.pendingAway,
                  hne] using And.intro hpending hne
              · exact htable
              · exact hrest

theorem finalizeDetailed_false_of_pending_hit
    (table : Coordinate → HashOutput) (state finalState : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (hvalue : state.values coordinate = none)
    (hhit : state.hitAt coordinate (table coordinate))
    (htable : ∀ output, finalState.values coordinate = some output →
      output = table coordinate)
    (hresult : (false, finalState) ∈ support
      (LazyRevealProbe.finalizeDetailed state)) : False := by
  apply finalizeDetailedFrom_false_of_pending_hit table state.coordinates.toList state finalState
    coordinate
  · have hpending : ∃ candidate, (coordinate, candidate) ∈ state.pending := by
      rw [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] at hhit
      simp only [Finset.mem_image, Finset.mem_filter] at hhit
      obtain ⟨entry, ⟨hentry, hcoordinate⟩, _⟩ := hhit
      exact ⟨entry.2, hcoordinate ▸ hentry⟩
    simp [LazyRevealProbe.State.coordinates, hpending]
  · exact hvalue
  · exact hhit
  · exact htable
  · exact hresult

theorem ChainInvariant.not_finalized_false_of_uncovered_probe
    {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
    {table : Coordinate → HashOutput}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {allowed : Coordinate → Prop} {state finalState : LazyRevealProbe.State Coordinate}
    {cache : SplitHashCache} (hinvariant : ChainInvariant parameter allowed state cache)
    (probe : Probe) (input : HashInput)
    (hhits : probe.Hits f parameter (tableOtsSecret table) ftsSecret)
    (hmatches : probe.MatchesInput parameter input)
    (hcached : cache (.ordinary input) ≠ none) (hnotAllowed : ¬allowed probe.coordinate)
    (htable : ∀ output, finalState.values probe.coordinate = some output →
      output = table probe.coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hfinalize : (false, finalState) ∈ support
      (LazyRevealProbe.finalizeDetailed state)) : False := by
  have hchain := probe.isChainCoordinate_of_matchesInput hmatches
  have hhit := hinvariant.2.hitAt f table ftsSecret probe input hchain hrealizes hhits hmatches
    hcached hnotAllowed
  have hvalue := hinvariant.1.value_eq_none_of_not_allowed hchain hnotAllowed
  exact finalizeDetailed_false_of_pending_hit table state finalState probe.coordinate hvalue hhit
    htable hfinalize

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
theorem chainInvariant_maskedRetainedGameAfterFtsSecrets
    (adversary : Adversary) (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (targetCache : QueryCache HashSpec) (fuel remaining : Nat)
    (finalState : LazyRevealProbe.State Coordinate) (finalCache : SplitHashCache)
    (root : Digest) (forgery : Forgery) (signingLog : QueryLog SigningSpec)
    (verified : Bool)
    (hlogRuns : ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ signingLog → entry.2 = some signature →
        SuccessfulSignRun f targetCache
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
            entry.1 signature)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        ((root, ((forgery, signingLog), verified)), finalCache) ∈ support
      (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty :
          LazyRevealProbe.State Coordinate) fuel
        ((maskedRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache))) :
    ChainInvariant parameter
      (CoveredChainCoordinate f targetCache
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
      finalState finalCache := by
  let rootCoordinate : Coordinate := .position (.node topLayer rootTree
    ⟨layerHeight topLayer - 1, by norm_num [layerHeight, topLayer, maxLayerHeight]⟩ 0)
  unfold maskedRetainedGameAfterFtsSecrets at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨rootRaw, hroot, hafterRoot⟩ := hresult
  cases rootRaw with
  | stopped hit => simp at hafterRoot
  | done rootState rootRemaining rootResult =>
      rcases rootResult with ⟨sampledRoot, rootCache⟩
      change LazyRevealProbe.RawResult.done rootState rootRemaining
          (sampledRoot, rootCache) ∈ support
        (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty :
            LazyRevealProbe.State Coordinate) fuel
          ((maskedTreeRoot topLayer rootTree).run emptySplitHashCache)) at hroot
      generalize topLayer = rootLay at hroot
      generalize rootTree = rootTreeIndex at hroot
      simp only at hafterRoot
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hafterRoot
      obtain ⟨publishRaw, hpublish, hafterPublish⟩ := hafterRoot
      cases publishRaw with
      | stopped hit => simp at hafterPublish
      | done publishState publishRemaining publishResult =>
          rcases publishResult with ⟨publishedUnit, publishCache⟩
          simp only at hafterPublish
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hafterPublish
          obtain ⟨restRaw, hrest, hfinish⟩ := hafterPublish
          cases restRaw with
          | stopped hit => simp at hfinish
          | done restState restRemaining restResult =>
              rcases restResult with ⟨result, restCache⟩
              simp [LazyRevealProbe.runRaw] at hfinish
              rcases hfinish with ⟨rfl, rfl, houtput, rfl⟩
              obtain ⟨hrootEq, hresultEq⟩ := houtput
              rw [← hresultEq] at hrest
              have hlogRunsSampled :
                  ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
                    (signature : Signature), entry ∈ signingLog →
                      entry.2 = some signature →
                        SuccessfulSignRun f targetCache
                          (⟨parameter, sampledRoot, tableOtsSecret table,
                            ftsSecret⟩ : SecretKey) entry.1 signature := by
                simpa only [hrootEq] using hlogRuns
              let allowed := CoveredChainCoordinate f targetCache
                (⟨parameter, sampledRoot, tableOtsSecret table,
                  ftsSecret⟩ : SecretKey) signingLog
              have hrootInvariantEmpty := chainInvariant_maskedTreeRoot_empty
                (parameter := parameter) (allowed := fun _ => False) (lay := rootLay)
                  (tree := rootTreeIndex) fuel rootRemaining rootState sampledRoot rootCache hroot
              have hrootInvariant : ChainInvariant parameter allowed rootState rootCache :=
                hrootInvariantEmpty.mono (by simp)
              have hpublishInvariant :=
                preservesChainInvariant_publishCoordinate_of_not_chain parameter allowed
                  rootCoordinate (by simp [rootCoordinate, IsChainCoordinate])
                    (state := rootState) (cache := rootCache) (fuel := rootRemaining)
                    (finalState := publishState) (remaining := publishRemaining)
                    (value := publishedUnit) (finalCache := publishCache) hrootInvariant
                      (by simpa [rootCoordinate] using hpublish)
              have hfinal := chainInvariant_retainedGameRestComputation adversary f parameter
                sampledRoot table ftsSecret targetCache publishState finalState publishCache
                  finalCache publishRemaining remaining forgery signingLog verified
                    hlogRunsSampled hf htable hrealizes hpublishInvariant hrest
              simpa only [hrootEq] using hfinal

end SphincsSecurity.Concrete.OtsProbeSimulation
