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

theorem maskedOtsSignFrom_some_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter (state finalState : LazyRevealProbe.State Coordinate)
      (cache finalCache : SplitHashCache) (fuel remaining : Nat)
      (selectedCounter : Counter) (encoding : ChainIndex → Digit),
      (ordinaryQueryCache finalCache).AgreesWithFn f →
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
                  exact evalWithAnswerFn_eq_of_mem_runRaw_ordinaryHashImpl f
                    (encode parameter lay tree leafIdx message
                      (BitVec.ofNat counterBits counter)) state encodeState cache encodeCache fuel
                        encodeRemaining (some selectedEncoding) hf hencode

theorem maskedOtsSign_some_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (counter : Counter) (encoding : ChainIndex → Digit)
    (hf : (ordinaryQueryCache finalCache).AgreesWithFn f)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some (counter, encoding), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedOtsSign parameter lay tree leafIdx message).run cache))) :
    evalWithAnswerFn f (encode parameter lay tree leafIdx message counter) = some encoding := by
  exact maskedOtsSignFrom_some_eval f parameter lay tree leafIdx message encodingAttemptLimit 0
    state finalState cache finalCache fuel remaining counter encoding hf hresult

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

end SphincsSecurity.Concrete.OtsProbeSimulation
