import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FtsProbeOrigin
import SphincsSecurity.Proof.OneTimeEvents
import SphincsSecurity.Proof.OtsProbeRealization

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

theorem LazyRevealProbe.ValuesLE.trans
    {first second third : LazyRevealProbe.State Coordinate}
    (hleft : LazyRevealProbe.ValuesLE first second)
    (hright : LazyRevealProbe.ValuesLE second third) :
    LazyRevealProbe.ValuesLE first third := by
  intro coordinate output hvalue
  exact hright coordinate output (hleft coordinate output hvalue)

def LazyRevealProbe.EnsuredLE (initial final : LazyRevealProbe.State Coordinate) : Prop :=
  initial.ensured ⊆ final.ensured

theorem LazyRevealProbe.EnsuredLE.refl (state : LazyRevealProbe.State Coordinate) :
    LazyRevealProbe.EnsuredLE state state := by
  exact fun _ hcoordinate => hcoordinate

theorem LazyRevealProbe.EnsuredLE.trans
    {first second third : LazyRevealProbe.State Coordinate}
    (hleft : LazyRevealProbe.EnsuredLE first second)
    (hright : LazyRevealProbe.EnsuredLE second third) :
    LazyRevealProbe.EnsuredLE first third := by
  exact fun coordinate hcoordinate => hright (hleft hcoordinate)

theorem LazyRevealProbe.ensuredLE_ensure (state : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) : LazyRevealProbe.EnsuredLE state (state.ensure coordinate) := by
  intro other hother
  simp [LazyRevealProbe.State.ensure, hother]

theorem LazyRevealProbe.ensuredLE_addPending (state : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (candidate : Digest) :
    LazyRevealProbe.EnsuredLE state (state.addPending coordinate candidate) := by
  exact fun _ hcoordinate => hcoordinate

theorem LazyRevealProbe.ensuredLE_publish (state : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) : LazyRevealProbe.EnsuredLE state (state.publish coordinate) := by
  exact fun _ hcoordinate => hcoordinate

theorem LazyRevealProbe.ensuredLE_materialize (state : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (sampled : HashOutput) :
    LazyRevealProbe.EnsuredLE state (state.materialize coordinate sampled) := by
  intro other hother
  simp [LazyRevealProbe.State.materialize, hother]

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

theorem LazyRevealProbe.ensuredLE_of_mem_runRaw_done
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (state finalState : LazyRevealProbe.State Coordinate) (fuel remaining : Nat)
    (value : alpha)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining value ∈
      support (LazyRevealProbe.runRaw state fuel computation)) :
    LazyRevealProbe.EnsuredLE state finalState := by
  induction computation using OracleComp.inductionOn generalizing
      state finalState fuel remaining value with
  | pure result =>
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl⟩
      exact fun _ hcoordinate => hcoordinate
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
          exact (LazyRevealProbe.ensuredLE_ensure state coordinate).trans
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
                exact (LazyRevealProbe.ensuredLE_addPending state coordinate candidate).trans
                  (ih () (state.addPending coordinate candidate) finalState remainingFuel
                    remaining value hresult)
      | peek coordinate =>
          rw [LazyRevealProbe.runRaw_peek_query_bind] at hresult
          exact ih (state.values coordinate) state finalState fuel remaining value hresult
      | publish coordinate =>
          rw [LazyRevealProbe.runRaw_publish_query_bind] at hresult
          exact (LazyRevealProbe.ensuredLE_publish state coordinate).trans
            (ih () (state.publish coordinate) finalState fuel remaining value hresult)
      | reveal coordinate =>
          rw [LazyRevealProbe.runRaw_reveal_query_bind] at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              rw [hvalue] at hresult
              exact ih output state finalState fuel remaining value hresult
          | none =>
              rw [hvalue, mem_support_bind_iff] at hresult
              obtain ⟨output, _, htail⟩ := hresult
              by_cases hhit : state.hitAt coordinate output
              · rw [if_pos hhit] at htail
                simp at htail
              · rw [if_neg hhit] at htail
                exact (LazyRevealProbe.ensuredLE_materialize state coordinate output).trans
                  (ih output (state.materialize coordinate output) finalState fuel remaining
                    value htail)

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

def StableOrdinaryInput (parameter : PublicParameter) (input : HashInput) : Prop :=
  decodeProbe? parameter input = none ∧
    ∀ position, decodePosition? parameter input = some position → ¬IsOtsPosition position

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

theorem SplitCachePreserving.ordinaryCacheIncreasing
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    (hpreserves : SplitCachePreserving computation) :
    OrdinaryCacheIncreasing computation := by
  intro state cache fuel finalState remaining value finalCache hresult
  rw [hpreserves state cache fuel finalState remaining value finalCache hresult]

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

theorem TargetSum.Valid.exists_digit_lt_last
    {codeword : Encoding} (hvalid : TargetSum.Valid codeword) :
    ∃ chainIdx : ChainIndex, (codeword chainIdx).val < chainLength - 1 := by
  by_contra hnone
  have hall : ∀ chainIdx : ChainIndex,
      (codeword chainIdx).val = chainLength - 1 := by
    intro chainIdx
    have hge := not_lt.mp (not_exists.mp hnone chainIdx)
    have hle := (codeword chainIdx).isLt
    simp only [chainLength, winternitzBits] at hge hle ⊢
    omega
  have hsum : TargetSum.sum codeword = numChains * (chainLength - 1) := by
    unfold TargetSum.sum
    simp_rw [hall]
    simp
  rw [hvalid] at hsum
  norm_num [targetSum, numChains, chainLength, winternitzBits] at hsum

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
        ∧ LazyRevealProbe.EnsuredLE componentFinalState finalState
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
              have htailEnsured := LazyRevealProbe.ensuredLE_of_mem_runRaw_done
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
                    hhead, rfl, htailValues, htailEnsured, htailCache⟩
              | succ tailPosition =>
                  exact ih
                    (computation := fun position => computation position.succ)
                    (hincreasing := fun position => hincreasing position.succ)
                    (values := tail) (state := headState) (finalState := finalState)
                    (cache := headCache) (finalCache := finalCache) (fuel := headRemaining)
                    (remaining := remaining) htail tailPosition

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

@[irreducible] noncomputable def maskedSignLayerAt
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))
      (Option (Counter × (ChainIndex → Digit))) :=
  maskedSignLayer parameter ftsSecret index lay

@[irreducible] noncomputable def maskedSignLayers
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))
      (Layer → Option (Counter × (ChainIndex → Digit))) :=
  sequenceFin (maskedSignLayerAt parameter ftsSecret index)

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

def HonestLayerParts (f : QueryImpl HashSpec Id) (secretKey : SecretKey) (index : Index)
    (parts : Layer → Counter × (ChainIndex → Digit)) : Prop :=
  ∀ lay, evalWithAnswerFn f
    (encode secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn f (layerMessage secretKey index lay)) (parts lay).1) =
        some (parts lay).2

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

theorem VerifierLayerMessage.otsLeaf_query_mem_verifyLayers
    {f : QueryImpl HashSpec Id} {parameter : PublicParameter} {index : Index}
    {leaves : DigestTree → FtsLeaf} {signature : Signature} {lay : Layer}
    {message : Digest} {input : HashInput}
    (hmessage : VerifierLayerMessage f parameter index leaves signature lay message)
    (hquery : input ∈ queriedInputs f
      (otsLeaf parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message
        (signature.counter lay) (signature.chainValue lay))) :
    input ∈ queriedInputs f
      (verifyLayers parameter index signature numLayers
        (evalWithAnswerFn f
          (ftsRecover parameter index leaves signature.ftsSecret signature.ftsPath))) := by
  simp only [VerifierLayerMessage] at hmessage
  obtain ⟨bottomLeaf, hbottom, middleLeaf, hmiddle, hposition⟩ := hmessage
  rcases hposition with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [show numLayers = bottomLayer.val + 1 by rfl, verifyLayers_succ_eq,
      dif_pos bottomLayer.isLt]
    exact queriedInputs_mono_bind_left f _ _ hquery
  · rw [show numLayers = bottomLayer.val + 1 by rfl, verifyLayers_succ_eq,
      dif_pos bottomLayer.isLt]
    apply queriedInputs_mono_bind_right
    rw [hbottom]
    apply queriedInputs_mono_bind_right
    change input ∈ queriedInputs f
      (verifyLayers parameter index signature (middleLayer.val + 1)
        (foldValue f parameter bottomLayer (treeIndexAt index bottomLayer)
          (leafIndexAt index bottomLayer) (signaturePath signature bottomLayer) bottomLeaf
          (layerHeight bottomLayer)))
    rw [verifyLayers_succ_eq, dif_pos middleLayer.isLt]
    simp only [show (⟨middleLayer.val, by exact middleLayer.isLt⟩ : Layer) = middleLayer by
      exact Fin.ext rfl]
    exact queriedInputs_mono_bind_left f _ _ hquery
  · rw [show numLayers = bottomLayer.val + 1 by rfl, verifyLayers_succ_eq,
      dif_pos bottomLayer.isLt]
    apply queriedInputs_mono_bind_right
    rw [hbottom]
    apply queriedInputs_mono_bind_right
    change input ∈ queriedInputs f
      (verifyLayers parameter index signature (middleLayer.val + 1)
        (foldValue f parameter bottomLayer (treeIndexAt index bottomLayer)
          (leafIndexAt index bottomLayer) (signaturePath signature bottomLayer) bottomLeaf
          (layerHeight bottomLayer)))
    rw [verifyLayers_succ_eq, dif_pos middleLayer.isLt]
    simp only [show (⟨middleLayer.val, by exact middleLayer.isLt⟩ : Layer) = middleLayer by
      exact Fin.ext rfl]
    apply queriedInputs_mono_bind_right
    rw [hmiddle]
    apply queriedInputs_mono_bind_right
    change input ∈ queriedInputs f
      (verifyLayers parameter index signature (topLayer.val + 1)
        (foldValue f parameter middleLayer (treeIndexAt index middleLayer)
          (leafIndexAt index middleLayer) (signaturePath signature middleLayer) middleLeaf
          (layerHeight middleLayer)))
    rw [verifyLayers_succ_eq, dif_pos topLayer.isLt]
    simp only [show (⟨topLayer.val, by exact topLayer.isLt⟩ : Layer) = topLayer by
      exact Fin.ext rfl]
    exact queriedInputs_mono_bind_left f _ _ hquery

theorem VerifierLayerMessage.otsLeaf_query_mem_verify
    {f : QueryImpl HashSpec Id} {publicKey : PublicKey} {message : Message}
    {signature : Signature} {digest : MessageDigest} {lay : Layer}
    {layerMessage : Digest} {input : HashInput}
    (hdigest : evalWithAnswerFn f
      (messageDigest publicKey.parameter publicKey.root message signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hlayer : VerifierLayerMessage f publicKey.parameter (digestIndex digest)
      (digestLeaves digest) signature lay layerMessage)
    (hquery : input ∈ queriedInputs f
      (otsLeaf publicKey.parameter lay (treeIndexAt (digestIndex digest) lay)
        (leafIndexAt (digestIndex digest) lay) layerMessage (signature.counter lay)
        (signature.chainValue lay))) :
    input ∈ queriedInputs f (verify publicKey message signature) := by
  rw [verify_eq, queriedInputs_bind]
  apply List.mem_append_right
  rw [hdigest]
  simp only [hadmissible, not_true_eq_false, if_false, queriedInputs_bind]
  apply List.mem_append_right
  apply List.mem_append_left
  exact VerifierLayerMessage.otsLeaf_query_mem_verifyLayers hlayer hquery

def VerifyProbeWitnessAt (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec)
    (forgedMessage : Message) (signature : Signature) (lay : Layer) : Prop :=
  ∃ (digest : MessageDigest) (layerMessage : Digest)
      (codeword : Encoding) (chainIdx : ChainIndex)
      (_hdigit : (codeword chainIdx).val < chainLength - 1)
      (probe : Probe) (input : HashInput),
    input = tweakableHashInput secretKey.parameter
        (.chain lay (treeIndexAt (digestIndex digest) lay)
          (leafIndexAt (digestIndex digest) lay) chainIdx
            ⟨(codeword chainIdx).val, _hdigit⟩)
        (digestBytes (signature.chainValue lay chainIdx))
      ∧ evalWithAnswerFn f (messageDigest secretKey.parameter secretKey.root
        forgedMessage signature.randomness) = digest
      ∧ Admissible digest
      ∧ evalWithAnswerFn f (encode secretKey.parameter lay
        (treeIndexAt (digestIndex digest) lay) (leafIndexAt (digestIndex digest) lay)
          layerMessage (signature.counter lay)) = some codeword
      ∧ VerifierLayerMessage f secretKey.parameter (digestIndex digest)
        (digestLeaves digest) signature lay layerMessage
      ∧ probe.Hits f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      ∧ probe.MatchesInput secretKey.parameter input
      ∧ input ∈ queriedInputs f
        (verify ⟨secretKey.root, secretKey.parameter⟩ forgedMessage signature)
      ∧ cache input ≠ none
      ∧ ¬CoveredChainCoordinate f cache secretKey signingLog probe.coordinate
      ∧ probe.SourceSettled cache secretKey

def VerifyProbeWitness (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec)
    (forgedMessage : Message) (signature : Signature) : Prop :=
  ∃ lay, VerifyProbeWitnessAt f cache secretKey signingLog forgedMessage signature lay

theorem SettledForgedFreshLayerOpening.exists_uncovered_matching_chain_probe
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index} {leaves : DigestTree → FtsLeaf}
    {signature : Signature}
    (hfresh : SettledForgedFreshLayerOpening f cache secretKey signingLog index leaves signature) :
    ∃ (lay : Layer) (message : Digest) (codeword : Encoding)
        (chainIdx : ChainIndex) (_hdigit : (codeword chainIdx).val < chainLength - 1)
        (probe : Probe) (input : HashInput),
      input = tweakableHashInput secretKey.parameter
          (.chain lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
            ⟨(codeword chainIdx).val, _hdigit⟩)
          (digestBytes (signature.chainValue lay chainIdx))
        ∧ evalWithAnswerFn f (encode secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) message (signature.counter lay)) = some codeword
        ∧ VerifierLayerMessage f secretKey.parameter index leaves signature lay message
        ∧ input ∈ queriedInputs f
          (otsLeaf secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            message (signature.counter lay) (signature.chainValue lay))
        ∧ probe.Hits f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        ∧ probe.MatchesInput secretKey.parameter input
        ∧ cache input ≠ none
        ∧ ¬CoveredChainCoordinate f cache secretKey signingLog probe.coordinate
        ∧ probe.SourceSettled cache secretKey := by
  obtain ⟨lay, message, hroot, hverifierMessage, hopening, hforgedRun, hnotSigned⟩ := hfresh
  obtain ⟨codeword, hencode, hvalues, _⟩ := hopening
  have hvalid := valid_of_eval_encode_eq_some f secretKey.parameter lay
    (treeIndexAt index lay) (leafIndexAt index lay) message (signature.counter lay)
      codeword hencode
  obtain ⟨chainIdx, hdigit⟩ := TargetSum.Valid.exists_digit_lt_last hvalid
  let valueProbe : OtsValueProbe :=
    ⟨lay, treeIndexAt index lay, leafIndexAt index lay, chainIdx,
      codeword chainIdx, signature.chainValue lay chainIdx⟩
  let step : ChainStep := ⟨(codeword chainIdx).val, hdigit⟩
  let input := tweakableHashInput secretKey.parameter
    (.chain lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx step)
    (digestBytes (signature.chainValue lay chainIdx))
  have hquery : input ∈ queriedInputs f
      (otsLeaf secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        message (signature.counter lay) (signature.chainValue lay)) := by
    simpa only [input, step, Nat.add_zero, walkValue, chainWalk,
      evalWithAnswerFn_pure] using
      otsLeaf_chain_query_mem f secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) message (signature.counter lay) (signature.chainValue lay)
          codeword hencode chainIdx 0 (by omega) hdigit
  have hhit : valueProbe.Hits f secretKey.parameter secretKey.otsSecret := by
    simpa only [OtsValueProbe.Hits, OtsValueProbe.target, valueProbe] using hvalues chainIdx
  have hmatch : (toProbe valueProbe).MatchesInput secretKey.parameter input := by
    apply toProbe_matchesInput secretKey.parameter valueProbe input
    exact Or.inl ⟨step, by simp [valueProbe, step], rfl⟩
  refine ⟨lay, message, codeword, chainIdx, hdigit, toProbe valueProbe, input, rfl, hencode,
    hverifierMessage, hquery, toProbe_hits hhit, hmatch, hforgedRun input hquery, ?_, ?_⟩
  · intro hcovered
    obtain ⟨entry, publishedSignature, publishedIndex, publishedLeaves, publishedLay,
      publishedChainIdx, publishedCodeword, targetDigit, hentry, hresponse, hrun, hdigest,
      hpublishedEncode, hle, hcoordinate⟩ := hcovered
    obtain ⟨hmessage, hopening⟩ := hrun.honest_layer_at_of_digest hdigest publishedLay
    have hcachedEncode := hrun.signed_encode_cached_of_digest hdigest publishedLay
    have hsigned : SignedLayerAt f cache secretKey signingLog publishedLay
        (treeIndexAt publishedIndex publishedLay) (leafIndexAt publishedIndex publishedLay) :=
      ⟨entry, publishedSignature, publishedIndex, publishedLeaves, hentry, hresponse, hrun,
        hdigest, rfl, rfl, hmessage, hcachedEncode, hopening⟩
    have hparts := chainValueCoordinate_injective
      (hcoordinate.symm.trans (toProbe_coordinate valueProbe))
    dsimp only [valueProbe] at hparts
    obtain ⟨rfl, htree, hleaf, _, _⟩ := hparts
    rw [htree, hleaf] at hsigned
    exact hnotSigned hsigned
  · exact toProbe_sourceSettled_of_layerRootSettled (leafIndexAt_lt index lay) hroot

set_option maxHeartbeats 400000 in
theorem SettledForgedFreshLayerOpening.toVerifyProbeWitness
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {forgedMessage : Message} {digest : MessageDigest}
    {signature : Signature}
    (hdigest : evalWithAnswerFn f (messageDigest secretKey.parameter secretKey.root
      forgedMessage signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hfresh : SettledForgedFreshLayerOpening f cache secretKey signingLog (digestIndex digest)
      (digestLeaves digest) signature) :
    VerifyProbeWitness f cache secretKey signingLog forgedMessage signature := by
  obtain ⟨lay, message, codeword, chainIdx, hdigit, probe, input, hinput, hencode,
    hverifierMessage, hquery, hhit, hmatch, hcached, huncovered, hsettled⟩ :=
      SettledForgedFreshLayerOpening.exists_uncovered_matching_chain_probe hfresh
  exact ⟨lay, digest, message, codeword, chainIdx, hdigit, probe, input, hinput,
    hdigest, hadmissible, hencode,
    hverifierMessage, hhit, hmatch,
    VerifierLayerMessage.otsLeaf_query_mem_verify hdigest hadmissible hverifierMessage hquery,
    hcached, huncovered, hsettled⟩

theorem SettledForgedBackwardChainOpening.exists_uncovered_matching_probe
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {forgedIndex : Index}
    {forgedLeaves : DigestTree → FtsLeaf}
    {forgedSignature : Signature}
    (hbackward : SettledForgedBackwardChainOpening f cache secretKey signingLog forgedIndex
      forgedLeaves forgedSignature) :
    ∃ (lay : Layer) (forgedMessage : Digest) (codeword : Encoding)
        (chainIdx : ChainIndex) (_hdigit : (codeword chainIdx).val < chainLength - 1)
        (probe : Probe) (input : HashInput),
      input = tweakableHashInput secretKey.parameter
          (.chain lay (treeIndexAt forgedIndex lay) (leafIndexAt forgedIndex lay) chainIdx
            ⟨(codeword chainIdx).val, _hdigit⟩)
          (digestBytes (forgedSignature.chainValue lay chainIdx))
        ∧ evalWithAnswerFn f
          (encode secretKey.parameter lay (treeIndexAt forgedIndex lay)
            (leafIndexAt forgedIndex lay) forgedMessage (forgedSignature.counter lay)) =
              some codeword
        ∧ VerifierLayerMessage f secretKey.parameter forgedIndex forgedLeaves forgedSignature lay
            forgedMessage
        ∧ input ∈ queriedInputs f
          (otsLeaf secretKey.parameter lay (treeIndexAt forgedIndex lay)
            (leafIndexAt forgedIndex lay) forgedMessage (forgedSignature.counter lay)
            (forgedSignature.chainValue lay))
        ∧ probe.Hits f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        ∧ probe.MatchesInput secretKey.parameter input
        ∧ cache input ≠ none
        ∧ ¬CoveredChainCoordinate f cache secretKey signingLog probe.coordinate
        ∧ probe.SourceSettled cache secretKey := by
  obtain ⟨lay, forgedMessage, entry, signedSignature, signedIndex, leaves, signedCodeword,
    forgedCodeword, hroot, hverifierMessage, hforgedOpening, hforgedRun, hentry, hresponse,
    hsignRun, hdigest,
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
  refine ⟨lay, forgedMessage, openingCodeword, chainIdx, hopeningDigit,
    toProbe valueProbe, input, rfl, hopeningEncode, hverifierMessage, hquery,
    toProbe_hits hhit, hmatch, hforgedRun input hquery, ?_, ?_⟩
  · intro hcovered
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
  · exact toProbe_sourceSettled_of_layerRootSettled (leafIndexAt_lt forgedIndex lay) hroot

set_option maxHeartbeats 400000 in
theorem SettledForgedBackwardChainOpening.toVerifyProbeWitness
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {forgedMessage : Message} {digest : MessageDigest}
    {signature : Signature}
    (hdigest : evalWithAnswerFn f (messageDigest secretKey.parameter secretKey.root
      forgedMessage signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hbackward : SettledForgedBackwardChainOpening f cache secretKey signingLog
      (digestIndex digest)
      (digestLeaves digest) signature) :
    VerifyProbeWitness f cache secretKey signingLog forgedMessage signature := by
  obtain ⟨lay, layerMessage, codeword, chainIdx, hdigit, probe, input, hinput, hencode,
    hverifierMessage, hquery, hhit, hmatch, hcached, huncovered, hsettled⟩ :=
      SettledForgedBackwardChainOpening.exists_uncovered_matching_probe hbackward
  exact ⟨lay, digest, layerMessage, codeword, chainIdx, hdigit, probe, input, hinput,
    hdigest, hadmissible, hencode, hverifierMessage, hhit, hmatch,
    VerifierLayerMessage.otsLeaf_query_mem_verify hdigest hadmissible hverifierMessage hquery,
    hcached, huncovered, hsettled⟩

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

end SphincsSecurity.Concrete.OtsProbeSimulation
