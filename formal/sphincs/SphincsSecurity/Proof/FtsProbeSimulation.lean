import SphincsSecurity.Proof.AdaptiveRevealProbe
import SphincsSecurity.Proof.ExtractFts
import SphincsSecurity.Proof.FewTimeSignerView

/-!
# Split random-oracle keys for hidden few-time leaves

Before an unrevealed few-time secret is guessed, its honest leaf-hash input is distinct from every
ordinary hash input available to the adversary. This file builds the lazy split-oracle side of that
argument. Ordinary inputs retain their exact keys, while an internal few-time leaf uses its secret
table coordinate as an opaque key. Both kinds receive lazy and consistent uniform answers.
-/

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open OracleComp OracleSpec ENNReal

abbrev Coordinate := Index × FtsTree × FtsLeaf

noncomputable local instance : Nonempty Coordinate :=
  ⟨(⟨0, by norm_num [totalHeight]⟩,
    ⟨0, by norm_num [ftsTrees]⟩,
    ⟨0, by norm_num [ftsTreeHeight]⟩)⟩

inductive SplitHashKey where
  | ordinary (input : HashInput)
  | hiddenLeaf (coordinate : Coordinate)
deriving DecidableEq

abbrev SplitHashCache := SplitHashKey → Option HashOutput

def emptySplitHashCache : SplitHashCache := fun _ => none

noncomputable local instance : SampleableType HashOutput :=
  SampleableType.ofFintype HashOutput

noncomputable def splitHashQuery (key : SplitHashKey) :
    StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) HashOutput := do
  let cache ← get
  match cache key with
  | some output => pure output
  | none =>
      let output ← liftM
        (AdaptiveRevealProbe.hashOutputQuery (Coordinate := Coordinate))
      set (Function.update cache key (some output))
      pure output

noncomputable def ordinaryHashImpl :
    QueryImpl HashSpec
      (StateT SplitHashCache
        (OracleComp (AdaptiveRevealProbe.World Coordinate))) :=
  fun input => splitHashQuery (.ordinary input)

noncomputable def ordinaryTweakableHash (parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) :
    StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) Digest := do
  let output ← splitHashQuery (.ordinary (tweakableHashInput parameter domain payload))
  pure (truncateHash output)

noncomputable def hiddenFtsLeafHash (_parameter : PublicParameter)
    (coordinate : Coordinate) :
    StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) Digest := do
  let output ← splitHashQuery (.hiddenLeaf coordinate)
  pure (truncateHash output)

noncomputable def maskedFtsNode (parameter : PublicParameter) (index : Index)
    (tree : FtsTree) : Nat → Nat →
      StateT SplitHashCache
        (OracleComp (AdaptiveRevealProbe.World Coordinate)) Digest
  | 0, nodeIdx =>
      hiddenFtsLeafHash parameter (index, tree, ftsLeafOfNat nodeIdx)
  | level + 1, nodeIdx => do
      let left ← maskedFtsNode parameter index tree level (2 * nodeIdx)
      let right ← maskedFtsNode parameter index tree level (2 * nodeIdx + 1)
      ordinaryTweakableHash parameter (.ftsNode index tree (level + 1) nodeIdx)
        (nodePayload left right)

noncomputable def maskedFtsKey (parameter : PublicParameter) (index : Index) :
    StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) Digest := do
  let roots ← sequenceFin fun tree =>
    maskedFtsNode parameter index tree ftsTreeHeight 0
  ordinaryTweakableHash parameter (.ftsRoots index) (ftsRootsPayload roots)

noncomputable def maskedFtsOpen (parameter : PublicParameter) (index : Index)
    (leaves : DigestTree → FtsLeaf) :
    StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate))
        (FtsTree → Fin ftsTreeHeight → Digest) :=
  sequenceFin fun tree =>
    sequenceFin fun level =>
      maskedFtsNode parameter index tree level.val
        (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)

noncomputable def revealFtsSecret (parameter : PublicParameter)
    (coordinate : Coordinate) :
    StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) Digest := do
  let value ← liftM (AdaptiveRevealProbe.revealQuery coordinate)
  let output ← splitHashQuery (.hiddenLeaf coordinate)
  let probe : FtsSecretProbe :=
    ⟨coordinate.1, coordinate.2.1, coordinate.2.2, value⟩
  modify fun cache : SplitHashCache =>
    Function.update cache (.ordinary (probe.input parameter)) (some output)
  pure value

noncomputable def revealSelectedFtsSecrets (parameter : PublicParameter) (index : Index)
    (leaves : DigestTree → FtsLeaf) :
    StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) (FtsTree → Digest) :=
  sequenceFin fun tree =>
    revealFtsSecret parameter (index, tree, leaves (ftsIndexOf tree))

noncomputable def probeFtsSecret (probe : FtsSecretProbe) :
    StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) Unit :=
  liftM (AdaptiveRevealProbe.probeQuery
    (probe.index, probe.tree, probe.leafIdx) probe.candidate)

noncomputable def decodeProbe? (parameter : PublicParameter) (input : HashInput) :
    Option FtsSecretProbe := by
  classical
  exact if hexists : ∃ probe : FtsSecretProbe, probe.input parameter = input then
    some hexists.choose
  else none

theorem decodeProbe?_eq_some_iff (parameter : PublicParameter) (input : HashInput)
    (probe : FtsSecretProbe) :
    decodeProbe? parameter input = some probe ↔ probe.input parameter = input := by
  classical
  unfold decodeProbe?
  split
  · rename_i hexists
    constructor
    · intro heq
      have hprobe : hexists.choose = probe := Option.some.inj heq
      rw [← hprobe]
      exact hexists.choose_spec
    · intro hinput
      congr 1
      apply FtsSecretProbe.input_injective parameter
      exact hexists.choose_spec.trans hinput.symm
  · rename_i hnone
    constructor
    · simp
    · intro hinput
      exact (hnone ⟨probe, hinput⟩).elim

theorem decodeProbe?_eq_none_iff (parameter : PublicParameter) (input : HashInput) :
    decodeProbe? parameter input = none ↔
      ∀ probe : FtsSecretProbe, probe.input parameter ≠ input := by
  constructor
  · intro hnone probe hinput
    have hsome := (decodeProbe?_eq_some_iff parameter input probe).2 hinput
    rw [hnone] at hsome
    simp at hsome
  · intro hnone
    cases hdecode : decodeProbe? parameter input with
    | none => rfl
    | some probe =>
        exact (hnone probe ((decodeProbe?_eq_some_iff parameter input probe).1 hdecode)).elim

@[simp] theorem decodeProbe?_input (parameter : PublicParameter) (probe : FtsSecretProbe) :
    decodeProbe? parameter (probe.input parameter) = some probe :=
  (decodeProbe?_eq_some_iff parameter (probe.input parameter) probe).2 rfl

noncomputable def probingHashQuery (parameter : PublicParameter) (input : HashInput) :
    StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) HashOutput := do
  match decodeProbe? parameter input with
  | some probe => probeFtsSecret probe
  | none => pure ()
  splitHashQuery (.ordinary input)

noncomputable def probingHashImpl (parameter : PublicParameter) :
    QueryImpl HashSpec
      (StateT SplitHashCache
        (OracleComp (AdaptiveRevealProbe.World Coordinate))) :=
  fun input => probingHashQuery parameter input

noncomputable def splitUniformImpl :
    QueryImpl unifSpec
      (StateT SplitHashCache
        (OracleComp (AdaptiveRevealProbe.World Coordinate))) :=
  fun n => liftM (AdaptiveRevealProbe.uniformQuery (Coordinate := Coordinate) n)

noncomputable def splitRomImpl :
    QueryImpl OracleWorld
      (StateT SplitHashCache
        (OracleComp (AdaptiveRevealProbe.World Coordinate))) :=
  splitUniformImpl + ordinaryHashImpl

noncomputable def maskedLayerMessage (secretKey : SecretKey) (index : Index)
    (lay : Layer) :
    StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) Digest :=
  if hbelow : lay.val + 1 < numLayers then
    let below : Layer := ⟨lay.val + 1, hbelow⟩
    simulateQ ordinaryHashImpl
      (treeRoot secretKey.parameter below (treeIndexAt index below)
        (secretKey.otsSecret below (treeIndexAt index below)))
  else
    maskedFtsKey secretKey.parameter index

noncomputable def maskedSignLayer (secretKey : SecretKey) (index : Index)
    (lay : Layer) :
    StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate))
        (Option (Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))) := do
  let tree := treeIndexAt index lay
  let leafIdx := leafIndexAt index lay
  let message ← maskedLayerMessage secretKey index lay
  match ← simulateQ ordinaryHashImpl
      (otsSign secretKey.parameter lay tree leafIdx
        (secretKey.otsSecret lay tree leafIdx) message) with
  | none => pure none
  | some (counter, values) => do
      let path ← simulateQ ordinaryHashImpl
        (treePath secretKey.parameter lay tree (secretKey.otsSecret lay tree) leafIdx)
      pure (some (counter, values, path))

noncomputable def maskedSignAfterDigest (secretKey : SecretKey)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) (Option Signature) := do
  let ftsPath ← maskedFtsOpen secretKey.parameter index leaves
  let layers ← sequenceFin fun lay => maskedSignLayer secretKey index lay
  match traverseOption layers with
  | none => pure none
  | some parts => do
      let selected ← revealSelectedFtsSecrets secretKey.parameter index leaves
      pure (some
        { randomness := randomness
          ftsSecret := selected
          ftsPath := ftsPath
          counter := fun lay => (parts lay).1
          chainValue := fun lay => (parts lay).2.1
          authPath := flattenPaths fun lay => (parts lay).2.2 })

noncomputable def maskedSignWithView (secretKey : SecretKey) (message : Message) :
    StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate))
        (Option Signature × Option FewTimeView) := do
  match ← simulateQ splitRomImpl
      (signDigestLoop digestAttemptLimit secretKey message) with
  | none => pure (none, none)
  | some (randomness, index, leaves) => do
      let signature ← maskedSignAfterDigest secretKey randomness index leaves
      pure (signature, some (selectedFewTimeView index leaves))

def tableProbe (table : Coordinate → Digest) (coordinate : Coordinate) :
    FtsSecretProbe :=
  ⟨coordinate.1, coordinate.2.1, coordinate.2.2, table coordinate⟩

def hiddenInput (parameter : PublicParameter) (table : Coordinate → Digest)
    (coordinate : Coordinate) : HashInput :=
  (tableProbe table coordinate).input parameter

noncomputable def mergedCache (parameter : PublicParameter)
    (table : Coordinate → Digest) (cache : SplitHashCache) : QueryCache HashSpec :=
  fun input =>
    match decodeProbe? parameter input with
    | some probe =>
        let coordinate : Coordinate := (probe.index, probe.tree, probe.leafIdx)
        if probe.candidate = table coordinate then cache (.hiddenLeaf coordinate)
        else cache (.ordinary input)
    | none => cache (.ordinary input)

@[simp] theorem mergedCache_empty (parameter : PublicParameter)
    (table : Coordinate → Digest) :
    mergedCache parameter table emptySplitHashCache = ∅ := by
  funext input
  unfold mergedCache emptySplitHashCache
  split <;> simp

@[simp] theorem mergedCache_probe_input (parameter : PublicParameter)
    (table : Coordinate → Digest) (cache : SplitHashCache) (probe : FtsSecretProbe) :
    mergedCache parameter table cache (probe.input parameter) =
      let coordinate : Coordinate := (probe.index, probe.tree, probe.leafIdx)
      if probe.candidate = table coordinate then cache (.hiddenLeaf coordinate)
      else cache (.ordinary (probe.input parameter)) := by
  rw [mergedCache, decodeProbe?_input]

@[simp] theorem mergedCache_hiddenInput (parameter : PublicParameter)
    (table : Coordinate → Digest) (cache : SplitHashCache) (coordinate : Coordinate) :
    mergedCache parameter table cache (hiddenInput parameter table coordinate) =
      cache (.hiddenLeaf coordinate) := by
  rw [hiddenInput, mergedCache_probe_input]
  simp only [tableProbe]
  rfl

theorem probe_eq_tableProbe_of_candidate (table : Coordinate → Digest)
    (probe : FtsSecretProbe)
    (hcandidate : probe.candidate =
      table (probe.index, probe.tree, probe.leafIdx)) :
    probe = tableProbe table (probe.index, probe.tree, probe.leafIdx) := by
  cases probe
  simp only [tableProbe, FtsSecretProbe.mk.injEq, true_and]
  exact hcandidate

theorem mergedCache_update_hiddenLeaf (parameter : PublicParameter)
    (table : Coordinate → Digest) (cache : SplitHashCache)
    (coordinate : Coordinate) (output : HashOutput) :
    mergedCache parameter table
        (Function.update cache (.hiddenLeaf coordinate) (some output)) =
      (mergedCache parameter table cache).cacheQuery
        (hiddenInput parameter table coordinate) output := by
  funext input
  by_cases heq : input = hiddenInput parameter table coordinate
  · subst input
    rw [mergedCache_hiddenInput, Function.update_self,
      QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ heq]
    unfold mergedCache
    cases hdecode : decodeProbe? parameter input with
    | none =>
        simp only
        rw [Function.update_of_ne]
        simp
    | some probe =>
        simp only
        let probeCoordinate : Coordinate := (probe.index, probe.tree, probe.leafIdx)
        by_cases hcandidate : probe.candidate = table probeCoordinate
        · rw [if_pos hcandidate]
          have hcandidate' :
              probe.candidate = table (probe.index, probe.tree, probe.leafIdx) :=
            hcandidate
          have hcoordinate : probeCoordinate ≠ coordinate := by
            intro hsame
            apply heq
            have hprobe := probe_eq_tableProbe_of_candidate table probe hcandidate
            have hinput := (decodeProbe?_eq_some_iff parameter input probe).1 hdecode
            have hsame' : (probe.index, probe.tree, probe.leafIdx) = coordinate := hsame
            rw [← hinput, hprobe, hiddenInput, hsame']
          rw [Function.update_of_ne (by
            intro hkey
            exact hcoordinate (SplitHashKey.hiddenLeaf.inj hkey))]
          simp [hcandidate']
        · have hcandidate' :
              probe.candidate ≠ table (probe.index, probe.tree, probe.leafIdx) :=
            hcandidate
          rw [if_neg hcandidate', Function.update_of_ne (by simp)]
          simp [hcandidate']

def IsOrdinaryInput (parameter : PublicParameter) (table : Coordinate → Digest)
    (input : HashInput) : Prop :=
  ∀ probe : FtsSecretProbe, decodeProbe? parameter input = some probe →
    probe.candidate ≠ table (probe.index, probe.tree, probe.leafIdx)

theorem mergedCache_eq_ordinary_of_isOrdinary (parameter : PublicParameter)
    (table : Coordinate → Digest) (cache : SplitHashCache) (input : HashInput)
    (hordinary : IsOrdinaryInput parameter table input) :
    mergedCache parameter table cache input = cache (.ordinary input) := by
  unfold mergedCache
  cases hdecode : decodeProbe? parameter input with
  | none => rfl
  | some probe =>
      simp only
      rw [if_neg (hordinary probe hdecode)]

theorem mergedCache_update_ordinary (parameter : PublicParameter)
    (table : Coordinate → Digest) (cache : SplitHashCache)
    (input : HashInput) (output : HashOutput)
    (hordinary : IsOrdinaryInput parameter table input) :
    mergedCache parameter table
        (Function.update cache (.ordinary input) (some output)) =
      (mergedCache parameter table cache).cacheQuery input output := by
  funext other
  by_cases heq : other = input
  · subst other
    rw [mergedCache_eq_ordinary_of_isOrdinary parameter table _ input hordinary,
      Function.update_self, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ heq]
    unfold mergedCache
    cases hdecode : decodeProbe? parameter other with
    | none =>
        rw [Function.update_of_ne]
        intro hkey
        exact heq (SplitHashKey.ordinary.inj hkey)
    | some probe =>
        simp only
        by_cases hcandidate :
            probe.candidate = table (probe.index, probe.tree, probe.leafIdx)
        · rw [if_pos hcandidate, Function.update_of_ne (by simp)]
          simp [hcandidate]
        · rw [if_neg hcandidate, Function.update_of_ne]
          · simp [hcandidate]
          · intro hkey
            exact heq (SplitHashKey.ordinary.inj hkey)

def fullSplitCache (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → Digest) : SplitHashCache
  | .ordinary input => some (f input)
  | .hiddenLeaf coordinate => some (f (hiddenInput parameter table coordinate))

@[simp] theorem mergedCache_fullSplitCache (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (table : Coordinate → Digest) :
    mergedCache parameter table (fullSplitCache f parameter table) = fun input => some (f input) := by
  funext input
  unfold mergedCache
  cases hdecode : decodeProbe? parameter input with
  | none => rfl
  | some probe =>
      simp only
      by_cases hcandidate :
          probe.candidate = table (probe.index, probe.tree, probe.leafIdx)
      · rw [if_pos hcandidate]
        have hprobe := probe_eq_tableProbe_of_candidate table probe hcandidate
        have hinput := (decodeProbe?_eq_some_iff parameter input probe).1 hdecode
        rw [fullSplitCache, hiddenInput, ← hinput, hprobe]
        exact rfl
      · rw [if_neg hcandidate]
        rfl

theorem splitHashQuery_run_eq (key : SplitHashKey) (cache : SplitHashCache) :
    (splitHashQuery key).run cache =
      match cache key with
      | some output => pure (output, cache)
      | none => (AdaptiveRevealProbe.hashOutputQuery (Coordinate := Coordinate)) >>= fun output =>
          pure (output, Function.update cache key (some output)) := by
  cases hlookup : cache key <;> simp [splitHashQuery, hlookup]

@[simp] theorem splitHashQuery_run_fullSplitCache
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → Digest) (key : SplitHashKey) :
    (splitHashQuery key).run (fullSplitCache f parameter table) =
      pure ((match key with
        | .ordinary input => f input
        | .hiddenLeaf coordinate => f (hiddenInput parameter table coordinate)),
          fullSplitCache f parameter table) := by
  rw [splitHashQuery_run_eq]
  cases key <;> simp [fullSplitCache]

@[simp] theorem splitHashQuery_run'_fullSplitCache
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → Digest) (key : SplitHashKey) :
    (splitHashQuery key).run' (fullSplitCache f parameter table) =
      pure (match key with
        | .ordinary input => f input
        | .hiddenLeaf coordinate => f (hiddenInput parameter table coordinate)) := by
  rw [StateT.run'_eq, splitHashQuery_run_eq]
  cases key <;> simp [fullSplitCache]

@[simp] theorem ordinaryTweakableHash_run'_fullSplitCache
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → Digest) (domain : HashDomain) (payload : HashInput) :
    (ordinaryTweakableHash parameter domain payload).run'
        (fullSplitCache f parameter table) =
      pure (truncateHash (f (tweakableHashInput parameter domain payload))) := by
  rw [StateT.run'_eq]
  change ((fun a => truncateHash a.1) <$>
      (splitHashQuery (.ordinary (tweakableHashInput parameter domain payload))).run
        (fullSplitCache f parameter table)) = _
  rw [splitHashQuery_run_eq]
  simp [fullSplitCache]

@[simp] theorem ordinaryTweakableHash_run_fullSplitCache
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → Digest) (domain : HashDomain) (payload : HashInput) :
    (ordinaryTweakableHash parameter domain payload).run
        (fullSplitCache f parameter table) =
      pure (truncateHash (f (tweakableHashInput parameter domain payload)),
        fullSplitCache f parameter table) := by
  simp [ordinaryTweakableHash]

@[simp] theorem hiddenFtsLeafHash_run'_fullSplitCache
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → Digest) (coordinate : Coordinate) :
    (hiddenFtsLeafHash parameter coordinate).run'
        (fullSplitCache f parameter table) =
      pure (truncateHash (f (hiddenInput parameter table coordinate))) := by
  rw [StateT.run'_eq]
  change ((fun a => truncateHash a.1) <$>
      (splitHashQuery (.hiddenLeaf coordinate)).run
        (fullSplitCache f parameter table)) = _
  rw [splitHashQuery_run_eq]
  simp [fullSplitCache]

@[simp] theorem hiddenFtsLeafHash_run_fullSplitCache
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → Digest) (coordinate : Coordinate) :
    (hiddenFtsLeafHash parameter coordinate).run
        (fullSplitCache f parameter table) =
      pure (truncateHash (f (hiddenInput parameter table coordinate)),
        fullSplitCache f parameter table) := by
  simp [hiddenFtsLeafHash]

theorem maskedFtsNode_run_fullSplitCache
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → Digest) (index : Index) (tree : FtsTree)
    (level nodeIdx : Nat) :
    (maskedFtsNode parameter index tree level nodeIdx).run
        (fullSplitCache f parameter table) =
      pure (honestFtsNode f parameter index tree
          (fun leafIdx => table (index, tree, leafIdx)) level nodeIdx,
        fullSplitCache f parameter table) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [maskedFtsNode]
      simp only [hiddenFtsLeafHash_run_fullSplitCache]
      congr 2
      simp only [honestFtsNode, ftsNode_zero_eq, ftsLeafHash, eval_tweakableHash]
      rfl
  | succ level ih =>
      rw [maskedFtsNode, StateT.run_bind, ih, pure_bind,
        StateT.run_bind, ih, pure_bind,
        ordinaryTweakableHash_run_fullSplitCache]
      congr 2
      exact (honestFtsNode_succ f parameter index tree
        (fun leafIdx => table (index, tree, leafIdx)) level nodeIdx).symm

theorem sequenceFin_run_of_run_eq_pure {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha)
    (values : Fin n → alpha) (cache : SplitHashCache)
    (hrun : ∀ position, (computation position).run cache = pure (values position, cache)) :
    (sequenceFin computation).run cache = pure (values, cache) := by
  induction n with
  | zero =>
      rw [sequenceFin, StateT.run_pure]
      congr 2
      funext position
      exact Fin.elim0 position
  | succ n ih =>
      rw [sequenceFin, StateT.run_bind, hrun 0, pure_bind,
        StateT.run_bind,
        ih (fun position => computation position.succ)
          (fun position => values position.succ)
          (fun position => hrun position.succ),
        pure_bind, StateT.run_pure]
      congr 2
      funext position
      cases position using Fin.cases <;> rfl

theorem maskedFtsKey_run_fullSplitCache
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → Digest) (index : Index) :
    (maskedFtsKey parameter index).run (fullSplitCache f parameter table) =
      pure (evalWithAnswerFn f
          (ftsKey parameter index (fun tree leafIdx => table (index, tree, leafIdx))),
        fullSplitCache f parameter table) := by
  unfold maskedFtsKey
  rw [StateT.run_bind,
    sequenceFin_run_of_run_eq_pure
      (values := fun tree => honestFtsNode f parameter index tree
        (fun leafIdx => table (index, tree, leafIdx)) ftsTreeHeight 0)
      (hrun := fun tree => maskedFtsNode_run_fullSplitCache f parameter table index tree
        ftsTreeHeight 0),
    pure_bind, ordinaryTweakableHash_run_fullSplitCache]
  congr 2
  simp only [ftsKey, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
    eval_tweakableHash, honestFtsNode]

theorem maskedFtsOpen_run_fullSplitCache
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → Digest) (index : Index)
    (leaves : DigestTree → FtsLeaf) :
    (maskedFtsOpen parameter index leaves).run (fullSplitCache f parameter table) =
      pure (evalWithAnswerFn f
          (ftsOpen parameter index leaves
            (fun tree leafIdx => table (index, tree, leafIdx))),
        fullSplitCache f parameter table) := by
  unfold maskedFtsOpen
  rw [sequenceFin_run_of_run_eq_pure
    (values := fun tree level => honestFtsNode f parameter index tree
      (fun leafIdx => table (index, tree, leafIdx)) level.val
      (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1))
    (hrun := fun tree => sequenceFin_run_of_run_eq_pure
      (values := fun level => honestFtsNode f parameter index tree
        (fun leafIdx => table (index, tree, leafIdx)) level.val
        (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1))
      (hrun := fun level => maskedFtsNode_run_fullSplitCache f parameter table index tree
        level.val (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)))]
  congr 2
  simp only [ftsOpen, evalWithAnswerFn_sequenceFin, honestFtsNode]

theorem splitHashQuery_run_isProbeBound (key : SplitHashKey) (cache : SplitHashCache)
    (fuel : Nat) :
    ((splitHashQuery key).run cache).IsQueryBoundP
      (AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate)) fuel := by
  rw [splitHashQuery_run_eq]
  cases hlookup : cache key with
  | some output => simp
  | none =>
      change (((fun output : HashOutput =>
          (output, Function.update cache key (some output))) <$>
        AdaptiveRevealProbe.hashOutputQuery (Coordinate := Coordinate)).IsQueryBoundP
          (AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate)) fuel)
      rw [isQueryBoundP_map_iff]
      exact AdaptiveRevealProbe.hashOutputQuery_isProbeBound
        (Coordinate := Coordinate) fuel

theorem splitHashQuery_run'_isProbeBound (key : SplitHashKey) (cache : SplitHashCache)
    (fuel : Nat) :
    ((splitHashQuery key).run' cache).IsQueryBoundP
      (AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate)) fuel := by
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  exact splitHashQuery_run_isProbeBound key cache fuel

theorem probingHashQuery_run_eq (parameter : PublicParameter) (input : HashInput)
    (cache : SplitHashCache) :
    (probingHashQuery parameter input).run cache =
      match decodeProbe? parameter input with
      | some probe =>
          AdaptiveRevealProbe.probeQuery
              (probe.index, probe.tree, probe.leafIdx) probe.candidate >>= fun _ =>
            (splitHashQuery (.ordinary input)).run cache
      | none => (splitHashQuery (.ordinary input)).run cache := by
  cases hdecode : decodeProbe? parameter input <;>
    simp [probingHashQuery, probeFtsSecret, hdecode]

theorem probingHashQuery_run_isProbeBound (parameter : PublicParameter)
    (input : HashInput) (cache : SplitHashCache) :
    ((probingHashQuery parameter input).run cache).IsQueryBoundP
      (AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate)) 1 := by
  rw [probingHashQuery_run_eq]
  cases hdecode : decodeProbe? parameter input with
  | none => exact splitHashQuery_run_isProbeBound (.ordinary input) cache 1
  | some probe =>
      change ((AdaptiveRevealProbe.probeQuery
          (probe.index, probe.tree, probe.leafIdx) probe.candidate >>= fun _ =>
        (splitHashQuery (.ordinary input)).run cache).IsQueryBoundP
          (AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate)) 1)
      have hbound := isQueryBoundP_bind (n := 1) (m := 0)
        (AdaptiveRevealProbe.probeQuery_isProbeBound
          (probe.index, probe.tree, probe.leafIdx) probe.candidate)
        (fun _ _ => splitHashQuery_run_isProbeBound (.ordinary input) cache 0)
      simpa using hbound

theorem probingHashQuery_run'_isProbeBound (parameter : PublicParameter)
    (input : HashInput) (cache : SplitHashCache) :
    ((probingHashQuery parameter input).run' cache).IsQueryBoundP
      (AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate)) 1 := by
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  exact probingHashQuery_run_isProbeBound parameter input cache

theorem simulateQ_probingHashImpl_run_isProbeBound (parameter : PublicParameter)
    (computation : OracleComp HashSpec alpha) (q : Nat)
    (hbound : computation.IsQueryBoundP (fun _ => True) q)
    (cache : SplitHashCache) :
    ((simulateQ (probingHashImpl parameter) computation).run cache).IsQueryBoundP
      (AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate)) q := by
  apply hbound.simulateQ_run_StateT_of_step
    (q := AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate))
  intro input workingCache
  change ((probingHashQuery parameter input).run workingCache).IsQueryBoundP
    (AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate)) 1
  exact probingHashQuery_run_isProbeBound parameter input workingCache

theorem simulateQ_probingHashImpl_run'_isProbeBound (parameter : PublicParameter)
    (computation : OracleComp HashSpec alpha) (q : Nat)
    (hbound : computation.IsQueryBoundP (fun _ => True) q)
    (cache : SplitHashCache) :
    ((simulateQ (probingHashImpl parameter) computation).run' cache).IsQueryBoundP
      (AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate)) q := by
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  exact simulateQ_probingHashImpl_run_isProbeBound parameter computation q hbound cache

theorem probEvent_probingHashExperiment_le (parameter : PublicParameter)
    (computation : OracleComp HashSpec alpha) (q : Nat)
    (hbound : computation.IsQueryBoundP (fun _ => True) q) :
    Pr[fun hit : Bool => hit = true |
        AdaptiveRevealProbe.experiment
          (AdaptiveRevealProbe.State.empty : AdaptiveRevealProbe.State Coordinate) q
          ((simulateQ (probingHashImpl parameter) computation).run'
            emptySplitHashCache)] ≤
      (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply AdaptiveRevealProbe.experiment_empty_probability_le
  exact simulateQ_probingHashImpl_run'_isProbeBound parameter computation q hbound
    emptySplitHashCache

def ProbeFree
    (computation : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ cache, (computation.run cache).IsQueryBoundP
    (AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate)) 0

theorem ProbeFree.pure (value : alpha) :
    ProbeFree (pure value : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha) := by
  intro cache
  simp

theorem ProbeFree.modify (update : SplitHashCache → SplitHashCache) :
    ProbeFree (modify update : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) Unit) := by
  intro cache
  simp

theorem ProbeFree.bind
    {left : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) beta}
    (hleft : ProbeFree left) (hnext : ∀ value, ProbeFree (next value)) :
    ProbeFree (left >>= next) := by
  intro cache
  rw [StateT.run_bind]
  have hbound := isQueryBoundP_bind (n := 0) (m := 0) (hleft cache)
    (fun result _ => hnext result.1 result.2)
  simpa using hbound

theorem ProbeFree.map
    {computation : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha}
    (hcomputation : ProbeFree computation) (transform : alpha → beta) :
    ProbeFree (transform <$> computation) := by
  rw [map_eq_bind_pure_comp]
  exact hcomputation.bind fun value => ProbeFree.pure (transform value)

theorem splitUniformImpl_probeFree (n : unifSpec.Domain) :
    ProbeFree (splitUniformImpl n) := by
  intro cache
  change (((fun output : Fin (n + 1) => (output, cache)) <$>
    AdaptiveRevealProbe.uniformQuery (Coordinate := Coordinate) n).IsQueryBoundP
      (AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
  rw [isQueryBoundP_map_iff, AdaptiveRevealProbe.uniformQuery,
    OracleComp.isQueryBoundP_query_iff]
  simp [AdaptiveRevealProbe.IsProbe]

theorem simulateQ_splitRomImpl_probeFree
    (computation : OracleComp OracleWorld alpha) :
    ProbeFree (simulateQ splitRomImpl computation) := by
  intro cache
  apply (isQueryBoundP_false computation 0).simulateQ_run_StateT_of_step
  intro input workingCache
  cases input with
  | inl n =>
      exact splitUniformImpl_probeFree n workingCache
  | inr hashInput =>
      exact splitHashQuery_run_isProbeBound (.ordinary hashInput) workingCache 0

theorem simulateQ_ordinaryHashImpl_probeFree
    (computation : OracleComp HashSpec alpha) :
    ProbeFree (simulateQ ordinaryHashImpl computation) := by
  intro cache
  apply (isQueryBoundP_false computation 0).simulateQ_run_StateT_of_step
  intro input workingCache
  exact splitHashQuery_run_isProbeBound (.ordinary input) workingCache 0

theorem splitHashQuery_probeFree (key : SplitHashKey) :
    ProbeFree (splitHashQuery key) :=
  fun cache => splitHashQuery_run_isProbeBound key cache 0

theorem ordinaryTweakableHash_probeFree (parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) :
    ProbeFree (ordinaryTweakableHash parameter domain payload) := by
  unfold ordinaryTweakableHash
  exact (splitHashQuery_probeFree (.ordinary
    (tweakableHashInput parameter domain payload))).bind fun output =>
      ProbeFree.pure (truncateHash output)

theorem hiddenFtsLeafHash_probeFree (parameter : PublicParameter)
    (coordinate : Coordinate) : ProbeFree (hiddenFtsLeafHash parameter coordinate) := by
  unfold hiddenFtsLeafHash
  exact (splitHashQuery_probeFree (.hiddenLeaf coordinate)).bind fun output =>
    ProbeFree.pure (truncateHash output)

theorem sequenceFin_probeFree {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha)
    (hcomputation : ∀ index, ProbeFree (computation index)) :
    ProbeFree (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact ProbeFree.pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomputation 0).bind fun head =>
        (ih (fun index => computation index.succ)
          (fun index => hcomputation index.succ)).bind fun tail =>
            ProbeFree.pure (Fin.cases head tail : Fin (n + 1) → alpha)

theorem maskedFtsNode_probeFree (parameter : PublicParameter) (index : Index)
    (tree : FtsTree) (level nodeIdx : Nat) :
    ProbeFree (maskedFtsNode parameter index tree level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      exact hiddenFtsLeafHash_probeFree parameter
        (index, tree, ftsLeafOfNat nodeIdx)
  | succ level ih =>
      rw [maskedFtsNode]
      exact (ih (2 * nodeIdx)).bind fun left =>
        (ih (2 * nodeIdx + 1)).bind fun right =>
          ordinaryTweakableHash_probeFree parameter
            (.ftsNode index tree (level + 1) nodeIdx) (nodePayload left right)

theorem maskedFtsKey_probeFree (parameter : PublicParameter) (index : Index) :
    ProbeFree (maskedFtsKey parameter index) := by
  unfold maskedFtsKey
  exact (sequenceFin_probeFree
    (fun tree => maskedFtsNode parameter index tree ftsTreeHeight 0)
    (fun tree => maskedFtsNode_probeFree parameter index tree ftsTreeHeight 0)).bind
      fun roots => ordinaryTweakableHash_probeFree parameter (.ftsRoots index)
        (ftsRootsPayload roots)

theorem maskedFtsOpen_probeFree (parameter : PublicParameter) (index : Index)
    (leaves : DigestTree → FtsLeaf) :
    ProbeFree (maskedFtsOpen parameter index leaves) := by
  unfold maskedFtsOpen
  apply sequenceFin_probeFree
  intro tree
  apply sequenceFin_probeFree
  intro level
  exact maskedFtsNode_probeFree parameter index tree level.val
    (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)

theorem revealQuery_probeFree (coordinate : Coordinate) :
    ProbeFree (liftM (AdaptiveRevealProbe.revealQuery coordinate) :
      StateT SplitHashCache
        (OracleComp (AdaptiveRevealProbe.World Coordinate)) Digest) := by
  intro cache
  change (((fun value : Digest => (value, cache)) <$>
    AdaptiveRevealProbe.revealQuery coordinate).IsQueryBoundP
      (AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
  rw [isQueryBoundP_map_iff]
  exact AdaptiveRevealProbe.revealQuery_isProbeBound coordinate 0

theorem revealFtsSecret_probeFree (parameter : PublicParameter)
    (coordinate : Coordinate) : ProbeFree (revealFtsSecret parameter coordinate) := by
  unfold revealFtsSecret
  exact (revealQuery_probeFree coordinate).bind fun value =>
    (splitHashQuery_probeFree (.hiddenLeaf coordinate)).bind fun output => by
      exact (ProbeFree.modify fun cache : SplitHashCache =>
        Function.update cache
          (.ordinary ((⟨coordinate.1, coordinate.2.1, coordinate.2.2,
            value⟩ : FtsSecretProbe).input parameter)) (some output)).bind fun _ =>
            ProbeFree.pure value

theorem revealSelectedFtsSecrets_probeFree (parameter : PublicParameter) (index : Index)
    (leaves : DigestTree → FtsLeaf) :
    ProbeFree (revealSelectedFtsSecrets parameter index leaves) := by
  unfold revealSelectedFtsSecrets
  apply sequenceFin_probeFree
  intro tree
  exact revealFtsSecret_probeFree parameter (index, tree, leaves (ftsIndexOf tree))

theorem maskedLayerMessage_probeFree (secretKey : SecretKey) (index : Index)
    (lay : Layer) : ProbeFree (maskedLayerMessage secretKey index lay) := by
  unfold maskedLayerMessage
  split
  · exact simulateQ_ordinaryHashImpl_probeFree _
  · exact maskedFtsKey_probeFree secretKey.parameter index

theorem maskedSignLayer_probeFree (secretKey : SecretKey) (index : Index)
    (lay : Layer) : ProbeFree (maskedSignLayer secretKey index lay) := by
  unfold maskedSignLayer
  exact (maskedLayerMessage_probeFree secretKey index lay).bind fun message =>
    (simulateQ_ordinaryHashImpl_probeFree
      (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
        message)).bind fun signed => by
      cases signed with
      | none => exact ProbeFree.pure none
      | some part =>
          exact (simulateQ_ordinaryHashImpl_probeFree
            (treePath secretKey.parameter lay (treeIndexAt index lay)
              (secretKey.otsSecret lay (treeIndexAt index lay))
              (leafIndexAt index lay))).bind fun path =>
                ProbeFree.pure (some (part.1, part.2, path))

theorem maskedSignAfterDigest_probeFree (secretKey : SecretKey)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    ProbeFree (maskedSignAfterDigest secretKey randomness index leaves) := by
  unfold maskedSignAfterDigest
  exact (maskedFtsOpen_probeFree secretKey.parameter index leaves).bind fun ftsPath =>
    (sequenceFin_probeFree (fun lay => maskedSignLayer secretKey index lay)
      (fun lay => maskedSignLayer_probeFree secretKey index lay)).bind fun layers => by
        cases hparts : traverseOption layers with
        | none => exact ProbeFree.pure none
        | some parts =>
            exact (revealSelectedFtsSecrets_probeFree secretKey.parameter index leaves).bind
              fun selected => ProbeFree.pure (some
                (show Signature from
                { randomness := randomness
                  ftsSecret := selected
                  ftsPath := ftsPath
                  counter := fun lay => (parts lay).1
                  chainValue := fun lay => (parts lay).2.1
                  authPath := flattenPaths fun lay => (parts lay).2.2 }))

theorem maskedSignWithView_probeFree (secretKey : SecretKey) (message : Message) :
    ProbeFree (maskedSignWithView secretKey message) := by
  unfold maskedSignWithView
  exact (simulateQ_splitRomImpl_probeFree
    (signDigestLoop digestAttemptLimit secretKey message)).bind fun selected => by
      cases selected with
      | none => exact ProbeFree.pure (none, none)
      | some data =>
          exact (maskedSignAfterDigest_probeFree secretKey data.1 data.2.1 data.2.2).bind
            fun signature => ProbeFree.pure
              (signature, some (selectedFewTimeView data.2.1 data.2.2))

@[simp] theorem hiddenFtsLeafHash_parameter_irrelevant
    (left right : PublicParameter) (coordinate : Coordinate) :
    hiddenFtsLeafHash left coordinate = hiddenFtsLeafHash right coordinate := rfl

end SphincsSecurity.Concrete.FtsProbeSimulation
