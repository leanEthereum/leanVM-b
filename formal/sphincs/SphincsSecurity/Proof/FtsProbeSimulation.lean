import SphincsSecurity.Proof.AdaptiveRevealProbe
import SphincsSecurity.Proof.ExtractFts
import SphincsSecurity.Proof.FewTimeSignerView
import SphincsSecurity.Proof.SigningTrace

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

noncomputable def probingRomImpl (parameter : PublicParameter) :
    QueryImpl OracleWorld
      (StateT SplitHashCache
        (OracleComp (AdaptiveRevealProbe.World Coordinate))) :=
  splitUniformImpl + probingHashImpl parameter

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

noncomputable def maskedSigningImpl (secretKey : SecretKey) :
    QueryImpl SigningSpec
      (StateT SplitHashCache
        (OracleComp (AdaptiveRevealProbe.World Coordinate))) :=
  fun request => Prod.fst <$> maskedSignWithView secretKey request

noncomputable def maskedExpandedAdversaryImpl (parameter : PublicParameter)
    (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT SplitHashCache
        (OracleComp (AdaptiveRevealProbe.World Coordinate))) :=
  probingRomImpl parameter + maskedSigningImpl secretKey

noncomputable def maskedGameAfterSecrets (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :
    StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) Bool := do
  let root ← simulateQ ordinaryHashImpl
    (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))
  let secretKey : SecretKey :=
    ⟨parameter, root, otsSecret, fun _index _tree _leafIdx => 0⟩
  let (forgery, log) ←
    (simulateQ (QueryImpl.withTraceAppend
      (maskedExpandedAdversaryImpl parameter secretKey) signingLogFragment)
      (adversary.main ⟨root, parameter⟩)).run
  let verified ← simulateQ (probingRomImpl parameter)
    (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)
  pure (decide (SigningTranscript.Valid log ∧
    ¬SigningTranscript.Contains log forgery) && verified)

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

theorem isOrdinaryInput_of_decode_none (parameter : PublicParameter)
    (table : Coordinate → Digest) (input : HashInput)
    (hdecode : decodeProbe? parameter input = none) :
    IsOrdinaryInput parameter table input := by
  intro probe hsome
  rw [hdecode] at hsome
  simp at hsome

theorem isOrdinaryInput_of_decode_miss (parameter : PublicParameter)
    (table : Coordinate → Digest) (input : HashInput) (probe : FtsSecretProbe)
    (hdecode : decodeProbe? parameter input = some probe)
    (hmiss : probe.candidate ≠ table (probe.index, probe.tree, probe.leafIdx)) :
    IsOrdinaryInput parameter table input := by
  intro other hother
  have heq : other = probe := Option.some.inj (hother.symm.trans hdecode)
  subst other
  exact hmiss

theorem isOrdinaryInput_of_not_hit (parameter : PublicParameter)
    (table : Coordinate → Digest) (input : HashInput)
    (hmiss : ∀ probe : FtsSecretProbe, decodeProbe? parameter input = some probe →
      table (probe.index, probe.tree, probe.leafIdx) ≠ probe.candidate) :
    IsOrdinaryInput parameter table input := by
  intro probe hdecode
  exact (hmiss probe hdecode).symm

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

theorem mergedCache_update_hiddenInput_ordinary
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (cache : SplitHashCache) (coordinate : Coordinate) (output : HashOutput) :
    mergedCache parameter table
        (Function.update cache (.ordinary (hiddenInput parameter table coordinate))
          (some output)) =
      mergedCache parameter table cache := by
  funext input
  by_cases heq : input = hiddenInput parameter table coordinate
  · subst input
    rw [mergedCache_hiddenInput, mergedCache_hiddenInput,
      Function.update_of_ne (by simp)]
  · unfold mergedCache
    cases hdecode : decodeProbe? parameter input with
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

noncomputable def projectDetailedCache (parameter : PublicParameter) (table : Coordinate → Digest) :
    AdaptiveRevealProbe.DetailedResult Coordinate (alpha × SplitHashCache) →
      Option (alpha × QueryCache HashSpec)
  | .stopped _ => none
  | .done true _ _ => none
  | .done false _ (value, cache) => some (value, mergedCache parameter table cache)

def RevealedSynced (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (cache : SplitHashCache) : Prop :=
  ∀ coordinate value, state.revealed coordinate = some value →
    value = table coordinate ∧
      ∃ output, cache (.hiddenLeaf coordinate) = some output ∧
        cache (.ordinary (hiddenInput parameter table coordinate)) = some output

theorem revealedSynced_empty (parameter : PublicParameter) (table : Coordinate → Digest) :
    RevealedSynced parameter table AdaptiveRevealProbe.State.empty emptySplitHashCache := by
  intro coordinate value hvalue
  simp [AdaptiveRevealProbe.State.empty] at hvalue

theorem IsOrdinaryInput.ne_hiddenInput
    {parameter : PublicParameter} {table : Coordinate → Digest} {input : HashInput}
    (hordinary : IsOrdinaryInput parameter table input) (coordinate : Coordinate) :
    input ≠ hiddenInput parameter table coordinate := by
  intro heq
  subst input
  let probe := tableProbe table coordinate
  have hdecode : decodeProbe? parameter (hiddenInput parameter table coordinate) = some probe := by
    change decodeProbe? parameter ((tableProbe table coordinate).input parameter) =
      some (tableProbe table coordinate)
    exact decodeProbe?_input parameter (tableProbe table coordinate)
  have hne := hordinary probe hdecode
  exact hne rfl

theorem hiddenInput_injective (parameter : PublicParameter) (table : Coordinate → Digest) :
    Function.Injective (hiddenInput parameter table) := by
  intro left right heq
  have hprobe := FtsSecretProbe.input_injective parameter heq
  rcases left with ⟨leftIndex, leftTree, leftLeaf⟩
  rcases right with ⟨rightIndex, rightTree, rightLeaf⟩
  simp only [tableProbe, FtsSecretProbe.mk.injEq] at hprobe
  cases hprobe.1
  cases hprobe.2.1
  cases hprobe.2.2.1
  rfl

theorem RevealedSynced.update_ordinary
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {state : AdaptiveRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hsynced : RevealedSynced parameter table state cache)
    (input : HashInput) (output : HashOutput)
    (hordinary : IsOrdinaryInput parameter table input) :
    RevealedSynced parameter table state
      (Function.update cache (.ordinary input) (some output)) := by
  intro coordinate value hrevealed
  obtain ⟨hvalue, oldOutput, hhidden, hordinaryCache⟩ :=
    hsynced coordinate value hrevealed
  refine ⟨hvalue, oldOutput, ?_, ?_⟩
  · rw [Function.update_of_ne (by simp)]
    exact hhidden
  · rw [Function.update_of_ne]
    · exact hordinaryCache
    · intro heq
      exact hordinary.ne_hiddenInput coordinate (SplitHashKey.ordinary.inj heq).symm

theorem RevealedSynced.install
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {state : AdaptiveRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hsynced : RevealedSynced parameter table state cache)
    (coordinate : Coordinate) (value : Digest) (output : HashOutput)
    (hvalue : value = table coordinate)
    (hhidden : cache (.hiddenLeaf coordinate) = some output) :
    RevealedSynced parameter table (state.install coordinate value)
      (Function.update cache (.ordinary (hiddenInput parameter table coordinate))
        (some output)) := by
  intro other otherValue hrevealed
  by_cases heq : other = coordinate
  · subst other
    have hotherValue : otherValue = value := by
      have hsome : some value = some otherValue := by
        simpa [AdaptiveRevealProbe.State.install] using hrevealed
      exact (Option.some.inj hsome).symm
    subst otherValue
    refine ⟨hvalue, output, ?_, ?_⟩
    · rw [Function.update_of_ne (by simp)]
      exact hhidden
    · rw [Function.update_self]
  · have hrevealedOld : state.revealed other = some otherValue := by
      simpa [AdaptiveRevealProbe.State.install, Function.update_of_ne heq] using hrevealed
    obtain ⟨hotherValue, oldOutput, hhiddenOld, hordinaryOld⟩ :=
      hsynced other otherValue hrevealedOld
    refine ⟨hotherValue, oldOutput, ?_, ?_⟩
    · rw [Function.update_of_ne (by simp)]
      exact hhiddenOld
    · rw [Function.update_of_ne]
      · exact hordinaryOld
      · intro hkey
        apply heq
        apply hiddenInput_injective parameter table
        exact SplitHashKey.ordinary.inj hkey

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

theorem revealFtsSecret_run_eq (parameter : PublicParameter)
    (coordinate : Coordinate) (cache : SplitHashCache) :
    (revealFtsSecret parameter coordinate).run cache =
      AdaptiveRevealProbe.revealQuery coordinate >>= fun value =>
        (splitHashQuery (.hiddenLeaf coordinate)).run cache >>= fun result =>
          pure (value, Function.update result.2
            (.ordinary ((⟨coordinate.1, coordinate.2.1, coordinate.2.2,
              value⟩ : FtsSecretProbe).input parameter)) (some result.1)) := by
  simp [revealFtsSecret, StateT.run_bind]

theorem runDetailed_revealFtsSecret_hidden
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache) (coordinate : Coordinate) (output : HashOutput)
    (hrevealed : state.revealed coordinate = none)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hhidden : cache (.hiddenLeaf coordinate) = some output) :
    AdaptiveRevealProbe.runDetailed table state fuel
        ((revealFtsSecret parameter coordinate).run cache) =
      pure (.done false (state.install coordinate (table coordinate))
        (table coordinate, Function.update cache
          (.ordinary (hiddenInput parameter table coordinate)) (some output))) := by
  rw [revealFtsSecret_run_eq, AdaptiveRevealProbe.revealQuery]
  change AdaptiveRevealProbe.runDetailed table state fuel
      ((liftM (OracleSpec.query (spec := AdaptiveRevealProbe.World Coordinate)
        (.reveal coordinate)) :
          OracleComp (AdaptiveRevealProbe.World Coordinate) Digest) >>= fun value =>
        (splitHashQuery (.hiddenLeaf coordinate)).run cache >>= fun result =>
          pure (value, Function.update result.2
            (.ordinary ((⟨coordinate.1, coordinate.2.1, coordinate.2.2,
              value⟩ : FtsSecretProbe).input parameter)) (some result.1))) = _
  rw [AdaptiveRevealProbe.runDetailed_reveal_query_bind, hrevealed]
  rw [if_neg (AdaptiveRevealProbe.not_mem_pending_of_tableHits_eq_false
    state table coordinate hclean)]
  rw [splitHashQuery_run_eq, hhidden, pure_bind]
  simp only [hiddenInput, tableProbe]
  simp [AdaptiveRevealProbe.runDetailed,
    AdaptiveRevealProbe.tableHits_install_eq_false state table coordinate
      (table coordinate) hclean]

theorem runDetailed_revealFtsSecret_revealed
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache) (coordinate : Coordinate) (value : Digest)
    (output : HashOutput)
    (hrevealed : state.revealed coordinate = some value)
    (hvalue : value = table coordinate)
    (hhidden : cache (.hiddenLeaf coordinate) = some output)
    (hordinary : cache (.ordinary (hiddenInput parameter table coordinate)) = some output)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) :
    AdaptiveRevealProbe.runDetailed table state fuel
        ((revealFtsSecret parameter coordinate).run cache) =
      pure (.done false state (table coordinate, cache)) := by
  rw [revealFtsSecret_run_eq, AdaptiveRevealProbe.revealQuery]
  change AdaptiveRevealProbe.runDetailed table state fuel
      ((liftM (OracleSpec.query (spec := AdaptiveRevealProbe.World Coordinate)
        (.reveal coordinate)) :
          OracleComp (AdaptiveRevealProbe.World Coordinate) Digest) >>= fun revealedValue =>
        (splitHashQuery (.hiddenLeaf coordinate)).run cache >>= fun result =>
          pure (revealedValue, Function.update result.2
            (.ordinary ((⟨coordinate.1, coordinate.2.1, coordinate.2.2,
              revealedValue⟩ : FtsSecretProbe).input parameter)) (some result.1))) = _
  rw [AdaptiveRevealProbe.runDetailed_reveal_query_bind, hrevealed]
  simp only
  rw [splitHashQuery_run_eq, hhidden]
  simp only [pure_bind]
  simp only [hvalue]
  have hupdate : Function.update cache
      (.ordinary ((⟨coordinate.1, coordinate.2.1, coordinate.2.2,
        table coordinate⟩ : FtsSecretProbe).input parameter)) (some output) = cache := by
    have hordinary' : cache
        (.ordinary ((⟨coordinate.1, coordinate.2.1, coordinate.2.2,
          table coordinate⟩ : FtsSecretProbe).input parameter)) = some output := by
      simpa only [hiddenInput, tableProbe] using hordinary
    conv_lhs => rw [← hordinary']
    exact Function.update_eq_self _ _
  rw [hupdate]
  simp [AdaptiveRevealProbe.runDetailed, hclean]

theorem runDetailed_splitHashQuery_hiddenLeaf
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache) (coordinate : Coordinate)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) :
    projectDetailedCache parameter table <$>
        AdaptiveRevealProbe.runDetailed table state fuel
          ((splitHashQuery (.hiddenLeaf coordinate)).run cache) =
      some <$> (randomOracle (hiddenInput parameter table coordinate)).run
        (mergedCache parameter table cache) := by
  rw [splitHashQuery_run_eq]
  cases hlookup : cache (.hiddenLeaf coordinate) with
  | some output =>
      have hmerged : mergedCache parameter table cache
          (hiddenInput parameter table coordinate) = some output := by
        rw [mergedCache_hiddenInput, hlookup]
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hmerged]
      simp [AdaptiveRevealProbe.runDetailed, projectDetailedCache, hclean]
  | none =>
      have hmerged : mergedCache parameter table cache
          (hiddenInput parameter table coordinate) = none := by
        rw [mergedCache_hiddenInput, hlookup]
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hmerged,
        AdaptiveRevealProbe.hashOutputQuery,
        AdaptiveRevealProbe.runDetailed_hashOutput_query_bind]
      have hsampler :
          uniformSampleImpl (spec := HashSpec)
            (hiddenInput parameter table coordinate) =
            AdaptiveRevealProbe.sampleHashOutput := by
        unfold AdaptiveRevealProbe.sampleHashOutput uniformSampleImpl
        rfl
      let finish := fun output : HashOutput =>
        (output, (mergedCache parameter table cache).cacheQuery
          (hiddenInput parameter table coordinate) output)
      calc
        projectDetailedCache parameter table <$>
            (do
              let output ← liftM AdaptiveRevealProbe.sampleHashOutput
              AdaptiveRevealProbe.runDetailed table state fuel
                (pure (output, Function.update cache (.hiddenLeaf coordinate) (some output)))) =
          some <$> finish <$> AdaptiveRevealProbe.sampleHashOutput := by
            simp only [AdaptiveRevealProbe.runDetailed,
              OracleComp.construct_pure, hclean, map_eq_bind_pure_comp, bind_assoc,
              pure_bind]
            apply bind_congr
            intro output
            simp only [Function.comp_apply, projectDetailedCache, pure_bind, finish]
            rw [mergedCache_update_hiddenLeaf]
        _ = some <$> finish <$>
            uniformSampleImpl (spec := HashSpec)
              (hiddenInput parameter table coordinate) := by
          rw [hsampler]

theorem runDetailed_splitHashQuery_ordinary
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache) (input : HashInput)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hordinary : IsOrdinaryInput parameter table input) :
    projectDetailedCache parameter table <$>
        AdaptiveRevealProbe.runDetailed table state fuel
          ((splitHashQuery (.ordinary input)).run cache) =
      some <$> (randomOracle input).run (mergedCache parameter table cache) := by
  rw [splitHashQuery_run_eq]
  cases hlookup : cache (.ordinary input) with
  | some output =>
      have hmerged : mergedCache parameter table cache input = some output := by
        rw [mergedCache_eq_ordinary_of_isOrdinary parameter table cache input hordinary,
          hlookup]
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hmerged]
      simp [AdaptiveRevealProbe.runDetailed, projectDetailedCache, hclean]
  | none =>
      have hmerged : mergedCache parameter table cache input = none := by
        rw [mergedCache_eq_ordinary_of_isOrdinary parameter table cache input hordinary,
          hlookup]
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hmerged,
        AdaptiveRevealProbe.hashOutputQuery,
        AdaptiveRevealProbe.runDetailed_hashOutput_query_bind]
      have hsampler :
          uniformSampleImpl (spec := HashSpec) input =
            AdaptiveRevealProbe.sampleHashOutput := by
        unfold AdaptiveRevealProbe.sampleHashOutput uniformSampleImpl
        rfl
      let finish := fun output : HashOutput =>
        (output, (mergedCache parameter table cache).cacheQuery input output)
      calc
        projectDetailedCache parameter table <$>
            (do
              let output ← liftM AdaptiveRevealProbe.sampleHashOutput
              AdaptiveRevealProbe.runDetailed table state fuel
                (pure (output, Function.update cache (.ordinary input) (some output)))) =
          some <$> finish <$> AdaptiveRevealProbe.sampleHashOutput := by
            simp only [AdaptiveRevealProbe.runDetailed, OracleComp.construct_pure,
              hclean, map_eq_bind_pure_comp, bind_assoc, pure_bind]
            apply bind_congr
            intro output
            simp only [Function.comp_apply, projectDetailedCache, pure_bind, finish]
            rw [mergedCache_update_ordinary parameter table cache input output hordinary]
        _ = some <$> finish <$> uniformSampleImpl (spec := HashSpec) input := by
          rw [hsampler]

theorem runDetailed_ordinaryTweakableHash
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache) (domain : HashDomain) (payload : HashInput)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hordinary : IsOrdinaryInput parameter table
      (tweakableHashInput parameter domain payload)) :
    projectDetailedCache parameter table <$>
        AdaptiveRevealProbe.runDetailed table state fuel
          ((ordinaryTweakableHash parameter domain payload).run cache) =
      some <$> (simulateQ (randomOracle : QueryImpl HashSpec _)
        (tweakableHash parameter domain payload)).run
          (mergedCache parameter table cache) := by
  let input := tweakableHashInput parameter domain payload
  have hmergedEq : mergedCache parameter table cache input = cache (.ordinary input) :=
    mergedCache_eq_ordinary_of_isOrdinary parameter table cache input hordinary
  have hqueryRun :
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (oracleHash input)).run (mergedCache parameter table cache) =
      (randomOracle input).run (mergedCache parameter table cache) := by
    change (simulateQ (randomOracle : QueryImpl HashSpec _)
      (liftM (HashSpec.query input))).run (mergedCache parameter table cache) = _
    rw [simulateQ_spec_query]
  unfold ordinaryTweakableHash tweakableHash
  rw [StateT.run_bind, splitHashQuery_run_eq,
    simulateQ_bind, StateT.run_bind, hqueryRun]
  simp only [simulateQ_pure, StateT.run_pure]
  cases hlookup : cache (.ordinary input) with
  | some output =>
      have hmerged : mergedCache parameter table cache input = some output := by
        rw [hmergedEq, hlookup]
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hmerged]
      simp [AdaptiveRevealProbe.runDetailed, projectDetailedCache, hclean, input]
  | none =>
      have hmerged : mergedCache parameter table cache input = none := by
        rw [hmergedEq, hlookup]
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hmerged]
      change projectDetailedCache parameter table <$>
          AdaptiveRevealProbe.runDetailed table state fuel
            (AdaptiveRevealProbe.hashOutputQuery (Coordinate := Coordinate) >>= fun output =>
              pure (truncateHash output,
                Function.update cache (.ordinary input) (some output))) = _
      rw [AdaptiveRevealProbe.hashOutputQuery,
        AdaptiveRevealProbe.runDetailed_hashOutput_query_bind]
      have hsampler : uniformSampleImpl (spec := HashSpec) input =
          AdaptiveRevealProbe.sampleHashOutput := by
        unfold AdaptiveRevealProbe.sampleHashOutput uniformSampleImpl
        rfl
      let finish := fun output : HashOutput =>
        (truncateHash output,
          (mergedCache parameter table cache).cacheQuery input output)
      calc
        projectDetailedCache parameter table <$>
            (do
              let output ← liftM AdaptiveRevealProbe.sampleHashOutput
              AdaptiveRevealProbe.runDetailed table state fuel
                (pure (truncateHash output,
                  Function.update cache (.ordinary input) (some output)))) =
          some <$> finish <$> AdaptiveRevealProbe.sampleHashOutput := by
            simp only [AdaptiveRevealProbe.runDetailed, OracleComp.construct_pure,
              hclean, map_eq_bind_pure_comp, bind_assoc, pure_bind]
            apply bind_congr
            intro output
            simp only [Function.comp_apply, projectDetailedCache, pure_bind, finish]
            rw [mergedCache_update_ordinary parameter table cache input output hordinary]
        _ = some <$> finish <$> uniformSampleImpl (spec := HashSpec) input := by
          rw [hsampler]
        _ = some <$> (do
            let result ← (fun output : HashOutput =>
              (output, (mergedCache parameter table cache).cacheQuery input output)) <$>
                uniformSampleImpl (spec := HashSpec) input
            pure (truncateHash result.1, result.2)) := by
          simp [map_eq_bind_pure_comp, finish]

theorem runDetailed_hiddenFtsLeafHash
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache) (coordinate : Coordinate)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) :
    projectDetailedCache parameter table <$>
        AdaptiveRevealProbe.runDetailed table state fuel
          ((hiddenFtsLeafHash parameter coordinate).run cache) =
      some <$> (simulateQ (randomOracle : QueryImpl HashSpec _)
        (ftsLeafHash parameter coordinate.1 coordinate.2.1 coordinate.2.2
          (table coordinate))).run (mergedCache parameter table cache) := by
  let input := hiddenInput parameter table coordinate
  have hqueryRun :
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (oracleHash input)).run (mergedCache parameter table cache) =
      (randomOracle input).run (mergedCache parameter table cache) := by
    change (simulateQ (randomOracle : QueryImpl HashSpec _)
      (liftM (HashSpec.query input))).run (mergedCache parameter table cache) = _
    rw [simulateQ_spec_query]
  have hinput : tweakableHashInput parameter
      (.ftsLeaf coordinate.1 coordinate.2.1 coordinate.2.2)
        (digestBytes (table coordinate)) = input := by
    rfl
  unfold hiddenFtsLeafHash ftsLeafHash tweakableHash
  rw [StateT.run_bind, splitHashQuery_run_eq,
    simulateQ_bind, StateT.run_bind]
  change _ = some <$> (do
    let result ← (simulateQ (randomOracle : QueryImpl HashSpec _)
      (oracleHash input)).run (mergedCache parameter table cache)
    pure (truncateHash result.1, result.2))
  rw [hqueryRun]
  simp only [StateT.run_pure]
  cases hlookup : cache (.hiddenLeaf coordinate) with
  | some output =>
      have hmerged : mergedCache parameter table cache input = some output := by
        change mergedCache parameter table cache
          (hiddenInput parameter table coordinate) = some output
        rw [mergedCache_hiddenInput, hlookup]
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hmerged]
      simp [AdaptiveRevealProbe.runDetailed, projectDetailedCache, hclean, input]
  | none =>
      have hmerged : mergedCache parameter table cache input = none := by
        change mergedCache parameter table cache
          (hiddenInput parameter table coordinate) = none
        rw [mergedCache_hiddenInput, hlookup]
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hmerged]
      change projectDetailedCache parameter table <$>
          AdaptiveRevealProbe.runDetailed table state fuel
            (AdaptiveRevealProbe.hashOutputQuery (Coordinate := Coordinate) >>= fun output =>
              pure (truncateHash output,
                Function.update cache (.hiddenLeaf coordinate) (some output))) = _
      rw [AdaptiveRevealProbe.hashOutputQuery,
        AdaptiveRevealProbe.runDetailed_hashOutput_query_bind]
      have hsampler : uniformSampleImpl (spec := HashSpec) input =
          AdaptiveRevealProbe.sampleHashOutput := by
        unfold AdaptiveRevealProbe.sampleHashOutput uniformSampleImpl
        rfl
      let finish := fun output : HashOutput =>
        (truncateHash output,
          (mergedCache parameter table cache).cacheQuery input output)
      calc
        projectDetailedCache parameter table <$>
            (do
              let output ← liftM AdaptiveRevealProbe.sampleHashOutput
              AdaptiveRevealProbe.runDetailed table state fuel
                (pure (truncateHash output,
                  Function.update cache (.hiddenLeaf coordinate) (some output)))) =
          some <$> finish <$> AdaptiveRevealProbe.sampleHashOutput := by
            simp only [AdaptiveRevealProbe.runDetailed, OracleComp.construct_pure,
              hclean, map_eq_bind_pure_comp, bind_assoc, pure_bind]
            apply bind_congr
            intro output
            simp only [Function.comp_apply, projectDetailedCache, pure_bind, finish]
            rw [mergedCache_update_hiddenLeaf]
        _ = some <$> finish <$> uniformSampleImpl (spec := HashSpec) input := by
          rw [hsampler]
        _ = some <$> (do
            let result ← (fun output : HashOutput =>
              (output, (mergedCache parameter table cache).cacheQuery input output)) <$>
                uniformSampleImpl (spec := HashSpec) input
            pure (truncateHash result.1, result.2)) := by
          simp [map_eq_bind_pure_comp, finish]

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

theorem runDetailed_probingHashQuery_hidden_miss
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (cache : SplitHashCache) (input : HashInput) (probe : FtsSecretProbe)
    (hdecode : decodeProbe? parameter input = some probe)
    (hrevealed : state.revealed (probe.index, probe.tree, probe.leafIdx) = none)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hmiss : table (probe.index, probe.tree, probe.leafIdx) ≠ probe.candidate) :
    projectDetailedCache parameter table <$>
        AdaptiveRevealProbe.runDetailed table state (remaining + 1)
          ((probingHashQuery parameter input).run cache) =
      some <$> (randomOracle input).run (mergedCache parameter table cache) := by
  rw [probingHashQuery_run_eq, hdecode]
  change projectDetailedCache parameter table <$>
      AdaptiveRevealProbe.runDetailed table state (remaining + 1)
        ((liftM (OracleSpec.query
          (spec := AdaptiveRevealProbe.World Coordinate)
          (.probe (probe.index, probe.tree, probe.leafIdx) probe.candidate)) :
            OracleComp (AdaptiveRevealProbe.World Coordinate) Unit) >>= fun _ =>
          (splitHashQuery (.ordinary input)).run cache) = _
  rw [AdaptiveRevealProbe.runDetailed_probe_query_bind, hrevealed]
  exact runDetailed_splitHashQuery_ordinary parameter table
    (state.addPending (probe.index, probe.tree, probe.leafIdx) probe.candidate)
    remaining cache input
    (AdaptiveRevealProbe.tableHits_addPending_eq_false state table
      (probe.index, probe.tree, probe.leafIdx) probe.candidate hclean hmiss)
    (isOrdinaryInput_of_decode_miss parameter table input probe hdecode hmiss.symm)

theorem runDetailed_probingHashQuery_decode_none
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache) (input : HashInput)
    (hdecode : decodeProbe? parameter input = none)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) :
    projectDetailedCache parameter table <$>
        AdaptiveRevealProbe.runDetailed table state fuel
          ((probingHashQuery parameter input).run cache) =
      some <$> (randomOracle input).run (mergedCache parameter table cache) := by
  rw [probingHashQuery_run_eq, hdecode]
  exact runDetailed_splitHashQuery_ordinary parameter table state fuel cache input hclean
    (isOrdinaryInput_of_decode_none parameter table input hdecode)

theorem runDetailed_probingHashQuery_revealed_miss
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (cache : SplitHashCache) (input : HashInput) (probe : FtsSecretProbe)
    (hdecode : decodeProbe? parameter input = some probe)
    (value : Digest)
    (hrevealed : state.revealed (probe.index, probe.tree, probe.leafIdx) = some value)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hmiss : table (probe.index, probe.tree, probe.leafIdx) ≠ probe.candidate) :
    projectDetailedCache parameter table <$>
        AdaptiveRevealProbe.runDetailed table state (remaining + 1)
          ((probingHashQuery parameter input).run cache) =
      some <$> (randomOracle input).run (mergedCache parameter table cache) := by
  rw [probingHashQuery_run_eq, hdecode]
  change projectDetailedCache parameter table <$>
      AdaptiveRevealProbe.runDetailed table state (remaining + 1)
        ((liftM (OracleSpec.query
          (spec := AdaptiveRevealProbe.World Coordinate)
          (.probe (probe.index, probe.tree, probe.leafIdx) probe.candidate)) :
            OracleComp (AdaptiveRevealProbe.World Coordinate) Unit) >>= fun _ =>
          (splitHashQuery (.ordinary input)).run cache) = _
  rw [AdaptiveRevealProbe.runDetailed_probe_query_bind, hrevealed]
  exact runDetailed_splitHashQuery_ordinary parameter table state remaining cache input hclean
    (isOrdinaryInput_of_decode_miss parameter table input probe hdecode hmiss.symm)

theorem runDetailed_probingHashQuery_revealed_hit
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (cache : SplitHashCache) (input : HashInput) (probe : FtsSecretProbe)
    (hdecode : decodeProbe? parameter input = some probe)
    (value : Digest)
    (hrevealed : state.revealed (probe.index, probe.tree, probe.leafIdx) = some value)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hhit : table (probe.index, probe.tree, probe.leafIdx) = probe.candidate)
    (hsynced : RevealedSynced parameter table state cache) :
    projectDetailedCache parameter table <$>
        AdaptiveRevealProbe.runDetailed table state (remaining + 1)
          ((probingHashQuery parameter input).run cache) =
      some <$> (randomOracle input).run (mergedCache parameter table cache) := by
  let coordinate : Coordinate := (probe.index, probe.tree, probe.leafIdx)
  have hprobe : probe = tableProbe table coordinate :=
    probe_eq_tableProbe_of_candidate table probe hhit.symm
  have hinput : input = hiddenInput parameter table coordinate := by
    have hprobeInput := (decodeProbe?_eq_some_iff parameter input probe).1 hdecode
    rw [hprobe] at hprobeInput
    exact hprobeInput.symm
  obtain ⟨hvalue, output, hhidden, hordinary⟩ :=
    hsynced coordinate value (by simpa only [coordinate] using hrevealed)
  rw [probingHashQuery_run_eq, hdecode]
  change projectDetailedCache parameter table <$>
      AdaptiveRevealProbe.runDetailed table state (remaining + 1)
        ((liftM (OracleSpec.query
          (spec := AdaptiveRevealProbe.World Coordinate)
          (.probe coordinate probe.candidate)) :
            OracleComp (AdaptiveRevealProbe.World Coordinate) Unit) >>= fun _ =>
          (splitHashQuery (.ordinary input)).run cache) = _
  rw [AdaptiveRevealProbe.runDetailed_probe_query_bind]
  simp only [coordinate, hrevealed]
  have hmerged : mergedCache parameter table cache
      (hiddenInput parameter table coordinate) = some output := by
    rw [mergedCache_hiddenInput, hhidden]
  rw [splitHashQuery_run_eq, hinput, hordinary,
    OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hmerged]
  simp [AdaptiveRevealProbe.runDetailed, projectDetailedCache, hclean]

theorem runDetailed_probingHashQuery_hidden_hit
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (cache : SplitHashCache) (input : HashInput) (probe : FtsSecretProbe)
    (hdecode : decodeProbe? parameter input = some probe)
    (hrevealed : state.revealed (probe.index, probe.tree, probe.leafIdx) = none)
    (hhit : table (probe.index, probe.tree, probe.leafIdx) = probe.candidate)
    (result : AdaptiveRevealProbe.DetailedResult Coordinate
      (HashOutput × SplitHashCache))
    (hresult : result ∈ support
      (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
        ((probingHashQuery parameter input).run cache))) :
    result.hit = true := by
  rw [probingHashQuery_run_eq, hdecode] at hresult
  change result ∈ support (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
      ((liftM (OracleSpec.query
        (spec := AdaptiveRevealProbe.World Coordinate)
        (.probe (probe.index, probe.tree, probe.leafIdx) probe.candidate)) :
          OracleComp (AdaptiveRevealProbe.World Coordinate) Unit) >>= fun _ =>
        (splitHashQuery (.ordinary input)).run cache)) at hresult
  rw [AdaptiveRevealProbe.runDetailed_probe_query_bind, hrevealed,
    splitHashQuery_run_eq] at hresult
  have htableHits := AdaptiveRevealProbe.tableHits_addPending_eq_true state table
    (probe.index, probe.tree, probe.leafIdx) probe.candidate hhit
  cases hlookup : cache (.ordinary input) with
  | some output =>
      simp [hlookup, AdaptiveRevealProbe.runDetailed, htableHits] at hresult
      subst result
      rfl
  | none =>
      simp only [hlookup] at hresult
      rw [AdaptiveRevealProbe.hashOutputQuery,
        AdaptiveRevealProbe.runDetailed_hashOutput_query_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨output, houtput, hresult⟩ := hresult
      simp [AdaptiveRevealProbe.runDetailed, htableHits] at hresult
      subst result
      rfl

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

def StateFree
    (computation : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ cache, (computation.run cache).IsQueryBoundP
    (AdaptiveRevealProbe.IsStateful (Coordinate := Coordinate)) 0

theorem StateFree.pure (value : alpha) :
    StateFree (pure value : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha) := by
  intro cache
  simp

theorem StateFree.bind
    {left : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) beta}
    (hleft : StateFree left) (hnext : ∀ value, StateFree (next value)) :
    StateFree (left >>= next) := by
  intro cache
  rw [StateT.run_bind]
  have hbound := isQueryBoundP_bind (n := 0) (m := 0) (hleft cache)
    (fun result _ => hnext result.1 result.2)
  simpa using hbound

theorem StateFree.map
    {computation : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha}
    (hcomputation : StateFree computation) (transform : alpha → beta) :
    StateFree (transform <$> computation) := by
  rw [map_eq_bind_pure_comp]
  exact hcomputation.bind fun value => StateFree.pure (transform value)

theorem splitHashQuery_stateFree (key : SplitHashKey) :
    StateFree (splitHashQuery key) := by
  intro cache
  rw [splitHashQuery_run_eq]
  cases hlookup : cache key with
  | some output => simp
  | none =>
      change (AdaptiveRevealProbe.hashOutputQuery (Coordinate := Coordinate) >>= fun output =>
        pure (output, Function.update cache key (some output))).IsQueryBoundP
          (AdaptiveRevealProbe.IsStateful (Coordinate := Coordinate)) 0
      rw [AdaptiveRevealProbe.hashOutputQuery,
        OracleComp.isQueryBoundP_query_bind_iff]
      constructor
      · simp [AdaptiveRevealProbe.IsStateful]
      · intro output
        trivial

theorem ordinaryTweakableHash_stateFree (parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) :
    StateFree (ordinaryTweakableHash parameter domain payload) := by
  unfold ordinaryTweakableHash
  exact (splitHashQuery_stateFree (.ordinary
    (tweakableHashInput parameter domain payload))).bind fun output =>
      StateFree.pure (truncateHash output)

theorem hiddenFtsLeafHash_stateFree (parameter : PublicParameter)
    (coordinate : Coordinate) : StateFree (hiddenFtsLeafHash parameter coordinate) := by
  unfold hiddenFtsLeafHash
  exact (splitHashQuery_stateFree (.hiddenLeaf coordinate)).bind fun output =>
    StateFree.pure (truncateHash output)

theorem sequenceFin_stateFree {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha)
    (hcomputation : ∀ index, StateFree (computation index)) :
    StateFree (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact StateFree.pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomputation 0).bind fun head =>
        (ih (fun index => computation index.succ)
          (fun index => hcomputation index.succ)).bind fun tail =>
            StateFree.pure (Fin.cases head tail : Fin (n + 1) → alpha)

theorem maskedFtsNode_stateFree (parameter : PublicParameter) (index : Index)
    (tree : FtsTree) (level nodeIdx : Nat) :
    StateFree (maskedFtsNode parameter index tree level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      exact hiddenFtsLeafHash_stateFree parameter
        (index, tree, ftsLeafOfNat nodeIdx)
  | succ level ih =>
      rw [maskedFtsNode]
      exact (ih (2 * nodeIdx)).bind fun left =>
        (ih (2 * nodeIdx + 1)).bind fun right =>
          ordinaryTweakableHash_stateFree parameter
            (.ftsNode index tree (level + 1) nodeIdx) (nodePayload left right)

theorem maskedFtsKey_stateFree (parameter : PublicParameter) (index : Index) :
    StateFree (maskedFtsKey parameter index) := by
  unfold maskedFtsKey
  exact (sequenceFin_stateFree
    (fun tree => maskedFtsNode parameter index tree ftsTreeHeight 0)
    (fun tree => maskedFtsNode_stateFree parameter index tree ftsTreeHeight 0)).bind
      fun roots => ordinaryTweakableHash_stateFree parameter (.ftsRoots index)
        (ftsRootsPayload roots)

theorem maskedFtsOpen_stateFree (parameter : PublicParameter) (index : Index)
    (leaves : DigestTree → FtsLeaf) :
    StateFree (maskedFtsOpen parameter index leaves) := by
  unfold maskedFtsOpen
  apply sequenceFin_stateFree
  intro tree
  apply sequenceFin_stateFree
  intro level
  exact maskedFtsNode_stateFree parameter index tree level.val
    (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)

def Coupled (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (masked : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha)
    (ordinary : StateT (QueryCache HashSpec) ProbComp alpha) : Prop :=
  ∀ cache,
    projectDetailedCache parameter table <$>
        AdaptiveRevealProbe.runDetailed table state fuel (masked.run cache) =
      some <$> ordinary.run (mergedCache parameter table cache)

def CoupledAt (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (masked : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha)
    (ordinary : StateT (QueryCache HashSpec) ProbComp alpha)
    (cache : SplitHashCache) : Prop :=
  projectDetailedCache parameter table <$>
      AdaptiveRevealProbe.runDetailed table state fuel (masked.run cache) =
    some <$> ordinary.run (mergedCache parameter table cache)

theorem Coupled.coupledAt
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {state : AdaptiveRevealProbe.State Coordinate} {fuel : Nat}
    {masked : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha}
    {ordinary : StateT (QueryCache HashSpec) ProbComp alpha}
    (hcoupled : Coupled parameter table state fuel masked ordinary)
    (cache : SplitHashCache) :
    CoupledAt parameter table state fuel masked ordinary cache :=
  hcoupled cache

theorem CoupledAt.bind_probeFree
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {state : AdaptiveRevealProbe.State Coordinate} {fuel : Nat}
    {left : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) beta}
    {ordinaryLeft : StateT (QueryCache HashSpec) ProbComp alpha}
    {ordinaryNext : alpha → StateT (QueryCache HashSpec) ProbComp beta}
    {cache : SplitHashCache}
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hprobeFree : ProbeFree left)
    (hleft : CoupledAt parameter table state fuel left ordinaryLeft cache)
    (hnext : ∀ finalState value finalCache,
      .done false finalState (value, finalCache) ∈
          support (AdaptiveRevealProbe.runDetailed table state fuel (left.run cache)) →
        CoupledAt parameter table finalState fuel (next value) (ordinaryNext value)
          finalCache) :
    CoupledAt parameter table state fuel (left >>= next)
      (ordinaryLeft >>= ordinaryNext) cache := by
  let resume : Option (alpha × QueryCache HashSpec) →
      ProbComp (Option (beta × QueryCache HashSpec))
    | none => pure none
    | some (value, ordinaryCache) => some <$> (ordinaryNext value).run ordinaryCache
  unfold CoupledAt at hleft ⊢
  rw [StateT.run_bind, StateT.run_bind,
    AdaptiveRevealProbe.runDetailed_bind_probeFree table state fuel
      (left.run cache) (fun result => (next result.1).run result.2)
      (hprobeFree cache)]
  simp only [map_bind]
  refine (OracleComp.bind_congr_of_forall_mem_support
    (AdaptiveRevealProbe.runDetailed table state fuel (left.run cache))
    (g := fun result => resume (projectDetailedCache parameter table result)) ?_).trans ?_
  · intro result hresult
    obtain ⟨finalState, value, hresultEq, hfinalClean⟩ :=
      AdaptiveRevealProbe.runDetailed_probeFree_support table state fuel
        (left.run cache) (hprobeFree cache) hclean result hresult
    subst result
    simp only [projectDetailedCache, resume]
    exact hnext finalState value.1 value.2 hresult
  · rw [← bind_map_left, hleft]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind, resume]

theorem coupledAt_revealFtsSecret
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache) (coordinate : Coordinate)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache)
    (hhidden : ∃ output, cache (.hiddenLeaf coordinate) = some output) :
    CoupledAt parameter table state fuel (revealFtsSecret parameter coordinate)
      (pure (table coordinate) : StateT (QueryCache HashSpec) ProbComp Digest) cache := by
  unfold CoupledAt
  cases hrevealed : state.revealed coordinate with
  | none =>
      obtain ⟨output, hhidden⟩ := hhidden
      rw [runDetailed_revealFtsSecret_hidden parameter table state fuel cache coordinate output
        hrevealed hclean hhidden]
      simp only [map_pure, projectDetailedCache, StateT.run_pure]
      rw [mergedCache_update_hiddenInput_ordinary]
  | some value =>
      obtain ⟨hvalue, output, hhiddenCache, hordinaryCache⟩ :=
        hsynced coordinate value hrevealed
      rw [runDetailed_revealFtsSecret_revealed parameter table state fuel cache coordinate
        value output hrevealed hvalue hhiddenCache hordinaryCache hclean]
      simp [projectDetailedCache]

theorem revealedSynced_of_mem_runDetailed_revealFtsSecret
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (coordinate : Coordinate) (value : Digest)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache)
    (hhidden : ∃ output, cache (.hiddenLeaf coordinate) = some output)
    (hresult : .done false finalState (value, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((revealFtsSecret parameter coordinate).run cache))) :
    RevealedSynced parameter table finalState finalCache := by
  cases hrevealed : state.revealed coordinate with
  | none =>
      obtain ⟨output, hhiddenCache⟩ := hhidden
      rw [runDetailed_revealFtsSecret_hidden parameter table state fuel cache coordinate output
        hrevealed hclean hhiddenCache] at hresult
      simp only [support_pure, Set.mem_singleton_iff,
        AdaptiveRevealProbe.DetailedResult.done.injEq] at hresult
      obtain ⟨hfinalState, hvalueCache⟩ := hresult.2
      subst finalState
      cases hvalueCache
      exact RevealedSynced.install hsynced coordinate (table coordinate) output rfl hhiddenCache
  | some revealedValue =>
      obtain ⟨hvalue, output, hhiddenCache, hordinaryCache⟩ :=
        hsynced coordinate revealedValue hrevealed
      rw [runDetailed_revealFtsSecret_revealed parameter table state fuel cache coordinate
        revealedValue output hrevealed hvalue hhiddenCache hordinaryCache hclean] at hresult
      simp only [support_pure, Set.mem_singleton_iff,
        AdaptiveRevealProbe.DetailedResult.done.injEq] at hresult
      obtain ⟨hfinalState, hvalueCache⟩ := hresult.2
      subst finalState
      cases hvalueCache
      exact hsynced

theorem Coupled.bind
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {state : AdaptiveRevealProbe.State Coordinate} {fuel : Nat}
    {left : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) beta}
    {ordinaryLeft : StateT (QueryCache HashSpec) ProbComp alpha}
    {ordinaryNext : alpha → StateT (QueryCache HashSpec) ProbComp beta}
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hstateFree : StateFree left)
    (hleft : Coupled parameter table state fuel left ordinaryLeft)
    (hnext : ∀ value, Coupled parameter table state fuel (next value)
      (ordinaryNext value)) :
    Coupled parameter table state fuel (left >>= next)
      (ordinaryLeft >>= ordinaryNext) := by
  intro cache
  let resume : Option (alpha × QueryCache HashSpec) →
      ProbComp (Option (beta × QueryCache HashSpec))
    | none => pure none
    | some (value, ordinaryCache) => some <$> (ordinaryNext value).run ordinaryCache
  rw [StateT.run_bind, StateT.run_bind,
    AdaptiveRevealProbe.runDetailed_bind_stateFree table state fuel
      (left.run cache) (fun result => (next result.1).run result.2)
      (hstateFree cache)]
  simp only [map_bind]
  refine (OracleComp.bind_congr_of_forall_mem_support
    (AdaptiveRevealProbe.runDetailed table state fuel (left.run cache))
    (g := fun result => resume (projectDetailedCache parameter table result)) ?_).trans ?_
  · intro result hresult
    obtain ⟨value, hresultEq⟩ :=
      AdaptiveRevealProbe.runDetailed_stateFree_support table state fuel
        (left.run cache) (hstateFree cache) hclean result hresult
    subst result
    simp only [projectDetailedCache, resume]
    exact hnext value.1 value.2
  · rw [← bind_map_left, hleft cache]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind, resume]

theorem Coupled.bind_probeFree
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {state : AdaptiveRevealProbe.State Coordinate} {fuel : Nat}
    {left : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) beta}
    {ordinaryLeft : StateT (QueryCache HashSpec) ProbComp alpha}
    {ordinaryNext : alpha → StateT (QueryCache HashSpec) ProbComp beta}
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hprobeFree : ProbeFree left)
    (hleft : Coupled parameter table state fuel left ordinaryLeft)
    (hnext : ∀ finalState value,
      AdaptiveRevealProbe.tableHits finalState table = false →
        Coupled parameter table finalState fuel (next value) (ordinaryNext value)) :
    Coupled parameter table state fuel (left >>= next)
      (ordinaryLeft >>= ordinaryNext) := by
  intro cache
  let resume : Option (alpha × QueryCache HashSpec) →
      ProbComp (Option (beta × QueryCache HashSpec))
    | none => pure none
    | some (value, ordinaryCache) => some <$> (ordinaryNext value).run ordinaryCache
  rw [StateT.run_bind, StateT.run_bind,
    AdaptiveRevealProbe.runDetailed_bind_probeFree table state fuel
      (left.run cache) (fun result => (next result.1).run result.2)
      (hprobeFree cache)]
  simp only [map_bind]
  refine (OracleComp.bind_congr_of_forall_mem_support
    (AdaptiveRevealProbe.runDetailed table state fuel (left.run cache))
    (g := fun result => resume (projectDetailedCache parameter table result)) ?_).trans ?_
  · intro result hresult
    obtain ⟨finalState, value, hresultEq, hfinalClean⟩ :=
      AdaptiveRevealProbe.runDetailed_probeFree_support table state fuel
        (left.run cache) (hprobeFree cache) hclean result hresult
    subst result
    simp only [projectDetailedCache, resume]
    exact hnext finalState value.1 hfinalClean value.2
  · rw [← bind_map_left, hleft cache]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind, resume]

theorem Coupled.pure
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (value : alpha) :
    Coupled parameter table state fuel
      (pure value : StateT SplitHashCache
        (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha)
      (pure value : StateT (QueryCache HashSpec) ProbComp alpha) := by
  intro cache
  simp [AdaptiveRevealProbe.runDetailed, projectDetailedCache, hclean]

theorem isOrdinaryInput_ftsNode (parameter : PublicParameter)
    (table : Coordinate → Digest) (index : Index) (tree : FtsTree)
    (level nodeIdx : Nat) (payload : HashInput)
    (hlevel : level < 2 ^ 32) (hnodeIdx : nodeIdx < 2 ^ 32) :
    IsOrdinaryInput parameter table
      (tweakableHashInput parameter (.ftsNode index tree level nodeIdx) payload) := by
  apply isOrdinaryInput_of_decode_none
  rw [decodeProbe?_eq_none_iff]
  intro probe heq
  have hdomain := (tweakableHashInput_injective parameter (by trivial)
    (by exact ⟨hlevel, hnodeIdx⟩) heq).1
  exact HashDomain.noConfusion hdomain

theorem isOrdinaryInput_ftsRoots (parameter : PublicParameter)
    (table : Coordinate → Digest) (index : Index) (payload : HashInput) :
    IsOrdinaryInput parameter table
      (tweakableHashInput parameter (.ftsRoots index) payload) := by
  apply isOrdinaryInput_of_decode_none
  rw [decodeProbe?_eq_none_iff]
  intro probe heq
  have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial) heq).1
  exact HashDomain.noConfusion hdomain

theorem coupled_hiddenFtsLeafHash
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (coordinate : Coordinate)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) :
    Coupled parameter table state fuel (hiddenFtsLeafHash parameter coordinate)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (ftsLeafHash parameter coordinate.1 coordinate.2.1 coordinate.2.2
          (table coordinate))) := by
  intro cache
  exact runDetailed_hiddenFtsLeafHash parameter table state fuel cache coordinate hclean

theorem coupled_ordinaryTweakableHash
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (domain : HashDomain) (payload : HashInput)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hordinary : IsOrdinaryInput parameter table
      (tweakableHashInput parameter domain payload)) :
    Coupled parameter table state fuel
      (ordinaryTweakableHash parameter domain payload)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (tweakableHash parameter domain payload)) := by
  intro cache
  exact runDetailed_ordinaryTweakableHash parameter table state fuel cache domain payload
    hclean hordinary

theorem coupled_maskedFtsNode
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (index : Index) (tree : FtsTree) (level nodeIdx : Nat)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hlevel : level ≤ ftsTreeHeight)
    (hnodeIdx : 2 ^ level * (nodeIdx + 1) ≤ 2 ^ ftsTreeHeight) :
    Coupled parameter table state fuel
      (maskedFtsNode parameter index tree level nodeIdx)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (ftsNode parameter index tree (fun leafIdx => table (index, tree, leafIdx))
          level nodeIdx)) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [maskedFtsNode, ftsNode_zero_eq]
      exact coupled_hiddenFtsLeafHash parameter table state fuel
        (index, tree, ftsLeafOfNat nodeIdx) hclean
  | succ level ih =>
      rw [maskedFtsNode, ftsNode_succ_eq, simulateQ_bind]
      have hlevelChild : level ≤ ftsTreeHeight := by omega
      have hleftNode : 2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ ftsTreeHeight := by
        rw [pow_succ] at hnodeIdx
        nlinarith [Nat.two_pow_pos level]
      have hrightNode : 2 ^ level * (2 * nodeIdx + 1 + 1) ≤ 2 ^ ftsTreeHeight := by
        rw [pow_succ] at hnodeIdx
        nlinarith [Nat.two_pow_pos level]
      have hlevelSmall : level + 1 < 2 ^ 32 := by
        norm_num [ftsTreeHeight] at hlevel ⊢
        omega
      have hnodeSmall : nodeIdx < 2 ^ 32 := by
        norm_num [ftsTreeHeight] at hnodeIdx ⊢
        nlinarith [Nat.two_pow_pos (level + 1)]
      refine Coupled.bind hclean
        (maskedFtsNode_stateFree parameter index tree level (2 * nodeIdx))
        (ih (2 * nodeIdx) hlevelChild hleftNode) ?_
      intro left
      rw [simulateQ_bind]
      exact Coupled.bind hclean
        (maskedFtsNode_stateFree parameter index tree level (2 * nodeIdx + 1))
        (ih (2 * nodeIdx + 1) hlevelChild hrightNode) fun right =>
          coupled_ordinaryTweakableHash parameter table state fuel
            (.ftsNode index tree (level + 1) nodeIdx) (nodePayload left right) hclean
            (isOrdinaryInput_ftsNode parameter table index tree (level + 1) nodeIdx
              (nodePayload left right) hlevelSmall hnodeSmall)

theorem coupled_sequenceFin {n : Nat}
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (masked : Fin n → StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha)
    (ordinary : Fin n → StateT (QueryCache HashSpec) ProbComp alpha)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hstateFree : ∀ position, StateFree (masked position))
    (hcoupled : ∀ position,
      Coupled parameter table state fuel (masked position) (ordinary position)) :
    Coupled parameter table state fuel (sequenceFin masked) (sequenceFin ordinary) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact Coupled.pure parameter table state fuel hclean Fin.elim0
  | succ n ih =>
      rw [sequenceFin, sequenceFin]
      exact Coupled.bind hclean (hstateFree 0) (hcoupled 0) fun head =>
        Coupled.bind hclean
          (sequenceFin_stateFree (fun position => masked position.succ)
            (fun position => hstateFree position.succ))
          (ih (fun position => masked position.succ)
            (fun position => ordinary position.succ)
            (fun position => hstateFree position.succ)
            (fun position => hcoupled position.succ)) fun tail =>
              by
                intro cache
                simp [AdaptiveRevealProbe.runDetailed, projectDetailedCache, hclean]

theorem simulateQ_randomOracle_sequenceFin {n : Nat}
    (computation : Fin n → OracleComp HashSpec alpha) :
    simulateQ (randomOracle : QueryImpl HashSpec _)
        (sequenceFin computation) =
      sequenceFin fun position =>
        simulateQ (randomOracle : QueryImpl HashSpec _) (computation position) := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      simp only [sequenceFin, simulateQ_bind, simulateQ_pure, ih]

theorem ftsOpen_node_bound (leafIdx : FtsLeaf) (level : Fin ftsTreeHeight) :
    2 ^ level.val * (Nat.xor (leafIdx.val / 2 ^ level.val) 1 + 1) ≤
      2 ^ ftsTreeHeight := by
  let bound := 2 ^ (ftsTreeHeight - level.val)
  have hlevel : level.val < ftsTreeHeight := level.isLt
  have hquotient : leafIdx.val / 2 ^ level.val < bound := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos level.val)).2
    change leafIdx.val < 2 ^ (ftsTreeHeight - level.val) * 2 ^ level.val
    rw [← pow_add]
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt hlevel)] using leafIdx.isLt
  have hboundEven : ∃ half, bound = 2 * half := by
    refine ⟨2 ^ (ftsTreeHeight - level.val - 1), ?_⟩
    change 2 ^ (ftsTreeHeight - level.val) = _
    rw [show ftsTreeHeight - level.val =
      (ftsTreeHeight - level.val - 1) + 1 by omega, pow_succ]
    exact Nat.mul_comm _ _
  have hsibling : Nat.xor (leafIdx.val / 2 ^ level.val) 1 < bound := by
    obtain ⟨parent, hcase⟩ := index_sibling_cases (leafIdx.val / 2 ^ level.val)
    obtain ⟨half, hbound⟩ := hboundEven
    rcases hcase with hcase | hcase <;> omega
  calc
    2 ^ level.val * (Nat.xor (leafIdx.val / 2 ^ level.val) 1 + 1) ≤
        2 ^ level.val * bound :=
      Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hsibling)
    _ = 2 ^ ftsTreeHeight := by
      change 2 ^ level.val * 2 ^ (ftsTreeHeight - level.val) = _
      rw [← pow_add]
      congr 1
      omega

theorem coupled_maskedFtsKey
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (index : Index)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) :
    Coupled parameter table state fuel (maskedFtsKey parameter index)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (ftsKey parameter index (fun tree leafIdx => table (index, tree, leafIdx)))) := by
  unfold maskedFtsKey ftsKey
  rw [simulateQ_bind, simulateQ_randomOracle_sequenceFin]
  exact Coupled.bind hclean
    (sequenceFin_stateFree
      (fun tree => maskedFtsNode parameter index tree ftsTreeHeight 0)
      (fun tree => maskedFtsNode_stateFree parameter index tree ftsTreeHeight 0))
    (coupled_sequenceFin parameter table state fuel
      (fun tree => maskedFtsNode parameter index tree ftsTreeHeight 0)
      (fun tree => simulateQ (randomOracle : QueryImpl HashSpec _)
        (ftsNode parameter index tree (fun leafIdx => table (index, tree, leafIdx))
          ftsTreeHeight 0)) hclean
      (fun tree => maskedFtsNode_stateFree parameter index tree ftsTreeHeight 0)
      (fun tree => coupled_maskedFtsNode parameter table state fuel index tree
        ftsTreeHeight 0 hclean (by rfl) (by simp))) fun roots =>
          coupled_ordinaryTweakableHash parameter table state fuel (.ftsRoots index)
            (ftsRootsPayload roots) hclean
            (isOrdinaryInput_ftsRoots parameter table index (ftsRootsPayload roots))

theorem coupled_maskedFtsOpen
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat) (index : Index)
    (leaves : DigestTree → FtsLeaf)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) :
    Coupled parameter table state fuel (maskedFtsOpen parameter index leaves)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (ftsOpen parameter index leaves
          (fun tree leafIdx => table (index, tree, leafIdx)))) := by
  unfold maskedFtsOpen ftsOpen
  rw [simulateQ_randomOracle_sequenceFin]
  apply coupled_sequenceFin parameter table state fuel _ _ hclean
  · intro tree
    exact sequenceFin_stateFree _ fun level =>
      maskedFtsNode_stateFree parameter index tree level.val
        (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)
  · intro tree
    rw [simulateQ_randomOracle_sequenceFin]
    apply coupled_sequenceFin parameter table state fuel _ _ hclean
    · intro level
      exact maskedFtsNode_stateFree parameter index tree level.val
        (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)
    · intro level
      exact coupled_maskedFtsNode parameter table state fuel index tree level.val
        (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1) hclean
        (Nat.le_of_lt level.isLt) (ftsOpen_node_bound (leaves (ftsIndexOf tree)) level)

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

theorem simulateQ_probingRomImpl_run_isProbeBound
    (parameter : PublicParameter) (computation : OracleComp OracleWorld alpha)
    (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches Sum.inr _) q)
    (cache : SplitHashCache) :
    ((simulateQ (probingRomImpl parameter) computation).run cache).IsQueryBoundP
      (AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate)) q := by
  apply hbound.simulateQ_run_StateT_of_step
  intro input workingCache
  cases input with
  | inl n =>
      exact splitUniformImpl_probeFree n workingCache
  | inr hashInput =>
      exact probingHashQuery_run_isProbeBound parameter hashInput workingCache

theorem simulateQ_probingRomImpl_run'_isProbeBound
    (parameter : PublicParameter) (computation : OracleComp OracleWorld alpha)
    (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches Sum.inr _) q)
    (cache : SplitHashCache) :
    ((simulateQ (probingRomImpl parameter) computation).run' cache).IsQueryBoundP
      (AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate)) q := by
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  exact simulateQ_probingRomImpl_run_isProbeBound parameter computation q hbound cache

theorem probEvent_maskedGame_hit_le (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (q : Nat)
    (hbound : ((maskedGameAfterSecrets adversary parameter otsSecret).run'
      emptySplitHashCache).IsQueryBoundP
        (AdaptiveRevealProbe.IsProbe (Coordinate := Coordinate)) q) :
    Pr[fun hit : Bool => hit = true |
        AdaptiveRevealProbe.experiment
          (AdaptiveRevealProbe.State.empty : AdaptiveRevealProbe.State Coordinate) q
          ((maskedGameAfterSecrets adversary parameter otsSecret).run'
            emptySplitHashCache)] ≤
      (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply AdaptiveRevealProbe.experiment_empty_probability_le
  exact hbound

@[simp] theorem hiddenFtsLeafHash_parameter_irrelevant
    (left right : PublicParameter) (coordinate : Coordinate) :
    hiddenFtsLeafHash left coordinate = hiddenFtsLeafHash right coordinate := rfl

end SphincsSecurity.Concrete.FtsProbeSimulation
