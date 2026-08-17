import XmssSecurity.CappedLeafEventProbability
import XmssSecurity.MerkleEventProbability

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedMerkle


theorem detailed_execution_verified_merkle_query_cached_as
    (adversary : Adversary Concrete.scheme)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support (detailedGameWithCache Concrete.scheme adversary))
    (encoding : Encoding) (hverified : execution.1.verified = true)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some encoding)
    (level : MerkleLevel) :
    ∃ output, execution.2
      (Concrete.CacheView.nodeInput execution.1.secretKey.parameter
        execution.1.forgery.epoch level
        (Merkle.ascend
          (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter
            execution.1.forgery.epoch)
          (Concrete.signaturePath execution.1.forgery.signature) 0 level.val
          (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
            execution.1.forgery.epoch
            (recoveredEndpoints
              (fun chain => Concrete.CacheView.chainStep execution.2
                execution.1.secretKey.parameter execution.1.forgery.epoch chain)
              encoding execution.1.forgery.signature.chainValue)))
        (Concrete.signaturePath execution.1.forgery.signature level.val)) = some output := by
  have hparameter :=
    (capped_detailed_execution_key_components_consistent adversary execution hmem).1
  unfold detailedGameWithCache detailedGameCore at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  unfold detailedGameAfterKeygen at hrest
  simp only at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, _hadversary, hverifyRest⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hverifyRest
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hfinal
  cases hfinal
  simp only at hparameter hverified hdecode ⊢
  subst verified
  have hroute :
      simulateQ xmssRomImpl
          (Concrete.scheme.verify publicKey forgery.epoch forgery.message forgery.signature) =
        simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.verify publicKey forgery.epoch forgery.message forgery.signature :
            OracleComp HashSpec Bool) := by
    simp only [Concrete.scheme, xmssRomImpl]
    change simulateQ (unifFwdImpl HashSpec +
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)))
      (liftM (Concrete.verify publicKey forgery.epoch forgery.message forgery.signature :
        OracleComp HashSpec Bool)) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.verify publicKey forgery.epoch forgery.message forgery.signature :
        OracleComp HashSpec Bool)
  rw [hroute] at hverify
  have hdecodePublic : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash finalCache publicKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness)) = some encoding := by
    rw [hparameter]
    exact hdecode
  rw [← hparameter]
  exact Concrete.CacheReplay.verify_true_merkle_query_cached_as_in_largerCache publicKey
    forgery.epoch forgery.message forgery.signature encoding level adversaryCache finalCache
    finalCache hverify hdecodePublic le_rfl

def orderedNodePair (epoch : Epoch) (level : Nat) (current sibling : Digest) : Digest × Digest :=
  if epoch.val.testBit level then (sibling, current) else (current, sibling)

@[simp]
theorem nodeInput_eq_merkleInput_ordered (parameter : PublicParameter) (epoch : Epoch)
    (level : MerkleLevel) (current sibling : Digest) :
    Concrete.CacheView.nodeInput parameter epoch level current sibling =
      Concrete.CacheView.merkleInput parameter level
        (Concrete.CacheView.nodeIndex epoch level.val)
        (orderedNodePair epoch level.val current sibling).1
        (orderedNodePair epoch level.val current sibling).2 := by
  by_cases hbit : epoch.val.testBit level.val = true
  · simp [Concrete.CacheView.nodeInput, Concrete.CacheView.merkleInput,
      Concrete.CacheView.authenticationNodePayload, orderedNodePair, hbit]
  · have hbitFalse := Bool.eq_false_of_not_eq_true hbit
    simp [Concrete.CacheView.nodeInput, Concrete.CacheView.merkleInput,
      Concrete.CacheView.authenticationNodePayload, orderedNodePair, hbitFalse]

theorem orderedNodePair_injective (epoch : Epoch) (level : Nat) :
    Function.Injective fun pair : Digest × Digest =>
      orderedNodePair epoch level pair.1 pair.2 := by
  intro left right heq
  by_cases hbit : epoch.val.testBit level = true
  · simp [orderedNodePair, hbit] at heq
    exact Prod.ext heq.2 heq.1
  · have hbitFalse := Bool.eq_false_of_not_eq_true hbit
    simpa [orderedNodePair, hbitFalse] using heq

theorem nodeIndex_valid_at_level (epoch : Epoch) (level : MerkleLevel) :
    (Concrete.CacheView.nodeIndex epoch level.val).val <
      2 ^ (treeHeight - (level.val + 1)) := by
  have hsum : (treeHeight - (level.val + 1)) + (level.val + 1) = treeHeight := by
    omega
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ (level.val + 1))).2
  calc
    epoch.val < 2 ^ treeHeight := epoch.isLt
    _ = 2 ^ (treeHeight - (level.val + 1)) * 2 ^ (level.val + 1) := by
      rw [← Nat.pow_add, hsum]

noncomputable def keygenMerkleTargetInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : HashInput :=
  if h : ∃ address : MerkleLevel × MerkleNode, ∃ left right,
      input = Concrete.CacheView.merkleInput secretKey.parameter address.1 address.2
        left right then
    let address := h.choose
    Concrete.CacheView.merkleInput secretKey.parameter address.1 address.2
      (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
        address.1.val (Concrete.childNode address.2 false))
      (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
        address.1.val (Concrete.childNode address.2 true))
  else input

@[simp]
theorem keygenMerkleTargetInput_merkleInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) :
    keygenMerkleTargetInput secretKey cache
      (Concrete.CacheView.merkleInput secretKey.parameter level node left right) =
      Concrete.CacheView.merkleInput secretKey.parameter level node
        (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
          level.val (Concrete.childNode node false))
        (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
          level.val (Concrete.childNode node true)) := by
  unfold keygenMerkleTargetInput
  split
  · rename_i h
    obtain ⟨chosenLeft, chosenRight, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      (hinput.trans rfl)
    simp only [HashDomain.merkle.injEq] at hdomain
    rcases hdomain with ⟨hlevel, hnode⟩
    dsimp only
    rw [← hlevel, ← hnode]
  · rename_i h
    exfalso
    exact h ⟨(level, node), left, right, rfl⟩

attribute [irreducible] keygenMerkleTargetInput

theorem ordered_honestNodePair_eq_children
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (epoch : Epoch)
    (level : MerkleLevel) :
    orderedNodePair epoch level.val
        (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
          level.val (Concrete.CacheReplay.pathNode epoch level.val))
        (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
          level.val (Concrete.authenticationPathNode epoch level)) =
      (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
          level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex epoch level.val) false),
        Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
          level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex epoch level.val) true)) := by
  rw [Concrete.CacheReplay.nodeIndex_eq_pathNode_succ]
  have hchildren := Concrete.CacheReplay.pathNode_children epoch level.val level.isLt
  by_cases hbit : epoch.val.testBit level.val = true
  · simp only [hbit, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [orderedNodePair, hbit, hleft, hright]
  · have hbitFalse := Bool.eq_false_of_not_eq_true hbit
    simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [orderedNodePair, hbitFalse, hleft, hright]

theorem adaptiveFreshDigestCollisionWith_of_merkleCollision
    (secretKey : SecretKey) (initialCache finalCache : QueryCache HashSpec)
    (epoch : Epoch) (level : MerkleLevel)
    (forgedCurrent forgedSibling honestCurrent honestSibling : Digest)
    (forgedOutput honestOutput : HashOutput)
    (hforgedFinal : finalCache
      (Concrete.CacheView.nodeInput secretKey.parameter epoch level
        forgedCurrent forgedSibling) = some forgedOutput)
    (hforgedInitial : initialCache
      (Concrete.CacheView.nodeInput secretKey.parameter epoch level
        forgedCurrent forgedSibling) = none)
    (hhonestInitial : initialCache
      (Concrete.CacheView.nodeInput secretKey.parameter epoch level
        honestCurrent honestSibling) = some honestOutput)
    (hcollision : Concrete.CacheView.digestAt finalCache
        (Concrete.CacheView.nodeInput secretKey.parameter epoch level
          forgedCurrent forgedSibling) =
      Concrete.CacheView.digestAt finalCache
        (Concrete.CacheView.nodeInput secretKey.parameter epoch level
          honestCurrent honestSibling))
    (hhonest : orderedNodePair epoch level.val honestCurrent honestSibling =
      (Concrete.CacheReplay.treeNode initialCache secretKey.parameter secretKey.chainStart
          level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex epoch level.val) false),
        Concrete.CacheReplay.treeNode initialCache secretKey.parameter secretKey.chainStart
          level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex epoch level.val) true))) :
    Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      (keygenMerkleTargetInput secretKey initialCache) := by
  let forgedInput := Concrete.CacheView.nodeInput secretKey.parameter epoch level
    forgedCurrent forgedSibling
  have hhonestLeft := congrArg Prod.fst hhonest
  have hhonestRight := congrArg Prod.snd hhonest
  simp only at hhonestLeft hhonestRight
  have hhonestInitial' := hhonestInitial
  rw [nodeInput_eq_merkleInput_ordered] at hhonestInitial'
  have hcollision' := hcollision
  rw [nodeInput_eq_merkleInput_ordered, nodeInput_eq_merkleInput_ordered] at hcollision'
  refine ⟨forgedInput, forgedOutput, honestOutput, hforgedFinal, hforgedInitial, ?_, ?_⟩
  · rw [show forgedInput = Concrete.CacheView.nodeInput secretKey.parameter epoch level
      forgedCurrent forgedSibling by rfl]
    rw [nodeInput_eq_merkleInput_ordered, keygenMerkleTargetInput_merkleInput,
      ← hhonestLeft, ← hhonestRight]
    exact hhonestInitial'
  · rw [show forgedInput = Concrete.CacheView.nodeInput secretKey.parameter epoch level
      forgedCurrent forgedSibling by rfl]
    rw [nodeInput_eq_merkleInput_ordered, keygenMerkleTargetInput_merkleInput,
      ← hhonestLeft, ← hhonestRight]
    exact hcollision'

theorem merkleCollision_afterKeygen_orientation
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (secretKey : SecretKey) (hsecret : secretKey = keyResult.1.2)
    (epoch : Epoch) (level : MerkleLevel)
    (forgedCurrent forgedSibling honestCurrent honestSibling : Digest)
    (forgedOutput : HashOutput)
    (hforgedCached : execution.2
      (Concrete.CacheView.nodeInput secretKey.parameter epoch level
        forgedCurrent forgedSibling) = some forgedOutput)
    (hne : (forgedCurrent, forgedSibling) ≠ (honestCurrent, honestSibling))
    (heq : Concrete.CacheView.nodeHash execution.2 secretKey.parameter epoch level.val
        forgedCurrent forgedSibling =
      Concrete.CacheView.nodeHash execution.2 secretKey.parameter epoch level.val
        honestCurrent honestSibling)
    (hhonest : orderedNodePair epoch level.val honestCurrent honestSibling =
      (Concrete.CacheReplay.treeNode execution.2 secretKey.parameter secretKey.chainStart
          level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex epoch level.val) false),
        Concrete.CacheReplay.treeNode execution.2 secretKey.parameter secretKey.chainStart
          level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex epoch level.val) true))) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  subst secretKey
  have hafterCacheLe := xmssRom_cache_le
    (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)
    keyResult.2 execution hafter
  have hkeygen' : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.precomputedKeygen).run ∅) := by
    simpa only [Concrete.scheme] using hkeygen
  let node := Concrete.CacheView.nodeIndex epoch level.val
  have horderedNe : orderedNodePair epoch level.val forgedCurrent forgedSibling ≠
      orderedNodePair epoch level.val honestCurrent honestSibling := by
    intro hordered
    exact hne (orderedNodePair_injective epoch level.val hordered)
  have hforgedInitial :=
    Concrete.precomputedKeygen_cache_merkleInput_eq_none_of_ne_in_largerCache keyResult
      hkeygen' execution.2 hafterCacheLe level node (nodeIndex_valid_at_level epoch level)
      (orderedNodePair epoch level.val forgedCurrent forgedSibling).1
      (orderedNodePair epoch level.val forgedCurrent forgedSibling).2 (by
        rw [← hhonest]
        exact horderedNe)
  rw [← nodeInput_eq_merkleInput_ordered] at hforgedInitial
  obtain ⟨honestOutput, hhonestCached⟩ :=
    Concrete.precomputedKeygen_cache_has_merkleInput_in_largerCache keyResult hkeygen'
      execution.2 hafterCacheLe level node (nodeIndex_valid_at_level epoch level)
  dsimp only [node] at hhonestCached
  have hhonestLeft := congrArg Prod.fst hhonest
  have hhonestRight := congrArg Prod.snd hhonest
  simp only at hhonestLeft hhonestRight
  rw [← hhonestLeft, ← hhonestRight, ← nodeInput_eq_merkleInput_ordered] at hhonestCached
  have hcollision := heq
  rw [Concrete.CacheView.nodeHash_eq _ _ _ _ _ _ level.isLt,
    Concrete.CacheView.nodeHash_eq _ _ _ _ _ _ level.isLt] at hcollision
  have hstable := Concrete.precomputedKeygen_merkleChildren_eq_of_cache_le keyResult hkeygen'
    execution.2 hafterCacheLe level node (nodeIndex_valid_at_level epoch level)
  have hhonestInitial : orderedNodePair epoch level.val honestCurrent honestSibling =
      (Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex epoch level.val) false),
        Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex epoch level.val) true)) := by
    dsimp only [node] at hstable
    exact hhonest.trans hstable.symm
  exact adaptiveFreshDigestCollisionWith_of_merkleCollision keyResult.1.2 keyResult.2
    execution.2 epoch level forgedCurrent forgedSibling honestCurrent honestSibling
    forgedOutput honestOutput hforgedCached hforgedInitial hhonestCached hcollision
    hhonestInitial




def merkleWitnessEvent (execution : GameOutcome × QueryCache HashSpec)
    (epoch : Epoch) (forgedEncoding : Encoding) (honestPath : Nat → Digest)
    (honestLeaf : Digest) (level : MerkleLevel) : Prop :=
  Merkle.IsXmssPathCollisionAt
    (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter epoch)
    (Concrete.signaturePath execution.1.forgery.signature) honestPath
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter epoch
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter epoch chain)
        forgedEncoding execution.1.forgery.signature.chainValue))
    honestLeaf level

def merkleWitnessHonestCurrent (execution : GameOutcome × QueryCache HashSpec)
    (epoch : Epoch) (honestPath : Nat → Digest) (honestLeaf : Digest)
    (level : MerkleLevel) : Prop :=
  Merkle.ascend
      (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter epoch)
      honestPath 0 level.val honestLeaf =
    Concrete.CacheReplay.treeNode execution.2 execution.1.secretKey.parameter
      execution.1.secretKey.chainStart level.val
      (Concrete.CacheReplay.pathNode epoch level.val)

def merkleWitnessHonestSibling (execution : GameOutcome × QueryCache HashSpec)
    (epoch : Epoch) (honestPath : Nat → Digest) (level : MerkleLevel) : Prop :=
  honestPath level.val =
    Concrete.CacheReplay.treeNode execution.2 execution.1.secretKey.parameter
      execution.1.secretKey.chainStart level.val
      (Concrete.authenticationPathNode epoch level)

attribute [irreducible] merkleWitnessEvent merkleWitnessHonestCurrent merkleWitnessHonestSibling

inductive MerkleWitness (execution : GameOutcome × QueryCache HashSpec) : Prop where
  | intro (verified : execution.1.verified = true)
      (epoch : Epoch) (epoch_eq : epoch = execution.1.forgery.epoch)
      (forgedEncoding : Encoding)
      (forged_decode : TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
          execution.1.forgery.epoch
          (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
          some forgedEncoding)
      (honestPath : Nat → Digest) (honestLeaf : Digest) (level : MerkleLevel)
      (event : merkleWitnessEvent execution epoch forgedEncoding honestPath honestLeaf level)
      (honest_current : merkleWitnessHonestCurrent execution epoch honestPath honestLeaf level)
      (honest_sibling : merkleWitnessHonestSibling execution epoch honestPath level) :
      MerkleWitness execution

def cachedMerkleInput (execution : GameOutcome × QueryCache HashSpec)
    (epoch : Epoch) (level : MerkleLevel) (current sibling : Digest) : HashInput :=
  Concrete.CacheView.nodeInput execution.1.secretKey.parameter epoch level current sibling

theorem cachedMerkleInput_eq (execution : GameOutcome × QueryCache HashSpec)
    (epoch : Epoch) (level : MerkleLevel) (current sibling : Digest) :
    cachedMerkleInput execution epoch level current sibling =
      Concrete.CacheView.nodeInput execution.1.secretKey.parameter epoch level current sibling := rfl

abbrev forgedMerkleQueryInput (execution : GameOutcome × QueryCache HashSpec)
    (epoch : Epoch) (encoding : Encoding) (level : MerkleLevel) : HashInput :=
  Concrete.CacheView.nodeInput execution.1.secretKey.parameter epoch level
    (Merkle.ascend
      (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter epoch)
      (Concrete.signaturePath execution.1.forgery.signature) 0 level.val
      (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter epoch
        (recoveredEndpoints
          (fun chain => Concrete.CacheView.chainStep execution.2
            execution.1.secretKey.parameter epoch chain)
          encoding execution.1.forgery.signature.chainValue)))
    (Concrete.signaturePath execution.1.forgery.signature level.val)

theorem forgedMerkleQueryInput_eq (execution : GameOutcome × QueryCache HashSpec)
    (epoch : Epoch) (encoding : Encoding) (level : MerkleLevel) :
    forgedMerkleQueryInput execution epoch encoding level =
      Concrete.CacheView.nodeInput execution.1.secretKey.parameter epoch level
        (Merkle.ascend
          (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter epoch)
          (Concrete.signaturePath execution.1.forgery.signature) 0 level.val
          (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter epoch
            (recoveredEndpoints
              (fun chain => Concrete.CacheView.chainStep execution.2
                execution.1.secretKey.parameter epoch chain)
              encoding execution.1.forgery.signature.chainValue)))
        (Concrete.signaturePath execution.1.forgery.signature level.val) := rfl

def cachedMerkleDigest (execution : GameOutcome × QueryCache HashSpec)
    (epoch : Epoch) (level : MerkleLevel) (current sibling : Digest) : Digest :=
  Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter epoch level.val
    current sibling

theorem cachedMerkleDigest_eq (execution : GameOutcome × QueryCache HashSpec)
    (epoch : Epoch) (level : MerkleLevel) (current sibling : Digest) :
    cachedMerkleDigest execution epoch level current sibling =
      Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter epoch level.val
        current sibling := rfl

def cachedHonestMerklePair (execution : GameOutcome × QueryCache HashSpec)
    (epoch : Epoch) (level : MerkleLevel) : Digest × Digest :=
  (Concrete.CacheReplay.treeNode execution.2 execution.1.secretKey.parameter
      execution.1.secretKey.chainStart level.val
      (Concrete.childNode (Concrete.CacheView.nodeIndex epoch level.val) false),
    Concrete.CacheReplay.treeNode execution.2 execution.1.secretKey.parameter
      execution.1.secretKey.chainStart level.val
      (Concrete.childNode (Concrete.CacheView.nodeIndex epoch level.val) true))

theorem cachedHonestMerklePair_eq (execution : GameOutcome × QueryCache HashSpec)
    (epoch : Epoch) (level : MerkleLevel) :
    cachedHonestMerklePair execution epoch level =
      (Concrete.CacheReplay.treeNode execution.2 execution.1.secretKey.parameter
          execution.1.secretKey.chainStart level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex epoch level.val) false),
        Concrete.CacheReplay.treeNode execution.2 execution.1.secretKey.parameter
          execution.1.secretKey.chainStart level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex epoch level.val) true)) := rfl

attribute [irreducible] cachedMerkleInput cachedMerkleDigest cachedHonestMerklePair

inductive CachedMerkleCollision (execution : GameOutcome × QueryCache HashSpec) : Prop where
  | intro (epoch : Epoch) (level : MerkleLevel)
      (forgedCurrent forgedSibling honestCurrent honestSibling : Digest)
      (forgedOutput : HashOutput)
      (forged_cached : execution.2
        (cachedMerkleInput execution epoch level forgedCurrent forgedSibling) = some forgedOutput)
      (distinct : (forgedCurrent, forgedSibling) ≠ (honestCurrent, honestSibling))
      (digest_eq : cachedMerkleDigest execution epoch level forgedCurrent forgedSibling =
        cachedMerkleDigest execution epoch level honestCurrent honestSibling)
      (honest_pair : orderedNodePair epoch level.val honestCurrent honestSibling =
        cachedHonestMerklePair execution epoch level) :
      CachedMerkleCollision execution

theorem afterKeygen_verified_merkle_query_cached_as
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (encoding : Encoding) (hverified : execution.1.verified = true)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some encoding)
    (level : MerkleLevel) :
    ∃ output, execution.2
      (Concrete.CacheView.nodeInput execution.1.secretKey.parameter
        execution.1.forgery.epoch level
        (Merkle.ascend
          (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter
            execution.1.forgery.epoch)
          (Concrete.signaturePath execution.1.forgery.signature) 0 level.val
          (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
            execution.1.forgery.epoch
            (recoveredEndpoints
              (fun chain => Concrete.CacheView.chainStep execution.2
                execution.1.secretKey.parameter execution.1.forgery.epoch chain)
              encoding execution.1.forgery.signature.chainValue)))
        (Concrete.signaturePath execution.1.forgery.signature level.val)) = some output := by
  have hgame := CappedLeaf.afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen execution hafter
  exact detailed_execution_verified_merkle_query_cached_as adversary execution hgame encoding
    hverified hdecode level

set_option linter.constructorNameAsVariable false

inductive OrientedMerkleWitness (execution : GameOutcome × QueryCache HashSpec) : Prop where
  | intro (verified : execution.1.verified = true)
      (epoch : Epoch) (epoch_eq : epoch = execution.1.forgery.epoch)
      (forgedEncoding : Encoding)
      (forged_decode : TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
          execution.1.forgery.epoch
          (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
          some forgedEncoding)
      (level : MerkleLevel)
      (forgedCurrent forgedSibling honestCurrent honestSibling : Digest)
      (forged_current : forgedCurrent =
        Merkle.ascend
          (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter epoch)
          (Concrete.signaturePath execution.1.forgery.signature) 0 level.val
          (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter epoch
            (recoveredEndpoints
              (fun chain => Concrete.CacheView.chainStep execution.2
                execution.1.secretKey.parameter epoch chain)
              forgedEncoding execution.1.forgery.signature.chainValue)))
      (forged_sibling : forgedSibling =
        Concrete.signaturePath execution.1.forgery.signature level.val)
      (distinct : (forgedCurrent, forgedSibling) ≠ (honestCurrent, honestSibling))
      (digest_eq : cachedMerkleDigest execution epoch level forgedCurrent forgedSibling =
        cachedMerkleDigest execution epoch level honestCurrent honestSibling)
      (honest_pair : orderedNodePair epoch level.val honestCurrent honestSibling =
        cachedHonestMerklePair execution epoch level) :
      OrientedMerkleWitness execution

theorem MerkleWitness.toOriented (execution : GameOutcome × QueryCache HashSpec)
    (witness : MerkleWitness execution) : OrientedMerkleWitness execution := by
  obtain ⟨hverified, epoch, hepoch, forgedEncoding, hforgedDecode, honestPath,
      honestLeaf, level, hevent, hhonestCurrent, hhonestSibling⟩ := witness
  unfold merkleWitnessEvent at hevent
  unfold merkleWitnessHonestCurrent at hhonestCurrent
  unfold merkleWitnessHonestSibling at hhonestSibling
  let forgedCurrent := Merkle.ascend
    (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter epoch)
    (Concrete.signaturePath execution.1.forgery.signature) 0 level.val
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter epoch
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter epoch chain)
        forgedEncoding execution.1.forgery.signature.chainValue))
  let forgedSibling := Concrete.signaturePath execution.1.forgery.signature level.val
  let honestCurrent := Merkle.ascend
    (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter epoch)
    honestPath 0 level.val honestLeaf
  let honestSibling := honestPath level.val
  change (forgedCurrent, forgedSibling) ≠ (honestCurrent, honestSibling) ∧
    Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter epoch level.val
        forgedCurrent forgedSibling =
      Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter epoch level.val
        honestCurrent honestSibling at hevent
  have heq : cachedMerkleDigest execution epoch level forgedCurrent forgedSibling =
      cachedMerkleDigest execution epoch level honestCurrent honestSibling := by
    rw [cachedMerkleDigest_eq, cachedMerkleDigest_eq]
    exact hevent.2
  have hhonest : orderedNodePair epoch level.val honestCurrent honestSibling =
      cachedHonestMerklePair execution epoch level := by
    rw [cachedHonestMerklePair_eq]
    rw [show honestCurrent = Concrete.CacheReplay.treeNode execution.2
        execution.1.secretKey.parameter execution.1.secretKey.chainStart level.val
        (Concrete.CacheReplay.pathNode epoch level.val) by exact hhonestCurrent,
      show honestSibling = Concrete.CacheReplay.treeNode execution.2
        execution.1.secretKey.parameter execution.1.secretKey.chainStart level.val
        (Concrete.authenticationPathNode epoch level) by exact hhonestSibling]
    exact ordered_honestNodePair_eq_children execution.2 execution.1.secretKey epoch level
  exact .intro hverified epoch hepoch forgedEncoding hforgedDecode level forgedCurrent
    forgedSibling honestCurrent honestSibling rfl rfl hevent.1 heq hhonest

theorem afterKeygen_verified_forgedMerkleQuery_cached
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (encoding : Encoding) (hverified : execution.1.verified = true)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some encoding)
    (level : MerkleLevel) :
    ∃ output, execution.2
      (forgedMerkleQueryInput execution execution.1.forgery.epoch encoding level) =
        some output := by
  obtain ⟨output, hcached⟩ :=
    afterKeygen_verified_merkle_query_cached_as adversary keyResult hkeygen execution hafter
      encoding hverified hdecode level
  exact ⟨output, hcached⟩

theorem forgedMerkleQueryInput_eq_of_epoch
    (execution : GameOutcome × QueryCache HashSpec)
    (epoch : Epoch) (hepoch : epoch = execution.1.forgery.epoch)
    (encoding : Encoding) (level : MerkleLevel) :
    forgedMerkleQueryInput execution epoch encoding level =
      forgedMerkleQueryInput execution execution.1.forgery.epoch encoding level := by
  subst epoch
  rfl

theorem afterKeygen_verified_forgedMerkleQuery_cached_at
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (encoding : Encoding) (hverified : execution.1.verified = true)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some encoding)
    (epoch : Epoch) (hepoch : epoch = execution.1.forgery.epoch)
    (level : MerkleLevel) :
    ∃ output, execution.2 (forgedMerkleQueryInput execution epoch encoding level) =
      some output := by
  subst epoch
  exact afterKeygen_verified_forgedMerkleQuery_cached adversary keyResult hkeygen execution
    hafter encoding hverified hdecode level

theorem cachedMerkleInput_eq_forgedMerkleQueryInput
    (execution : GameOutcome × QueryCache HashSpec)
    (epoch : Epoch) (encoding : Encoding) (level : MerkleLevel)
    (forgedCurrent forgedSibling : Digest)
    (hcurrent : forgedCurrent =
      Merkle.ascend
        (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter epoch)
        (Concrete.signaturePath execution.1.forgery.signature) 0 level.val
        (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter epoch
          (recoveredEndpoints
            (fun chain => Concrete.CacheView.chainStep execution.2
              execution.1.secretKey.parameter epoch chain)
            encoding execution.1.forgery.signature.chainValue)))
    (hsibling : forgedSibling =
      Concrete.signaturePath execution.1.forgery.signature level.val) :
    cachedMerkleInput execution epoch level forgedCurrent forgedSibling =
      forgedMerkleQueryInput execution epoch encoding level := by
  rw [cachedMerkleInput_eq, forgedMerkleQueryInput_eq, hcurrent, hsibling]

theorem OrientedMerkleWitness.cachedQuery
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (witness : OrientedMerkleWitness execution) :
    ∃ epoch level forgedCurrent forgedSibling honestCurrent honestSibling forgedOutput,
      execution.2 (cachedMerkleInput execution epoch level forgedCurrent forgedSibling) =
        some forgedOutput ∧
      (forgedCurrent, forgedSibling) ≠ (honestCurrent, honestSibling) ∧
      cachedMerkleDigest execution epoch level forgedCurrent forgedSibling =
        cachedMerkleDigest execution epoch level honestCurrent honestSibling ∧
      orderedNodePair epoch level.val honestCurrent honestSibling =
        cachedHonestMerklePair execution epoch level := by
  obtain ⟨hverified, epoch, hepoch, forgedEncoding, hforgedDecode, level, forgedCurrent,
      forgedSibling, honestCurrent, honestSibling, hforgedCurrent, hforgedSibling,
      hne, heq, hhonest⟩ := witness
  obtain ⟨forgedOutput, hcached⟩ :=
    afterKeygen_verified_forgedMerkleQuery_cached_at adversary keyResult hkeygen execution
      hafter forgedEncoding hverified hforgedDecode epoch hepoch level
  have hinput := cachedMerkleInput_eq_forgedMerkleQueryInput execution epoch forgedEncoding
    level forgedCurrent forgedSibling hforgedCurrent hforgedSibling
  refine ⟨epoch, level, forgedCurrent, forgedSibling, honestCurrent, honestSibling,
    forgedOutput, ?_, hne, heq, hhonest⟩
  rw [hinput]
  exact hcached

theorem OrientedMerkleWitness.withCachedQuery
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (witness : OrientedMerkleWitness execution) : CachedMerkleCollision execution := by
  obtain ⟨epoch, level, forgedCurrent, forgedSibling, honestCurrent, honestSibling,
      forgedOutput, hforgedCached, hne, heq, hhonest⟩ :=
    OrientedMerkleWitness.cachedQuery adversary keyResult hkeygen execution hafter witness
  exact .intro epoch level forgedCurrent forgedSibling honestCurrent honestSibling forgedOutput
    hforgedCached hne heq hhonest

theorem MerkleWitness.toCachedCollision
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (witness : MerkleWitness execution) : CachedMerkleCollision execution :=
  OrientedMerkleWitness.withCachedQuery adversary keyResult hkeygen execution hafter
    (MerkleWitness.toOriented execution witness)

theorem CachedMerkleCollision.afterKeygen_orientation
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (collision : CachedMerkleCollision execution) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  obtain ⟨epoch, level, forgedCurrent, forgedSibling, honestCurrent, honestSibling,
      forgedOutput, hforgedCached, hne, heq, hhonest⟩ := collision
  have hkeys := CappedLeaf.detailedGameAfterKeygen_keys_eq adversary keyResult.1.1
    keyResult.1.2
    keyResult.2 execution hafter
  have hforgedCached' : execution.2
      (Concrete.CacheView.nodeInput execution.1.secretKey.parameter epoch level
        forgedCurrent forgedSibling) = some forgedOutput := by
    rw [← cachedMerkleInput_eq]
    exact hforgedCached
  have heq' :
      Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter epoch level.val
          forgedCurrent forgedSibling =
        Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter epoch level.val
          honestCurrent honestSibling := by
    rw [← cachedMerkleDigest_eq, ← cachedMerkleDigest_eq]
    exact heq
  have hhonest' : orderedNodePair epoch level.val honestCurrent honestSibling =
      (Concrete.CacheReplay.treeNode execution.2 execution.1.secretKey.parameter
          execution.1.secretKey.chainStart level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex epoch level.val) false),
        Concrete.CacheReplay.treeNode execution.2 execution.1.secretKey.parameter
          execution.1.secretKey.chainStart level.val
          (Concrete.childNode (Concrete.CacheView.nodeIndex epoch level.val) true)) := by
    rw [← cachedHonestMerklePair_eq]
    exact hhonest
  exact merkleCollision_afterKeygen_orientation adversary keyResult hkeygen execution hafter
    execution.1.secretKey hkeys.2 epoch level forgedCurrent forgedSibling honestCurrent
    honestSibling forgedOutput hforgedCached' hne heq' hhonest'

theorem merkle_witness_afterKeygen_orientation
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (witness : MerkleWitness execution) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) :=
  CachedMerkleCollision.afterKeygen_orientation adversary keyResult hkeygen execution hafter
    (MerkleWitness.toCachedCollision adversary keyResult hkeygen execution hafter witness)



theorem same_merkle_witness_afterKeygen_orientation
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (hverified : execution.1.verified = true)
    (request : SignRequest) (signature : Signature)
    (signedEncoding forgedEncoding : Encoding)
    (hsignedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        request.epoch (request.message, signature.randomness)) = some signedEncoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        request.epoch
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding)
    (hreturned : SigningTranscript.Returned execution.1.signingLog request signature)
    (hepoch : request.epoch = execution.1.forgery.epoch)
    (level : MerkleLevel)
    (hevent : Concrete.SameEpochBadEventOccurs execution.2
      execution.1.secretKey.parameter request.epoch request.message
      execution.1.forgery.message signedEncoding forgedEncoding signature
      execution.1.forgery.signature
      (TargetSum.decodeDigest_eq_some_iff.mp hsignedDecode).2 (.merkle level)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  have hgame := CappedLeaf.afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen execution hafter
  have hsignature := CappedLeaf.detailed_execution_returned_signature_eq adversary execution hgame
    request signature signedEncoding hsignedDecode hreturned
  have hdecodeEpoch := congrArg (fun epoch => TargetSum.decodeDigest
    (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter epoch
      (execution.1.forgery.message, execution.1.forgery.signature.randomness))) hepoch
  have hforgedDecode' : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding := hdecodeEpoch.symm.trans hforgedDecode
  change Merkle.IsXmssPathCollisionAt
    (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter request.epoch)
    (Concrete.signaturePath execution.1.forgery.signature)
    (Concrete.signaturePath signature)
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter request.epoch
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter request.epoch chain)
        forgedEncoding execution.1.forgery.signature.chainValue))
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter request.epoch
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter request.epoch chain)
        signedEncoding signature.chainValue)) level at hevent
  refine merkle_witness_afterKeygen_orientation adversary keyResult hkeygen execution hafter
    (.intro hverified request.epoch hepoch forgedEncoding hforgedDecode'
      (Concrete.signaturePath signature)
      (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter request.epoch
        (recoveredEndpoints
          (fun chain => Concrete.CacheView.chainStep execution.2
            execution.1.secretKey.parameter request.epoch chain)
          signedEncoding signature.chainValue)) level
      (by unfold merkleWitnessEvent; exact hevent) ?_ ?_)
  · unfold merkleWitnessHonestCurrent
    rw [hsignature,
      Concrete.CacheReplay.leafHash_recovered_signWithEncoding]
    exact Concrete.CacheReplay.authenticationPath_ascends_to_treeNode execution.2
      execution.1.secretKey request.epoch signature.randomness signedEncoding level.val
      level.isLt.le
  · rw [hsignature]
    unfold merkleWitnessHonestSibling
    simp [Concrete.signaturePath, Concrete.CacheReplay.signWithEncoding,
      Concrete.CacheReplay.authenticationPath, level.isLt]

theorem fresh_merkle_witness_afterKeygen_orientation
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (hverified : execution.1.verified = true)
    (forgedEncoding : Encoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding)
    (level : MerkleLevel)
    (hevent : Concrete.FreshEpochBadEventOccurs execution.2
      execution.1.secretKey.parameter execution.1.forgery.epoch forgedEncoding
      execution.1.forgery.signature
      (execution.1.secretKey.chainStart execution.1.forgery.epoch)
      (Concrete.signaturePath
        (Concrete.CacheReplay.signWithEncoding execution.2 execution.1.secretKey
          execution.1.forgery.epoch execution.1.forgery.signature.randomness forgedEncoding))
      (TargetSum.decodeDigest_eq_some_iff.mp hforgedDecode).2 (.merkle level)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  let honestSignature := Concrete.CacheReplay.signWithEncoding execution.2
    execution.1.secretKey execution.1.forgery.epoch
    execution.1.forgery.signature.randomness forgedEncoding
  change Merkle.IsXmssPathCollisionAt
    (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter
      execution.1.forgery.epoch)
    (Concrete.signaturePath execution.1.forgery.signature)
    (Concrete.signaturePath honestSignature)
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
      execution.1.forgery.epoch
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter execution.1.forgery.epoch chain)
        forgedEncoding execution.1.forgery.signature.chainValue))
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
      execution.1.forgery.epoch
      (fun chain => Wots.publicChain
        (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
          execution.1.forgery.epoch chain)
        (execution.1.secretKey.chainStart execution.1.forgery.epoch chain))) level at hevent
  refine merkle_witness_afterKeygen_orientation adversary keyResult hkeygen execution hafter
    (.intro hverified execution.1.forgery.epoch rfl forgedEncoding hforgedDecode
      (Concrete.signaturePath honestSignature)
      (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch
        (fun chain => Wots.publicChain
          (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
            execution.1.forgery.epoch chain)
          (execution.1.secretKey.chainStart execution.1.forgery.epoch chain))) level
      (by unfold merkleWitnessEvent; exact hevent) ?_ ?_)
  · unfold merkleWitnessHonestCurrent
    change Merkle.ascend
      (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch)
      (Concrete.signaturePath honestSignature) 0 level.val
      (Concrete.CacheReplay.leafAt execution.2 execution.1.secretKey.parameter
        execution.1.secretKey.chainStart execution.1.forgery.epoch) = _
    exact Concrete.CacheReplay.authenticationPath_ascends_to_treeNode execution.2
      execution.1.secretKey execution.1.forgery.epoch
      execution.1.forgery.signature.randomness forgedEncoding level.val level.isLt.le
  · unfold merkleWitnessHonestSibling
    simp [honestSignature, Concrete.signaturePath,
      Concrete.CacheReplay.signWithEncoding, Concrete.CacheReplay.authenticationPath,
      level.isLt]

theorem merkle_event_afterKeygen_orientation
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (level : MerkleLevel)
    (hevent : OutcomeBadEventOccurs execution.2 execution.1 (.merkle level)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  rcases hevent.2 with hsame | hfresh
  · obtain ⟨request, signature, signedEncoding, forgedEncoding, hsignedDecode,
      hforgedDecode, hreturned, hepoch, hmerkle⟩ := hsame
    exact same_merkle_witness_afterKeygen_orientation adversary keyResult hkeygen execution
      hafter hevent.1 request signature signedEncoding forgedEncoding hsignedDecode
      hforgedDecode hreturned hepoch level hmerkle
  · obtain ⟨forgedEncoding, hforgedValid, _hunsigned, hforgedDecode, hmerkle⟩ := hfresh
    exact fresh_merkle_witness_afterKeygen_orientation adversary keyResult hkeygen execution
      hafter hevent.1 forgedEncoding hforgedDecode level hmerkle

theorem merkle_outcomeBadEvent_probability_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) (level : MerkleLevel) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      OutcomeBadEventOccurs execution.2 execution.1 (.merkle level) |
      detailedGameWithCache Concrete.scheme adversary] ≤
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  apply outcomeBadEvent_probability_le_of_afterKeygen_freshCollision_forScheme Concrete.scheme q adversary hbound
    (.merkle level) (fun key cache => keygenMerkleTargetInput key.2 cache)
  intro keyResult hkeygen execution hafter hevent
  exact merkle_event_afterKeygen_orientation adversary keyResult hkeygen execution hafter
    level hevent


end XmssSecurity.CappedMerkle

namespace XmssSecurity

theorem capped_merkle_outcomeBadEvent_probability_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (level : MerkleLevel) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      OutcomeBadEventOccurs execution.2 execution.1 (.merkle level) |
      detailedGameWithCache Concrete.scheme adversary] ≤
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) :=
  CappedMerkle.merkle_outcomeBadEvent_probability_le q adversary hbound level

end XmssSecurity
