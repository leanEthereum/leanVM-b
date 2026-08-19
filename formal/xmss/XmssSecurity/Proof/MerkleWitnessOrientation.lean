import XmssSecurity.Proof.MerkleCollisionOrientation

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

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
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary keyResult.1.1 keyResult.1.2)).run
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
  have hgame := afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen execution hafter
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
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary keyResult.1.1 keyResult.1.2)).run
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
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary keyResult.1.1 keyResult.1.2)).run
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
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary keyResult.1.1 keyResult.1.2)).run
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
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (witness : OrientedMerkleWitness execution) : CachedMerkleCollision execution := by
  obtain ⟨epoch, level, forgedCurrent, forgedSibling, honestCurrent, honestSibling,
      forgedOutput, hforgedCached, hne, heq, hhonest⟩ :=
    OrientedMerkleWitness.cachedQuery adversary keyResult hkeygen execution hafter witness
  exact .intro epoch level forgedCurrent forgedSibling honestCurrent honestSibling forgedOutput
    hforgedCached hne heq hhonest

theorem MerkleWitness.toCachedCollision
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (witness : MerkleWitness execution) : CachedMerkleCollision execution :=
  OrientedMerkleWitness.withCachedQuery adversary keyResult hkeygen execution hafter
    (MerkleWitness.toOriented execution witness)

theorem CachedMerkleCollision.afterKeygen_orientation
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (collision : CachedMerkleCollision execution) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  obtain ⟨epoch, level, forgedCurrent, forgedSibling, honestCurrent, honestSibling,
      forgedOutput, hforgedCached, hne, heq, hhonest⟩ := collision
  have hkeys := detailedGameAfterKeygen_keys_eq adversary keyResult.1.1 keyResult.1.2
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
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (witness : MerkleWitness execution) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) :=
  CachedMerkleCollision.afterKeygen_orientation adversary keyResult hkeygen execution hafter
    (MerkleWitness.toCachedCollision adversary keyResult hkeygen execution hafter witness)

end XmssSecurity

