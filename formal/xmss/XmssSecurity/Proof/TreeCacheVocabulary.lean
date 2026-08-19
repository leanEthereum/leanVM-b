import XmssSecurity.Proof.KeygenCache
import XmssSecurity.Proof.CausalTreeTableIndependence
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec

namespace XmssSecurity

def MerkleHashInput
    (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ level node, AtHashAddress parameter (.merkle level node) input

def LeafCacheOutputsCorrespond
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (left right : QueryCache HashSpec) : Prop :=
  ∀ epoch,
    left (Concrete.CacheView.leafInput parameter epoch
      (leftEndpoints epoch)) =
    right (Concrete.CacheView.leafInput parameter epoch
      (rightEndpoints epoch))

def LeafReplayOutputsCorrespondOn
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (indices : List TreeValueIndex)
    (leftCache rightCache : QueryCache HashSpec) : Prop :=
  ∀ index ∈ indices,
    leftCache (Concrete.CacheView.leafInput parameter index.node
      (Concrete.CacheReplay.oneTimePublicKey leftCache parameter
        leftSecret index.node)) =
    rightCache (Concrete.CacheView.leafInput parameter index.node
      (Concrete.CacheReplay.oneTimePublicKey rightCache parameter
        rightSecret index.node))

def LeafReplayOutputsCorrespond
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec) : Prop :=
  ∀ epoch,
    leftCache (Concrete.CacheView.leafInput parameter epoch
      (Concrete.CacheReplay.oneTimePublicKey leftCache parameter
        leftSecret epoch)) =
    rightCache (Concrete.CacheView.leafInput parameter epoch
      (Concrete.CacheReplay.oneTimePublicKey rightCache parameter
        rightSecret epoch))

def ReplayEndpointsMatch
    (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest)
    (endpoints : Epoch → ChainIndex → Digest)
    (cache : QueryCache HashSpec) : Prop :=
  ∀ epoch,
    endpoints epoch =
      Concrete.CacheReplay.oneTimePublicKey cache parameter secret epoch

theorem leafReplayOutputsCorrespondOn_allLeaves
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : LeafReplayOutputsCorrespondOn parameter leftSecret rightSecret
      (treeValueIndicesAtHeight 0) leftCache rightCache) :
    LeafReplayOutputsCorrespond parameter leftSecret rightSecret
      leftCache rightCache := by
  intro epoch
  let index : TreeValueIndex := ⟨0, epoch⟩
  apply hrel index
  unfold treeValueIndicesAtHeight index
  exact List.mem_ofFn.mpr ⟨epoch, rfl⟩

theorem Concrete.CacheView.chainInput_ne_merkleInput
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) (level : MerkleLevel)
    (node : MerkleNode) (left right : Digest) :
    Concrete.CacheView.chainInput parameter epoch chain step value ≠
      Concrete.CacheView.merkleInput parameter level node left right := by
  intro heq
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
  simp at hdomain

theorem Concrete.CacheView.leafInput_ne_merkleInput
    (parameter : PublicParameter) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) (level : MerkleLevel)
    (node : MerkleNode) (left right : Digest) :
    Concrete.CacheView.leafInput parameter epoch endpoints ≠
      Concrete.CacheView.merkleInput parameter level node left right := by
  intro heq
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
  simp at hdomain

theorem Concrete.CacheView.chainStep_cacheQuery_merkleInput
    (cache : QueryCache HashSpec) (output : HashOutput)
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest) :
    Concrete.CacheView.chainStep
        (cache.cacheQuery
          (Concrete.CacheView.merkleInput parameter level node left right)
          output) parameter epoch chain =
      Concrete.CacheView.chainStep cache parameter epoch chain := by
  funext position value
  unfold Concrete.CacheView.chainStep
  split
  · unfold Concrete.CacheView.digestAt
    rw [QueryCache.cacheQuery_of_ne]
    exact Concrete.CacheView.chainInput_ne_merkleInput parameter epoch chain
      _ value level node left right
  · rfl

theorem Concrete.CacheReplay.oneTimePublicKey_cacheQuery_merkleInput
    (cache : QueryCache HashSpec) (output : HashOutput)
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) :
    Concrete.CacheReplay.oneTimePublicKey
        (cache.cacheQuery
          (Concrete.CacheView.merkleInput parameter level node left right)
          output) parameter secret epoch =
      Concrete.CacheReplay.oneTimePublicKey cache parameter secret epoch := by
  unfold Concrete.CacheReplay.oneTimePublicKey
  funext chain
  rw [Concrete.CacheView.chainStep_cacheQuery_merkleInput]

theorem ReplayEndpointsMatch.cacheQuery_merkleInput
    (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest)
    (endpoints : Epoch → ChainIndex → Digest)
    (cache : QueryCache HashSpec)
    (hrel : ReplayEndpointsMatch parameter secret endpoints cache)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest)
    (output : HashOutput) :
    ReplayEndpointsMatch parameter secret endpoints
      (cache.cacheQuery
        (Concrete.CacheView.merkleInput parameter level node left right)
        output) := by
  intro epoch
  rw [Concrete.CacheReplay.oneTimePublicKey_cacheQuery_merkleInput]
  exact hrel epoch

theorem LeafCacheOutputsCorrespond.cacheQuery_distinct
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (left right : QueryCache HashSpec)
    (hrel : LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      left right)
    (leftInput rightInput : HashInput) (output : HashOutput)
    (hleft : ∀ epoch, leftInput ≠ Concrete.CacheView.leafInput parameter
      epoch (leftEndpoints epoch))
    (hright : ∀ epoch, rightInput ≠ Concrete.CacheView.leafInput parameter
      epoch (rightEndpoints epoch)) :
    LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      (left.cacheQuery leftInput output) (right.cacheQuery rightInput output) := by
  intro epoch
  rw [QueryCache.cacheQuery_of_ne left output (hleft epoch).symm,
    QueryCache.cacheQuery_of_ne right output (hright epoch).symm]
  exact hrel epoch

theorem Concrete.CacheView.leafInput_eq_iff
    (parameter : PublicParameter)
    (leftEpoch rightEpoch : Epoch)
    (leftEndpoints rightEndpoints : ChainIndex → Digest) :
    Concrete.CacheView.leafInput parameter leftEpoch leftEndpoints =
        Concrete.CacheView.leafInput parameter rightEpoch rightEndpoints ↔
      leftEpoch = rightEpoch ∧ leftEndpoints = rightEndpoints := by
  constructor
  · intro heq
    have hepoch : leftEpoch = rightEpoch := by
      have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
      simpa using hdomain
    subst rightEpoch
    exact ⟨rfl, Concrete.CacheView.leafInput_injective parameter leftEpoch heq⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem LeafCacheOutputsCorrespond.cacheQuery_pair_update
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (left right : QueryCache HashSpec)
    (hrel : LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      left right)
    (epoch : Epoch)
    (newLeft newRight : ChainIndex → Digest) (output : HashOutput) :
    LeafCacheOutputsCorrespond parameter
      (Function.update leftEndpoints epoch newLeft)
      (Function.update rightEndpoints epoch newRight)
      (left.cacheQuery
        (Concrete.CacheView.leafInput parameter epoch newLeft) output)
      (right.cacheQuery
        (Concrete.CacheView.leafInput parameter epoch newRight) output) := by
  classical
  intro candidate
  by_cases hepoch : candidate = epoch
  · subst candidate
    rw [show Function.update leftEndpoints epoch newLeft epoch = newLeft by
        simp,
      show Function.update rightEndpoints epoch newRight epoch = newRight by
        simp]
    simp only [QueryCache.cacheQuery_self]
  · have hleftUpdate :
        Function.update leftEndpoints epoch newLeft candidate =
          leftEndpoints candidate := by
      simp [hepoch]
    have hrightUpdate :
        Function.update rightEndpoints epoch newRight candidate =
          rightEndpoints candidate := by
      simp [hepoch]
    rw [hleftUpdate, hrightUpdate]
    rw [QueryCache.cacheQuery_of_ne left output (by
        intro heq
        exact hepoch ((Concrete.CacheView.leafInput_eq_iff parameter candidate
          epoch (leftEndpoints candidate) newLeft).mp heq).1),
      QueryCache.cacheQuery_of_ne right output (by
        intro heq
        exact hepoch ((Concrete.CacheView.leafInput_eq_iff parameter candidate
          epoch (rightEndpoints candidate) newRight).mp heq).1)]
    exact hrel candidate

def chainEndpointDigit : Digit :=
  ⟨chainLength - 1, by decide⟩

end XmssSecurity
