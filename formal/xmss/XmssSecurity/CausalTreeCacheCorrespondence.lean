import XmssSecurity.CausalSigningKeygenCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

def MerkleHashInput
    (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ level node, AtHashAddress parameter (.merkle level node) input

def TreeRetainedHashInput
    (parameter : PublicParameter) (selected : ChainIndex)
    (input : HashInput) : Prop :=
  OutsideChainHashInput parameter selected input ∨
    MerkleHashInput parameter input

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

theorem LeafReplayOutputsCorrespond.cacheQuery_merkleInput
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : LeafReplayOutputsCorrespond parameter leftSecret rightSecret
      leftCache rightCache)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest)
    (output : HashOutput) :
    LeafReplayOutputsCorrespond parameter leftSecret rightSecret
      (leftCache.cacheQuery
        (Concrete.CacheView.merkleInput parameter level node left right) output)
      (rightCache.cacheQuery
        (Concrete.CacheView.merkleInput parameter level node left right) output) := by
  intro epoch
  rw [Concrete.CacheReplay.oneTimePublicKey_cacheQuery_merkleInput,
    Concrete.CacheReplay.oneTimePublicKey_cacheQuery_merkleInput,
    QueryCache.cacheQuery_of_ne, QueryCache.cacheQuery_of_ne]
  · exact hrel epoch
  · exact Concrete.CacheView.leafInput_ne_merkleInput parameter epoch
      (Concrete.CacheReplay.oneTimePublicKey rightCache parameter
        rightSecret epoch) level node left right
  · exact Concrete.CacheView.leafInput_ne_merkleInput parameter epoch
      (Concrete.CacheReplay.oneTimePublicKey leftCache parameter
        leftSecret epoch) level node left right

structure CoupledTreeCacheCorrespondence
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec) : Prop where
  retained : HashCachesAgreeOn
    (TreeRetainedHashInput parameter selected) leftCache rightCache
  leaves : LeafCacheOutputsCorrespond parameter
    leftEndpoints rightEndpoints leftCache rightCache

theorem Concrete.CacheReplay.cache_eq_of_zero_query_bound
    (computation : OracleComp HashSpec α) (target : HashInput)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hbound : computation.IsQueryBoundP (· = target) 0)
    (hmem : (result, finalCache) ∈ support
      ((simulateQ randomOracle computation).run initialCache)) :
    finalCache target = initialCache target := by
  cases hinitial : initialCache target with
  | none =>
      exact Concrete.CacheReplay.cache_none_of_zero_query_bound computation
        target initialCache finalCache result hbound hinitial hmem
  | some output =>
      exact Concrete.CacheReplay.randomOracle_cache_le computation initialCache
        (result, finalCache) hmem hinitial

theorem CoupledTreeCacheCorrespondence.of_oneTimePublicKey_runs
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftCache rightCache)
    (epoch : Epoch)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftResult rightResult :
      (ChainIndex → Digest) × QueryCache HashSpec)
    (hleft : leftResult ∈ support
      ((simulateQ randomOracle
        (Concrete.oneTimePublicKey parameter leftSecret epoch)).run leftCache))
    (hright : rightResult ∈ support
      ((simulateQ randomOracle
        (Concrete.oneTimePublicKey parameter rightSecret epoch)).run rightCache))
    (houtside : HashCachesAgreeOn
      (OutsideChainHashInput parameter selected)
      leftResult.2 rightResult.2) :
    CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftResult.2 rightResult.2 := by
  constructor
  · intro input hinput
    rcases hinput with houtsideInput | ⟨level, node, hmerkle⟩
    · exact houtside input houtsideInput
    · calc
        leftResult.2 input = leftCache input :=
          Concrete.CacheReplay.cache_eq_of_zero_query_bound
            (Concrete.oneTimePublicKey parameter leftSecret epoch) input
              leftCache leftResult.2 leftResult.1
              (OracleComp.IsQueryBoundP.of_imp
                (p' := AtHashAddress parameter (.merkle level node))
                (fun candidate heq => heq ▸ hmerkle)
                (Concrete.oneTimePublicKey_queryBound_zero_merkleAddress
                  parameter leftSecret epoch level node)) hleft
        _ = rightCache input := hrel.retained input (Or.inr ⟨level, node, hmerkle⟩)
        _ = rightResult.2 input :=
          (Concrete.CacheReplay.cache_eq_of_zero_query_bound
            (Concrete.oneTimePublicKey parameter rightSecret epoch) input
              rightCache rightResult.2 rightResult.1
              (OracleComp.IsQueryBoundP.of_imp
                (p' := AtHashAddress parameter (.merkle level node))
                (fun candidate heq => heq ▸ hmerkle)
                (Concrete.oneTimePublicKey_queryBound_zero_merkleAddress
                  parameter rightSecret epoch level node)) hright).symm
  · intro targetEpoch
    let leftInput := Concrete.CacheView.leafInput parameter targetEpoch
      (leftEndpoints targetEpoch)
    let rightInput := Concrete.CacheView.leafInput parameter targetEpoch
      (rightEndpoints targetEpoch)
    calc
      leftResult.2 leftInput = leftCache leftInput :=
        Concrete.CacheReplay.cache_eq_of_zero_query_bound
          (Concrete.oneTimePublicKey parameter leftSecret epoch) leftInput
            leftCache leftResult.2 leftResult.1
            (OracleComp.IsQueryBoundP.of_imp
              (p' := AtHashAddress parameter (.leaf targetEpoch))
              (fun candidate heq => heq ▸ (by
                simp [leftInput, Concrete.CacheView.leafInput]))
              (Concrete.oneTimePublicKey_queryBound_zero_leafAddress
                parameter leftSecret epoch targetEpoch)) hleft
      _ = rightCache rightInput := hrel.leaves targetEpoch
      _ = rightResult.2 rightInput :=
        (Concrete.CacheReplay.cache_eq_of_zero_query_bound
          (Concrete.oneTimePublicKey parameter rightSecret epoch) rightInput
            rightCache rightResult.2 rightResult.1
            (OracleComp.IsQueryBoundP.of_imp
              (p' := AtHashAddress parameter (.leaf targetEpoch))
              (fun candidate heq => heq ▸ (by
                simp [rightInput, Concrete.CacheView.leafInput]))
              (Concrete.oneTimePublicKey_queryBound_zero_leafAddress
                parameter rightSecret epoch targetEpoch)) hright).symm

theorem coupledFixedChainMaterialInvariant_initialTreeCacheCorrespondence
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hrel : CoupledFixedChainMaterialInvariant parameter selected left right)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest) :
    CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints
      left.2.2.2 right.1.2.2.2 := by
  constructor
  · intro input hinput
    rcases hinput with houtside | ⟨level, node, hmerkle⟩
    · exact hrel.cachesAgree input houtside
    · rw [hrel.leftMerkleFresh level node input hmerkle,
        hrel.rightMerkleFresh level node input hmerkle]
  · intro epoch
    rw [hrel.leftLeafFresh epoch _ (by
          simp [Concrete.CacheView.leafInput]),
      hrel.rightLeafFresh epoch _ (by
          simp [Concrete.CacheView.leafInput])]

theorem treeRetainedHashInput_ne_leafInput
    (parameter : PublicParameter) (selected : ChainIndex)
    (epoch : Epoch) (endpoints : ChainIndex → Digest)
    (input : HashInput)
    (hinput : TreeRetainedHashInput parameter selected input) :
    input ≠ Concrete.CacheView.leafInput parameter epoch endpoints := by
  rcases hinput with houtside | ⟨level, node, hmerkle⟩
  · exact outsideChainHashInput_ne_leafInput parameter selected epoch
      endpoints input houtside
  · intro heq
    have hleaf : AtHashAddress parameter (.leaf epoch) input := by
      rw [heq]
      simp [Concrete.CacheView.leafInput]
    have hdomain := atHashAddress_unique parameter (.merkle level node)
      (.leaf epoch) input hmerkle hleaf
    simp at hdomain

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

theorem LeafCacheOutputsCorrespond.cacheQuery_pair
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (left right : QueryCache HashSpec)
    (hrel : LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      left right)
    (epoch : Epoch) (output : HashOutput) :
    LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      (left.cacheQuery
        (Concrete.CacheView.leafInput parameter epoch (leftEndpoints epoch))
        output)
      (right.cacheQuery
        (Concrete.CacheView.leafInput parameter epoch (rightEndpoints epoch))
        output) := by
  intro candidate
  by_cases hepoch : candidate = epoch
  · subst candidate
    simp
  · rw [QueryCache.cacheQuery_of_ne left output (by
        intro heq
        exact hepoch ((Concrete.CacheView.leafInput_eq_iff parameter candidate
          epoch (leftEndpoints candidate) (leftEndpoints epoch)).mp heq).1),
      QueryCache.cacheQuery_of_ne right output (by
        intro heq
        exact hepoch ((Concrete.CacheView.leafInput_eq_iff parameter candidate
          epoch (rightEndpoints candidate) (rightEndpoints epoch)).mp heq).1)]
    exact hrel candidate

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

theorem CoupledTreeCacheCorrespondence.cacheQuery_retained
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftCache rightCache)
    (input : HashInput) (output : HashOutput)
    (hinput : TreeRetainedHashInput parameter selected input) :
    CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints
      (leftCache.cacheQuery input output)
      (rightCache.cacheQuery input output) := by
  constructor
  · exact hrel.retained.cacheQuery
      (TreeRetainedHashInput parameter selected) leftCache rightCache input output
  · apply hrel.leaves.cacheQuery_distinct
    · intro epoch
      exact (treeRetainedHashInput_ne_leafInput parameter selected epoch
        (leftEndpoints epoch) input hinput)
    · intro epoch
      exact (treeRetainedHashInput_ne_leafInput parameter selected epoch
        (rightEndpoints epoch) input hinput)

theorem CoupledTreeCacheCorrespondence.cacheQuery_leafPair
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftCache rightCache)
    (epoch : Epoch) (output : HashOutput) :
    CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints
      (leftCache.cacheQuery
        (Concrete.CacheView.leafInput parameter epoch
          (leftEndpoints epoch)) output)
      (rightCache.cacheQuery
        (Concrete.CacheView.leafInput parameter epoch
          (rightEndpoints epoch)) output) := by
  constructor
  · apply HashCachesAgreeOn.cacheQuery_distinct
      (TreeRetainedHashInput parameter selected) leftCache rightCache
        hrel.retained
    · intro input hinput
      exact treeRetainedHashInput_ne_leafInput parameter selected epoch
        (leftEndpoints epoch) input hinput
    · intro input hinput
      exact treeRetainedHashInput_ne_leafInput parameter selected epoch
        (rightEndpoints epoch) input hinput
  · exact hrel.leaves.cacheQuery_pair parameter
      leftEndpoints rightEndpoints leftCache rightCache epoch output

theorem CoupledTreeCacheCorrespondence.cacheQuery_leafPair_update
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftCache rightCache)
    (epoch : Epoch)
    (newLeft newRight : ChainIndex → Digest) (output : HashOutput) :
    CoupledTreeCacheCorrespondence parameter selected
      (Function.update leftEndpoints epoch newLeft)
      (Function.update rightEndpoints epoch newRight)
      (leftCache.cacheQuery
        (Concrete.CacheView.leafInput parameter epoch newLeft) output)
      (rightCache.cacheQuery
        (Concrete.CacheView.leafInput parameter epoch newRight) output) := by
  constructor
  · apply HashCachesAgreeOn.cacheQuery_distinct
      (TreeRetainedHashInput parameter selected) leftCache rightCache
        hrel.retained
    · intro input hinput
      exact treeRetainedHashInput_ne_leafInput parameter selected epoch
        newLeft input hinput
    · intro input hinput
      exact treeRetainedHashInput_ne_leafInput parameter selected epoch
        newRight input hinput
  · exact hrel.leaves.cacheQuery_pair_update parameter leftEndpoints
      rightEndpoints leftCache rightCache epoch newLeft newRight output

theorem relTriple_randomOracle_leafPair_of_both_none
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftCache rightCache)
    (epoch : Epoch) (newLeft newRight : ChainIndex → Digest)
    (hleftNone : leftCache
      (Concrete.CacheView.leafInput parameter epoch newLeft) = none)
    (hrightNone : rightCache
      (Concrete.CacheView.leafInput parameter epoch newRight) = none) :
    RelTriple
      ((randomOracle
        (Concrete.CacheView.leafInput parameter epoch newLeft)).run leftCache)
      ((randomOracle
        (Concrete.CacheView.leafInput parameter epoch newRight)).run rightCache)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          CoupledTreeCacheCorrespondence parameter selected
            (Function.update leftEndpoints epoch newLeft)
            (Function.update rightEndpoints epoch newRight)
            leftResult.2 rightResult.2) := by
  rw [randomOracle, QueryImpl.withCaching_run_none _ hleftNone,
    QueryImpl.withCaching_run_none _ hrightNone,
    map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
  intro leftOutput rightOutput houtput
  subst rightOutput
  apply relTriple_pure_pure
  exact ⟨rfl, hrel.cacheQuery_leafPair_update parameter selected
    leftEndpoints rightEndpoints leftCache rightCache epoch newLeft newRight
      leftOutput⟩

theorem relTriple_randomOracle_retained
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftCache rightCache)
    (input : HashInput)
    (hinput : TreeRetainedHashInput parameter selected input) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((randomOracle input).run rightCache)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          CoupledTreeCacheCorrespondence parameter selected
            leftEndpoints rightEndpoints leftResult.2 rightResult.2) := by
  cases hleft : leftCache input with
  | none =>
      have hright : rightCache input = none := by
        rw [← hrel.retained input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft,
        QueryImpl.withCaching_run_none _ hright,
        map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
      intro leftOutput rightOutput houtput
      subst rightOutput
      apply relTriple_pure_pure
      exact ⟨rfl, hrel.cacheQuery_retained parameter selected
        leftEndpoints rightEndpoints leftCache rightCache input leftOutput
          hinput⟩
  | some output =>
      have hright : rightCache input = some output := by
        rw [← hrel.retained input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
        QueryImpl.withCaching_run_some _ hright]
      exact relTriple_pure_pure ⟨rfl, hrel⟩

theorem relTriple_randomOracle_merkle_with_replay
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hcache : CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftCache rightCache)
    (hreplay : LeafReplayOutputsCorrespond parameter leftSecret rightSecret
      leftCache rightCache)
    (level : MerkleLevel) (node : MerkleNode)
    (leftChild rightChild : Digest) :
    RelTriple
      ((randomOracle (Concrete.CacheView.merkleInput parameter level node
        leftChild rightChild)).run leftCache)
      ((randomOracle (Concrete.CacheView.merkleInput parameter level node
        leftChild rightChild)).run rightCache)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          CoupledTreeCacheCorrespondence parameter selected
            leftEndpoints rightEndpoints leftResult.2 rightResult.2 ∧
          LeafReplayOutputsCorrespond parameter leftSecret rightSecret
            leftResult.2 rightResult.2) := by
  let input := Concrete.CacheView.merkleInput parameter level node
    leftChild rightChild
  have hinput : TreeRetainedHashInput parameter selected input := by
    right
    exact ⟨level, node, by simp [input, Concrete.CacheView.merkleInput]⟩
  cases hleft : leftCache input with
  | none =>
      have hright : rightCache input = none := by
        rw [← hcache.retained input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft,
        QueryImpl.withCaching_run_none _ hright,
        map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
      intro leftOutput rightOutput houtput
      subst rightOutput
      apply relTriple_pure_pure
      exact ⟨rfl, hcache.cacheQuery_retained parameter selected
          leftEndpoints rightEndpoints leftCache rightCache input leftOutput
            hinput,
        hreplay.cacheQuery_merkleInput parameter leftSecret rightSecret
          leftCache rightCache level node leftChild rightChild leftOutput⟩
  | some output =>
      have hright : rightCache input = some output := by
        rw [← hcache.retained input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
        QueryImpl.withCaching_run_some _ hright]
      exact relTriple_pure_pure ⟨rfl, hcache, hreplay⟩

theorem relTriple_leafHash_run_of_treeCacheCorrespondence
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftCache rightCache)
    (epoch : Epoch) (newLeft newRight : ChainIndex → Digest)
    (hleftNone : leftCache
      (Concrete.CacheView.leafInput parameter epoch newLeft) = none)
    (hrightNone : rightCache
      (Concrete.CacheView.leafInput parameter epoch newRight) = none) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.leafHash parameter epoch newLeft :
          OracleComp HashSpec Digest)).run leftCache)
      ((simulateQ randomOracle
        (Concrete.leafHash parameter epoch newRight :
          OracleComp HashSpec Digest)).run rightCache)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          CoupledTreeCacheCorrespondence parameter selected
            (Function.update leftEndpoints epoch newLeft)
            (Function.update rightEndpoints epoch newRight)
            leftResult.2 rightResult.2) := by
  change RelTriple
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$>
        (randomOracle (Concrete.CacheView.leafInput parameter epoch newLeft)).run
          leftCache)
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$>
        (randomOracle (Concrete.CacheView.leafInput parameter epoch newRight)).run
          rightCache) _
  apply relTriple_map
  apply relTriple_post_mono
    (relTriple_randomOracle_leafPair_of_both_none parameter selected
      leftEndpoints rightEndpoints leftCache rightCache hrel epoch
        newLeft newRight hleftNone hrightNone)
  intro leftResult rightResult hresult
  exact ⟨congrArg truncateHash hresult.1, hresult.2⟩

theorem relTriple_nodeHash_run_of_treeCacheCorrespondence
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftCache rightCache)
    (level : MerkleLevel) (node : MerkleNode)
    (leftChild rightChild : Digest) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.nodeHash parameter level node leftChild rightChild :
          OracleComp HashSpec Digest)).run leftCache)
      ((simulateQ randomOracle
        (Concrete.nodeHash parameter level node leftChild rightChild :
          OracleComp HashSpec Digest)).run rightCache)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          CoupledTreeCacheCorrespondence parameter selected
            leftEndpoints rightEndpoints leftResult.2 rightResult.2) := by
  let input := Concrete.CacheView.merkleInput parameter level node
    leftChild rightChild
  have hinput : TreeRetainedHashInput parameter selected input := by
    right
    exact ⟨level, node, by simp [input, Concrete.CacheView.merkleInput]⟩
  change RelTriple
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$> (randomOracle input).run leftCache)
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$> (randomOracle input).run rightCache) _
  apply relTriple_map
  apply relTriple_post_mono
    (relTriple_randomOracle_retained parameter selected leftEndpoints
      rightEndpoints leftCache rightCache hrel input hinput)
  intro leftResult rightResult hresult
  exact ⟨congrArg truncateHash hresult.1, hresult.2⟩

theorem relTriple_nodeHash_run_with_replayCorrespondence
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hcache : CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftCache rightCache)
    (hreplay : LeafReplayOutputsCorrespond parameter leftSecret rightSecret
      leftCache rightCache)
    (level : MerkleLevel) (node : MerkleNode)
    (leftChild rightChild : Digest) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.nodeHash parameter level node leftChild rightChild :
          OracleComp HashSpec Digest)).run leftCache)
      ((simulateQ randomOracle
        (Concrete.nodeHash parameter level node leftChild rightChild :
          OracleComp HashSpec Digest)).run rightCache)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          CoupledTreeCacheCorrespondence parameter selected
            leftEndpoints rightEndpoints leftResult.2 rightResult.2 ∧
          LeafReplayOutputsCorrespond parameter leftSecret rightSecret
            leftResult.2 rightResult.2) := by
  change RelTriple
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$>
        (randomOracle (Concrete.CacheView.merkleInput parameter level node
          leftChild rightChild)).run leftCache)
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$>
        (randomOracle (Concrete.CacheView.merkleInput parameter level node
          leftChild rightChild)).run rightCache) _
  apply relTriple_map
  apply relTriple_post_mono
    (relTriple_randomOracle_merkle_with_replay parameter selected
      leftEndpoints rightEndpoints leftSecret rightSecret leftCache rightCache
        hcache hreplay level node leftChild rightChild)
  intro leftResult rightResult hresult
  exact ⟨congrArg truncateHash hresult.1, hresult.2⟩

theorem relTriple_treeNode_succ_run_with_treeCacheCorrespondence
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) (hlevel : levels < treeHeight)
    (leftChild rightChild : Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hleftLeft :
      (simulateQ randomOracle
        (Concrete.treeNode parameter leftSecret levels
          (Concrete.childNode node false) : OracleComp HashSpec Digest)).run
            leftCache = pure (leftChild, leftCache))
    (hleftRight :
      (simulateQ randomOracle
        (Concrete.treeNode parameter rightSecret levels
          (Concrete.childNode node false) : OracleComp HashSpec Digest)).run
            rightCache = pure (leftChild, rightCache))
    (hrightLeft :
      (simulateQ randomOracle
        (Concrete.treeNode parameter leftSecret levels
          (Concrete.childNode node true) : OracleComp HashSpec Digest)).run
            leftCache = pure (rightChild, leftCache))
    (hrightRight :
      (simulateQ randomOracle
        (Concrete.treeNode parameter rightSecret levels
          (Concrete.childNode node true) : OracleComp HashSpec Digest)).run
            rightCache = pure (rightChild, rightCache))
    (hcache : CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftCache rightCache)
    (hreplay : LeafReplayOutputsCorrespond parameter leftSecret rightSecret
      leftCache rightCache) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.treeNode parameter leftSecret (levels + 1) node :
          OracleComp HashSpec Digest)).run leftCache)
      ((simulateQ randomOracle
        (Concrete.treeNode parameter rightSecret (levels + 1) node :
          OracleComp HashSpec Digest)).run rightCache)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          CoupledTreeCacheCorrespondence parameter selected
            leftEndpoints rightEndpoints leftResult.2 rightResult.2 ∧
          LeafReplayOutputsCorrespond parameter leftSecret rightSecret
            leftResult.2 rightResult.2) := by
  simp only [Concrete.treeNode_succ_eq, simulateQ_bind, StateT.run_bind,
    hleftLeft, hleftRight, hrightLeft, hrightRight, pure_bind,
    hlevel, ↓reduceDIte]
  exact relTriple_nodeHash_run_with_replayCorrespondence parameter selected
    leftEndpoints rightEndpoints leftSecret rightSecret leftCache rightCache
      hcache hreplay ⟨levels, hlevel⟩ node leftChild rightChild

theorem relTriple_fixedChainMaterial_leafAt_run_with_treeCacheCorrespondence
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hmaterial : CoupledFixedChainMaterialInvariant
      parameter selected left right)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (epoch : Epoch)
    (leftCache rightCache : QueryCache HashSpec)
    (hcache : CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftCache rightCache)
    (hleftLe : left.2.2.2 ≤ leftCache)
    (hrightLe : right.1.2.2.2 ≤ rightCache)
    (hleftAbsent : ∀ input, AtHashAddress parameter (.leaf epoch) input →
      leftCache input = none)
    (hrightAbsent : ∀ input, AtHashAddress parameter (.leaf epoch) input →
      rightCache input = none) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.leafAt parameter (unflattenSecret left.1.2) epoch :
          OracleComp HashSpec Digest)).run leftCache)
      ((simulateQ randomOracle
        (Concrete.leafAt parameter (unflattenSecret right.1.1.2) epoch :
          OracleComp HashSpec Digest)).run rightCache)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          ∃ newLeft newRight,
            CoupledTreeCacheCorrespondence parameter selected
              (Function.update leftEndpoints epoch newLeft)
              (Function.update rightEndpoints epoch newRight)
              leftResult.2 rightResult.2 ∧
            newLeft = Concrete.CacheReplay.oneTimePublicKey leftResult.2
              parameter (unflattenSecret left.1.2) epoch ∧
            newRight = Concrete.CacheReplay.oneTimePublicKey rightResult.2
              parameter (unflattenSecret right.1.1.2) epoch) := by
  let leftOneTime :=
    (simulateQ randomOracle
      (Concrete.oneTimePublicKey parameter
        (unflattenSecret left.1.2) epoch)).run leftCache
  let rightOneTime :=
    (simulateQ randomOracle
      (Concrete.oneTimePublicKey parameter
        (unflattenSecret right.1.1.2) epoch)).run rightCache
  have honeTime : RelTriple leftOneTime rightOneTime
      (fun leftResult rightResult =>
        ((∀ candidate, candidate ≠ selected →
          leftResult.1 candidate = rightResult.1 candidate) ∧
        HashCachesAgreeOn (OutsideChainHashInput parameter selected)
          leftResult.2 rightResult.2 ∧
        left.2.2.2 ≤ leftResult.2 ∧
        right.1.2.2.2 ≤ rightResult.2) ∧
        leftResult ∈ support leftOneTime ∧
        rightResult ∈ support rightOneTime) := by
    apply relTriple_with_support
    exact relTriple_fixedChainMaterial_oneTimePublicKey_run_from_cache
      parameter selected left right hmaterial epoch leftCache rightCache
        (fun input hinput => hcache.retained input (Or.inl hinput))
          hleftLe hrightLe
  unfold Concrete.leafAt
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind honeTime
  intro leftOneTimeResult rightOneTimeResult honeTimeResult
  obtain ⟨honeTimeRelation, hleftSupport, hrightSupport⟩ := honeTimeResult
  have hcorrespond := hcache.of_oneTimePublicKey_runs parameter selected
    leftEndpoints rightEndpoints leftCache rightCache epoch
      (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
        leftOneTimeResult rightOneTimeResult hleftSupport hrightSupport
          honeTimeRelation.2.1
  have hleftNone := oneTimePublicKey_run_leafInput_none parameter
    (unflattenSecret left.1.2) epoch leftCache hleftAbsent
      leftOneTimeResult hleftSupport
  have hrightNone := oneTimePublicKey_run_leafInput_none parameter
    (unflattenSecret right.1.1.2) epoch rightCache hrightAbsent
      rightOneTimeResult hrightSupport
  apply relTriple_post_mono (relTriple_with_support
    (relTriple_leafHash_run_of_treeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftOneTimeResult.2 rightOneTimeResult.2
        hcorrespond epoch leftOneTimeResult.1 rightOneTimeResult.1
          hleftNone hrightNone))
  intro leftResult rightResult hresult
  obtain ⟨hleafRelation, hleftLeaf, hrightLeaf⟩ := hresult
  have hleftLeafLe := Concrete.CacheReplay.randomOracle_cache_le
    (Concrete.leafHash parameter epoch leftOneTimeResult.1 :
      OracleComp HashSpec Digest) leftOneTimeResult.2 leftResult hleftLeaf
  have hrightLeafLe := Concrete.CacheReplay.randomOracle_cache_le
    (Concrete.leafHash parameter epoch rightOneTimeResult.1 :
      OracleComp HashSpec Digest) rightOneTimeResult.2 rightResult hrightLeaf
  have hleftReplay := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.oneTimePublicKey parameter (unflattenSecret left.1.2) epoch :
      OracleComp HashSpec (ChainIndex → Digest)) leftCache leftOneTimeResult.2
      leftResult.2 leftOneTimeResult.1 hleftSupport hleftLeafLe
  have hrightReplay := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.oneTimePublicKey parameter (unflattenSecret right.1.1.2) epoch :
      OracleComp HashSpec (ChainIndex → Digest)) rightCache rightOneTimeResult.2
      rightResult.2 rightOneTimeResult.1 hrightSupport hrightLeafLe
  rw [Concrete.CacheReplay.eval_oneTimePublicKey] at hleftReplay hrightReplay
  exact ⟨hleafRelation.1, leftOneTimeResult.1, rightOneTimeResult.1,
    hleafRelation.2, hleftReplay.symm, hrightReplay.symm⟩

set_option maxRecDepth 100000 in
theorem relTriple_fixedChainMaterial_leafTreeValues_run_with_correspondence
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hmaterial : CoupledFixedChainMaterialInvariant
      parameter selected left right) :
    ∀ (indices : List TreeValueIndex),
      (∀ index ∈ indices, index.1.val = 0) →
      indices.Pairwise TreeValueIndex.Precedes →
      ∀ (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
        (leftCache rightCache : QueryCache HashSpec),
        TreeValuesFresh parameter indices leftCache →
        TreeValuesFresh parameter indices rightCache →
        CoupledTreeCacheCorrespondence parameter selected
          leftEndpoints rightEndpoints leftCache rightCache →
        left.2.2.2 ≤ leftCache → right.1.2.2.2 ≤ rightCache →
        RelTriple
          (treeValues parameter (unflattenSecret left.1.2) indices leftCache)
          (treeValues parameter (unflattenSecret right.1.1.2) indices rightCache)
          (fun leftResult rightResult =>
            leftResult.1 = rightResult.1 ∧
              ∃ finalLeft finalRight,
                CoupledTreeCacheCorrespondence parameter selected
                  finalLeft finalRight leftResult.2 rightResult.2 ∧
                LeafReplayOutputsCorrespondOn parameter
                  (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
                  indices leftResult.2 rightResult.2) := by
  intro indices
  induction indices with
  | nil =>
      intro _hzero _hordered leftEndpoints rightEndpoints leftCache rightCache
        _hleftFresh _hrightFresh hcache _hleftLe _hrightLe
      simp only [treeValues_nil]
      exact relTriple_pure_pure ⟨rfl, leftEndpoints, rightEndpoints, hcache,
        by simp [LeafReplayOutputsCorrespondOn]⟩
  | cons current indices ih =>
      intro hzero hordered leftEndpoints rightEndpoints leftCache rightCache
        hleftFresh hrightFresh hcache hleftLe hrightLe
      have hcurrentZero : current.1.val = 0 := hzero current (by simp)
      have htailZero : ∀ index ∈ indices, index.1.val = 0 := by
        intro index hindex
        exact hzero index (by simp [hindex])
      have hcurrentBefore : ∀ target ∈ indices,
          current.Precedes target := (List.pairwise_cons.mp hordered).1
      have htailOrdered : indices.Pairwise TreeValueIndex.Precedes :=
        (List.pairwise_cons.mp hordered).2
      have hleftAbsent : ∀ input,
          AtHashAddress parameter (.leaf current.node) input →
            leftCache input = none := by
        intro input hinput
        apply hleftFresh current (by simp) input
        unfold TreeValueIndex.domain
        rw [dif_pos hcurrentZero]
        exact hinput
      have hrightAbsent : ∀ input,
          AtHashAddress parameter (.leaf current.node) input →
            rightCache input = none := by
        intro input hinput
        apply hrightFresh current (by simp) input
        unfold TreeValueIndex.domain
        rw [dif_pos hcurrentZero]
        exact hinput
      have hhead : RelTriple
          ((simulateQ randomOracle
            (current.computation parameter (unflattenSecret left.1.2))).run
              leftCache)
          ((simulateQ randomOracle
            (current.computation parameter (unflattenSecret right.1.1.2))).run
              rightCache)
          (fun leftResult rightResult =>
            leftResult.1 = rightResult.1 ∧
              ∃ newLeft newRight,
                CoupledTreeCacheCorrespondence parameter selected
                  (Function.update leftEndpoints current.node newLeft)
                  (Function.update rightEndpoints current.node newRight)
                  leftResult.2 rightResult.2 ∧
                newLeft = Concrete.CacheReplay.oneTimePublicKey leftResult.2
                  parameter (unflattenSecret left.1.2) current.node ∧
                newRight = Concrete.CacheReplay.oneTimePublicKey rightResult.2
                  parameter (unflattenSecret right.1.1.2) current.node) := by
        simpa [TreeValueIndex.computation, hcurrentZero] using
          (relTriple_fixedChainMaterial_leafAt_run_with_treeCacheCorrespondence
            parameter selected left right hmaterial leftEndpoints rightEndpoints
              current.node leftCache rightCache hcache hleftLe hrightLe
                hleftAbsent hrightAbsent)
      have hheadSupport := relTriple_with_support hhead
      simp only [treeValues_cons]
      apply relTriple_bind hheadSupport
      intro leftHeadResult rightHeadResult hheadResult
      obtain ⟨hheadRelation, hleftHeadSupport, hrightHeadSupport⟩ := hheadResult
      obtain ⟨hheadValue, nextLeft, nextRight, hnextCache,
        hnextLeft, hnextRight⟩ := hheadRelation
      have hleftTailFresh := treeValue_preserves_tail_fresh parameter
        (unflattenSecret left.1.2) current indices hcurrentBefore leftCache
          hleftFresh leftHeadResult hleftHeadSupport
      have hrightTailFresh := treeValue_preserves_tail_fresh parameter
        (unflattenSecret right.1.1.2) current indices hcurrentBefore rightCache
          hrightFresh rightHeadResult hrightHeadSupport
      have hleftNextLe : left.2.2.2 ≤ leftHeadResult.2 := hleftLe.trans
        (Concrete.CacheReplay.randomOracle_cache_le
          (current.computation parameter (unflattenSecret left.1.2))
            leftCache leftHeadResult (by
              simpa [TreeValueIndex.computation, hcurrentZero] using
                hleftHeadSupport))
      have hrightNextLe : right.1.2.2.2 ≤ rightHeadResult.2 := hrightLe.trans
        (Concrete.CacheReplay.randomOracle_cache_le
          (current.computation parameter (unflattenSecret right.1.1.2))
            rightCache rightHeadResult (by
              simpa [TreeValueIndex.computation, hcurrentZero] using
                hrightHeadSupport))
      apply relTriple_bind
        (relTriple_with_support (ih htailZero htailOrdered
          (Function.update leftEndpoints current.node nextLeft)
          (Function.update rightEndpoints current.node nextRight)
          leftHeadResult.2 rightHeadResult.2 hleftTailFresh hrightTailFresh
            hnextCache hleftNextLe hrightNextLe))
      intro leftTailResult rightTailResult htailResult
      obtain ⟨htailRelation, hleftTailSupport, hrightTailSupport⟩ := htailResult
      obtain ⟨htailValues, finalLeft, finalRight, hfinalCache,
        htailReplay⟩ := htailRelation
      have hleftTailLe := treeValues_cache_le parameter
        (unflattenSecret left.1.2) indices leftHeadResult.2 leftTailResult
          hleftTailSupport
      have hrightTailLe := treeValues_cache_le parameter
        (unflattenSecret right.1.1.2) indices rightHeadResult.2 rightTailResult
          hrightTailSupport
      have hleftCurrentStable :=
        Concrete.CacheReplay.leafAt_oneTimePublicKey_eq_in_largerCache
          parameter (unflattenSecret left.1.2) current.node leftCache
            leftHeadResult.2 leftTailResult.2 leftHeadResult.1 (by
              simpa [TreeValueIndex.computation, hcurrentZero] using
                hleftHeadSupport) hleftTailLe
      have hrightCurrentStable :=
        Concrete.CacheReplay.leafAt_oneTimePublicKey_eq_in_largerCache
          parameter (unflattenSecret right.1.1.2) current.node rightCache
            rightHeadResult.2 rightTailResult.2 rightHeadResult.1 (by
              simpa [TreeValueIndex.computation, hcurrentZero] using
                hrightHeadSupport) hrightTailLe
      obtain ⟨leftOutput, hleftCached⟩ :=
        Concrete.CacheReplay.leafAt_query_cached parameter
          (unflattenSecret left.1.2) current.node leftCache leftHeadResult.2
            leftHeadResult.1 (by
              simpa [TreeValueIndex.computation, hcurrentZero] using
                hleftHeadSupport)
      have hheadReplay :
          leftHeadResult.2 (Concrete.CacheView.leafInput parameter current.node
            (Concrete.CacheReplay.oneTimePublicKey leftHeadResult.2 parameter
              (unflattenSecret left.1.2) current.node)) =
          rightHeadResult.2 (Concrete.CacheView.leafInput parameter current.node
            (Concrete.CacheReplay.oneTimePublicKey rightHeadResult.2 parameter
              (unflattenSecret right.1.1.2) current.node)) := by
        simpa [hnextLeft, hnextRight] using hnextCache.leaves current.node
      have hrightCached :
          rightHeadResult.2 (Concrete.CacheView.leafInput parameter current.node
            (Concrete.CacheReplay.oneTimePublicKey rightHeadResult.2 parameter
              (unflattenSecret right.1.1.2) current.node)) = some leftOutput := by
        rw [← hheadReplay]
        exact hleftCached
      apply relTriple_pure_pure
      refine ⟨congrArg₂ List.cons hheadValue htailValues,
        finalLeft, finalRight, hfinalCache, ?_⟩
      intro index hindex
      simp only [List.mem_cons] at hindex
      rcases hindex with rfl | hindex
      · rw [← hleftCurrentStable, ← hrightCurrentStable]
        exact (hleftTailLe hleftCached).trans
          (hrightTailLe hrightCached).symm
      · exact htailReplay index hindex

theorem relTriple_fixedChainMaterial_allLeafValues_run_with_correspondence
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hmaterial : CoupledFixedChainMaterialInvariant
      parameter selected left right) :
    RelTriple
      (treeValues parameter (unflattenSecret left.1.2)
        (treeValueIndicesAtHeight 0) left.2.2.2)
      (treeValues parameter (unflattenSecret right.1.1.2)
        (treeValueIndicesAtHeight 0) right.1.2.2.2)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          ∃ finalLeft finalRight,
            CoupledTreeCacheCorrespondence parameter selected
              finalLeft finalRight leftResult.2 rightResult.2 ∧
            LeafReplayOutputsCorrespond parameter
              (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
              leftResult.2 rightResult.2) := by
  have hzero : ∀ index ∈ treeValueIndicesAtHeight 0,
      index.1.val = 0 := by
    intro index hindex
    rw [treeValueIndicesAtHeight, List.mem_ofFn] at hindex
    obtain ⟨node, rfl⟩ := hindex
    rfl
  have hordered : (treeValueIndicesAtHeight 0).Pairwise
      TreeValueIndex.Precedes := by
    simp only [treeValueIndicesAtHeight, List.pairwise_ofFn]
    intro leftNode rightNode hlt
    exact Or.inr ⟨rfl, hlt⟩
  have hleftFresh : TreeValuesFresh parameter
      (treeValueIndicesAtHeight 0) left.2.2.2 := by
    intro index hindex input hinput
    have hheight := hzero index hindex
    unfold TreeValueIndex.domain at hinput
    rw [dif_pos hheight] at hinput
    exact hmaterial.leftLeafFresh index.node input hinput
  have hrightFresh : TreeValuesFresh parameter
      (treeValueIndicesAtHeight 0) right.1.2.2.2 := by
    intro index hindex input hinput
    have hheight := hzero index hindex
    unfold TreeValueIndex.domain at hinput
    rw [dif_pos hheight] at hinput
    exact hmaterial.rightLeafFresh index.node input hinput
  let initialEndpoints : Epoch → ChainIndex → Digest := fun _ _ => 0
  apply relTriple_post_mono
    (relTriple_fixedChainMaterial_leafTreeValues_run_with_correspondence
      parameter selected left right hmaterial (treeValueIndicesAtHeight 0)
        hzero hordered initialEndpoints initialEndpoints left.2.2.2 right.1.2.2.2
          hleftFresh hrightFresh
            (coupledFixedChainMaterialInvariant_initialTreeCacheCorrespondence
              parameter selected left right hmaterial initialEndpoints
                initialEndpoints) le_rfl le_rfl)
  intro leftResult rightResult hresult
  obtain ⟨hvalues, finalLeft, finalRight, hcache, hreplay⟩ := hresult
  exact ⟨hvalues, finalLeft, finalRight, hcache,
    leafReplayOutputsCorrespondOn_allLeaves parameter
      (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
      leftResult.2 rightResult.2 hreplay⟩

theorem relTriple_fixedChainMaterial_merkleTreeValue_run_with_correspondence
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (processed : List TreeValueIndex)
    (leftPrefix rightPrefix : List Digest × QueryCache HashSpec)
    (hleftPrefix : leftPrefix ∈ support
      (treeValues parameter (unflattenSecret left.1.2)
        processed left.2.2.2))
    (hrightPrefix : rightPrefix ∈ support
      (treeValues parameter (unflattenSecret right.1.1.2)
        processed right.1.2.2.2))
    (hprefixValues : leftPrefix.1 = rightPrefix.1)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (hcache : CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftPrefix.2 rightPrefix.2)
    (hreplay : LeafReplayOutputsCorrespond parameter
      (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
      leftPrefix.2 rightPrefix.2)
    (current : TreeValueIndex) (hpositive : 0 < current.1.val)
    (hleftChild : TreeValueIndex.ofSubtree (current.1.val - 1)
      (Concrete.childNode current.node false) (by omega)
      (childNode_subtreeValid (current.1.val - 1) current.node false
        (by simpa [Nat.sub_add_cancel hpositive] using current.subtreeValid)) ∈
        processed)
    (hrightChild : TreeValueIndex.ofSubtree (current.1.val - 1)
      (Concrete.childNode current.node true) (by omega)
      (childNode_subtreeValid (current.1.val - 1) current.node true
        (by simpa [Nat.sub_add_cancel hpositive] using current.subtreeValid)) ∈
        processed) :
    RelTriple
      ((simulateQ randomOracle
        (current.computation parameter (unflattenSecret left.1.2))).run
          leftPrefix.2)
      ((simulateQ randomOracle
        (current.computation parameter (unflattenSecret right.1.1.2))).run
          rightPrefix.2)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          CoupledTreeCacheCorrespondence parameter selected
            leftEndpoints rightEndpoints leftResult.2 rightResult.2 ∧
          LeafReplayOutputsCorrespond parameter
            (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
            leftResult.2 rightResult.2) := by
  let levels := current.1.val - 1
  have hsucc : current.1.val = levels + 1 := by
    dsimp [levels]
    omega
  have hlevel : levels < treeHeight := by
    dsimp [levels]
    omega
  have hparentValid : TreeSubtreeValid (levels + 1) current.node := by
    simpa [← hsucc] using current.subtreeValid
  let leftIndex := TreeValueIndex.ofSubtree levels
    (Concrete.childNode current.node false) (by omega)
      (childNode_subtreeValid levels current.node false hparentValid)
  let rightIndex := TreeValueIndex.ofSubtree levels
    (Concrete.childNode current.node true) (by omega)
      (childNode_subtreeValid levels current.node true hparentValid)
  have hleftIndex : leftIndex ∈ processed := by
    simpa [leftIndex, levels] using hleftChild
  have hrightIndex : rightIndex ∈ processed := by
    simpa [rightIndex, levels] using hrightChild
  have hleftReplay := treeValues_support_replay parameter
    (unflattenSecret left.1.2) processed left.2.2.2 leftPrefix hleftPrefix
  have hrightReplay := treeValues_support_replay parameter
    (unflattenSecret right.1.1.2) processed right.1.2.2.2 rightPrefix
      hrightPrefix
  have hleftChildEq := treeValuesReplay_eq_at_mem parameter parameter
    (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
    leftPrefix.2 rightPrefix.2 processed leftPrefix.1 hleftReplay
      (hprefixValues ▸ hrightReplay) leftIndex hleftIndex
  have hrightChildEq := treeValuesReplay_eq_at_mem parameter parameter
    (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
    leftPrefix.2 rightPrefix.2 processed leftPrefix.1 hleftReplay
      (hprefixValues ▸ hrightReplay) rightIndex hrightIndex
  let leftChild := Concrete.CacheReplay.treeNode leftPrefix.2 parameter
    (unflattenSecret left.1.2) levels (Concrete.childNode current.node false)
  let rightChild := Concrete.CacheReplay.treeNode leftPrefix.2 parameter
    (unflattenSecret left.1.2) levels (Concrete.childNode current.node true)
  have hleftLeft := treeValues_rerun_index_eq_pure parameter
    (unflattenSecret left.1.2) processed left.2.2.2 leftPrefix
      hleftPrefix leftIndex hleftIndex
  have hleftRight := treeValues_rerun_index_eq_pure parameter
    (unflattenSecret right.1.1.2) processed right.1.2.2.2 rightPrefix
      hrightPrefix leftIndex hleftIndex
  have hrightLeft := treeValues_rerun_index_eq_pure parameter
    (unflattenSecret left.1.2) processed left.2.2.2 leftPrefix
      hleftPrefix rightIndex hrightIndex
  have hrightRight := treeValues_rerun_index_eq_pure parameter
    (unflattenSecret right.1.1.2) processed right.1.2.2.2 rightPrefix
      hrightPrefix rightIndex hrightIndex
  have hleftChildEq' : leftChild =
      Concrete.CacheReplay.treeNode rightPrefix.2 parameter
        (unflattenSecret right.1.1.2) levels
          (Concrete.childNode current.node false) := by
    simpa [leftIndex, leftChild] using hleftChildEq
  have hrightChildEq' : rightChild =
      Concrete.CacheReplay.treeNode rightPrefix.2 parameter
        (unflattenSecret right.1.1.2) levels
          (Concrete.childNode current.node true) := by
    simpa [rightIndex, rightChild] using hrightChildEq
  have hleftLeft' :
      (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret left.1.2) levels
          (Concrete.childNode current.node false) :
          OracleComp HashSpec Digest)).run leftPrefix.2 =
        pure (leftChild, leftPrefix.2) := by
    change (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret left.1.2) levels
          (Concrete.childNode current.node false))).run leftPrefix.2 = _
      at hleftLeft
    exact hleftLeft
  have hleftRight' :
      (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret right.1.1.2) levels
          (Concrete.childNode current.node false) :
          OracleComp HashSpec Digest)).run rightPrefix.2 =
        pure (leftChild, rightPrefix.2) := by
    change (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret right.1.1.2) levels
          (Concrete.childNode current.node false))).run rightPrefix.2 =
      pure (Concrete.CacheReplay.treeNode rightPrefix.2 parameter
        (unflattenSecret right.1.1.2) levels
          (Concrete.childNode current.node false), rightPrefix.2) at hleftRight
    rw [hleftChildEq']
    exact hleftRight
  have hrightLeft' :
      (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret left.1.2) levels
          (Concrete.childNode current.node true) :
          OracleComp HashSpec Digest)).run leftPrefix.2 =
        pure (rightChild, leftPrefix.2) := by
    change (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret left.1.2) levels
          (Concrete.childNode current.node true))).run leftPrefix.2 = _
      at hrightLeft
    exact hrightLeft
  have hrightRight' :
      (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret right.1.1.2) levels
          (Concrete.childNode current.node true) :
          OracleComp HashSpec Digest)).run rightPrefix.2 =
        pure (rightChild, rightPrefix.2) := by
    change (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret right.1.1.2) levels
          (Concrete.childNode current.node true))).run rightPrefix.2 =
      pure (Concrete.CacheReplay.treeNode rightPrefix.2 parameter
        (unflattenSecret right.1.1.2) levels
          (Concrete.childNode current.node true), rightPrefix.2) at hrightRight
    rw [hrightChildEq']
    exact hrightRight
  change RelTriple
    ((simulateQ randomOracle
      (Concrete.treeNode parameter (unflattenSecret left.1.2)
        current.1.val current.node)).run leftPrefix.2)
    ((simulateQ randomOracle
      (Concrete.treeNode parameter (unflattenSecret right.1.1.2)
        current.1.val current.node)).run rightPrefix.2) _
  rw [hsucc]
  exact relTriple_treeNode_succ_run_with_treeCacheCorrespondence
    parameter selected leftEndpoints rightEndpoints
      (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
        levels current.node hlevel leftChild rightChild leftPrefix.2
          rightPrefix.2 hleftLeft' hleftRight' hrightLeft' hrightRight' hcache
            hreplay

set_option maxRecDepth 100000 in
theorem relTriple_fixedChainMaterial_merkleTreeValues_run_with_correspondence
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest)) :
    ∀ (indices base : List TreeValueIndex)
      (leftBase rightBase : List Digest × QueryCache HashSpec),
      (∀ current ∈ indices, ∃ hpositive : 0 < current.1.val,
        TreeValueIndex.ofSubtree (current.1.val - 1)
          (Concrete.childNode current.node false) (by omega)
          (childNode_subtreeValid (current.1.val - 1) current.node false
            (by simpa [Nat.sub_add_cancel hpositive] using current.subtreeValid)) ∈
            base ∧
        TreeValueIndex.ofSubtree (current.1.val - 1)
          (Concrete.childNode current.node true) (by omega)
          (childNode_subtreeValid (current.1.val - 1) current.node true
            (by simpa [Nat.sub_add_cancel hpositive] using current.subtreeValid)) ∈
            base) →
      indices.Pairwise TreeValueIndex.Precedes →
      leftBase ∈ support
        (treeValues parameter (unflattenSecret left.1.2) base left.2.2.2) →
      rightBase ∈ support
        (treeValues parameter (unflattenSecret right.1.1.2)
          base right.1.2.2.2) →
      leftBase.1 = rightBase.1 →
      TreeValuesFresh parameter indices leftBase.2 →
      TreeValuesFresh parameter indices rightBase.2 →
      ∀ (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest),
      CoupledTreeCacheCorrespondence parameter selected
        leftEndpoints rightEndpoints leftBase.2 rightBase.2 →
      LeafReplayOutputsCorrespond parameter
        (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
        leftBase.2 rightBase.2 →
      RelTriple
        (treeValues parameter (unflattenSecret left.1.2) indices leftBase.2)
        (treeValues parameter (unflattenSecret right.1.1.2) indices rightBase.2)
        (fun leftResult rightResult =>
          leftResult.1 = rightResult.1 ∧
            CoupledTreeCacheCorrespondence parameter selected
              leftEndpoints rightEndpoints leftResult.2 rightResult.2 ∧
            LeafReplayOutputsCorrespond parameter
              (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
              leftResult.2 rightResult.2 ∧
            (leftBase.1 ++ leftResult.1, leftResult.2) ∈ support
              (treeValues parameter (unflattenSecret left.1.2)
                (base ++ indices) left.2.2.2) ∧
            (rightBase.1 ++ rightResult.1, rightResult.2) ∈ support
              (treeValues parameter (unflattenSecret right.1.1.2)
                (base ++ indices) right.1.2.2.2)) := by
  intro indices
  induction indices with
  | nil =>
      intro base leftBase rightBase _hchildren _hordered hleftBase hrightBase
        _hbaseValues _hleftFresh _hrightFresh leftEndpoints rightEndpoints
          hcache hreplay
      simp only [treeValues_nil]
      apply relTriple_pure_pure
      refine ⟨rfl, hcache, hreplay, ?_, ?_⟩
      · simpa using hleftBase
      · simpa using hrightBase
  | cons current indices ih =>
      intro base leftBase rightBase hchildren hordered hleftBase hrightBase
        hbaseValues hleftFresh hrightFresh leftEndpoints rightEndpoints hcache
          hreplay
      obtain ⟨hpositive, hleftChild, hrightChild⟩ :=
        hchildren current (by simp)
      have htailChildren : ∀ target ∈ indices,
          ∃ hpositive : 0 < target.1.val,
            TreeValueIndex.ofSubtree (target.1.val - 1)
              (Concrete.childNode target.node false) (by omega)
              (childNode_subtreeValid (target.1.val - 1) target.node false
                (by simpa [Nat.sub_add_cancel hpositive] using
                  target.subtreeValid)) ∈ base ∧
            TreeValueIndex.ofSubtree (target.1.val - 1)
              (Concrete.childNode target.node true) (by omega)
              (childNode_subtreeValid (target.1.val - 1) target.node true
                (by simpa [Nat.sub_add_cancel hpositive] using
                  target.subtreeValid)) ∈ base := by
        intro target htarget
        exact hchildren target (by simp [htarget])
      have hcurrentBefore : ∀ target ∈ indices,
          current.Precedes target := (List.pairwise_cons.mp hordered).1
      have htailOrdered : indices.Pairwise TreeValueIndex.Precedes :=
        (List.pairwise_cons.mp hordered).2
      have hhead :=
        relTriple_fixedChainMaterial_merkleTreeValue_run_with_correspondence
          parameter selected left right base leftBase rightBase hleftBase
            hrightBase hbaseValues leftEndpoints rightEndpoints hcache hreplay
              current hpositive hleftChild hrightChild
      let LeftProperty := fun result : Digest × QueryCache HashSpec =>
        TreeValuesFresh parameter indices result.2 ∧
          (leftBase.1 ++ [result.1], result.2) ∈ support
            (treeValues parameter (unflattenSecret left.1.2)
              (base ++ [current]) left.2.2.2)
      let RightProperty := fun result : Digest × QueryCache HashSpec =>
        TreeValuesFresh parameter indices result.2 ∧
          (rightBase.1 ++ [result.1], result.2) ∈ support
            (treeValues parameter (unflattenSecret right.1.1.2)
              (base ++ [current]) right.1.2.2.2)
      have hleftProperty : ∀ result ∈ support
          ((simulateQ randomOracle
            (current.computation parameter (unflattenSecret left.1.2))).run
              leftBase.2), LeftProperty result := by
        intro result hresult
        exact ⟨treeValue_preserves_tail_fresh parameter
            (unflattenSecret left.1.2) current indices hcurrentBefore
            leftBase.2 hleftFresh result hresult,
          treeValues_append_support parameter (unflattenSecret left.1.2)
            base [current] left.2.2.2 leftBase ([result.1], result.2)
            hleftBase (treeValues_singleton_support parameter
              (unflattenSecret left.1.2) current leftBase.2 result hresult)⟩
      have hrightProperty : ∀ result ∈ support
          ((simulateQ randomOracle
            (current.computation parameter (unflattenSecret right.1.1.2))).run
              rightBase.2), RightProperty result := by
        intro result hresult
        exact ⟨treeValue_preserves_tail_fresh parameter
            (unflattenSecret right.1.1.2) current indices hcurrentBefore
            rightBase.2 hrightFresh result hresult,
          treeValues_append_support parameter (unflattenSecret right.1.1.2)
            base [current] right.1.2.2.2 rightBase ([result.1], result.2)
            hrightBase (treeValues_singleton_support parameter
              (unflattenSecret right.1.1.2) current rightBase.2 result hresult)⟩
      have hheadExtended := relTriple_strengthen_support
        (leftProperty := LeftProperty) (rightProperty := RightProperty)
        hhead hleftProperty hrightProperty
      simp only [treeValues_cons]
      apply relTriple_bind hheadExtended
      intro leftHeadResult rightHeadResult hheadResult
      obtain ⟨hheadRelation, hleftProperties, hrightProperties⟩ := hheadResult
      obtain ⟨leftHead, leftHeadCache⟩ := leftHeadResult
      obtain ⟨rightHead, rightHeadCache⟩ := rightHeadResult
      dsimp only at hheadRelation hleftProperties hrightProperties ⊢
      let nextLeftBase : List Digest × QueryCache HashSpec :=
        (leftBase.1 ++ [leftHead], leftHeadCache)
      let nextRightBase : List Digest × QueryCache HashSpec :=
        (rightBase.1 ++ [rightHead], rightHeadCache)
      have hnextValues : nextLeftBase.1 = nextRightBase.1 := by
        simp [nextLeftBase, nextRightBase, hbaseValues, hheadRelation.1]
      have hnextChildren : ∀ target ∈ indices,
          ∃ hpositive : 0 < target.1.val,
            TreeValueIndex.ofSubtree (target.1.val - 1)
              (Concrete.childNode target.node false) (by omega)
              (childNode_subtreeValid (target.1.val - 1) target.node false
                (by simpa [Nat.sub_add_cancel hpositive] using
                  target.subtreeValid)) ∈ base ++ [current] ∧
            TreeValueIndex.ofSubtree (target.1.val - 1)
              (Concrete.childNode target.node true) (by omega)
              (childNode_subtreeValid (target.1.val - 1) target.node true
                (by simpa [Nat.sub_add_cancel hpositive] using
                  target.subtreeValid)) ∈ base ++ [current] := by
        intro target htarget
        obtain ⟨hpos, hleft, hright⟩ := htailChildren target htarget
        exact ⟨hpos, List.mem_append_left [current] hleft,
          List.mem_append_left [current] hright⟩
      apply relTriple_bind
        (ih (base ++ [current]) nextLeftBase nextRightBase hnextChildren
          htailOrdered hleftProperties.2 hrightProperties.2 hnextValues
            hleftProperties.1 hrightProperties.1 leftEndpoints rightEndpoints
              hheadRelation.2.1 hheadRelation.2.2)
      intro leftTailResult rightTailResult htailResult
      apply relTriple_pure_pure
      refine ⟨congrArg₂ List.cons hheadRelation.1 htailResult.1,
        htailResult.2.1, htailResult.2.2.1, ?_, ?_⟩
      · simpa [nextLeftBase, List.append_assoc] using htailResult.2.2.2.1
      · simpa [nextRightBase, List.append_assoc] using htailResult.2.2.2.2

theorem relTriple_fixedChainMaterial_merkleHeight_run_with_correspondence
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (height : Fin (treeHeight + 1)) (hpositive : 0 < height.val)
    (leftBase rightBase : List Digest × QueryCache HashSpec)
    (hleftBase : leftBase ∈ support
      (treeValues parameter (unflattenSecret left.1.2)
        (treeValueIndicesBelow height.val) left.2.2.2))
    (hrightBase : rightBase ∈ support
      (treeValues parameter (unflattenSecret right.1.1.2)
        (treeValueIndicesBelow height.val) right.1.2.2.2))
    (hbaseValues : leftBase.1 = rightBase.1)
    (hleftFresh : TreeValuesFresh parameter
      (treeValueIndicesAtHeight height) leftBase.2)
    (hrightFresh : TreeValuesFresh parameter
      (treeValueIndicesAtHeight height) rightBase.2)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (hcache : CoupledTreeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftBase.2 rightBase.2)
    (hreplay : LeafReplayOutputsCorrespond parameter
      (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
      leftBase.2 rightBase.2) :
    RelTriple
      (treeValues parameter (unflattenSecret left.1.2)
        (treeValueIndicesAtHeight height) leftBase.2)
      (treeValues parameter (unflattenSecret right.1.1.2)
        (treeValueIndicesAtHeight height) rightBase.2)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          CoupledTreeCacheCorrespondence parameter selected
            leftEndpoints rightEndpoints leftResult.2 rightResult.2 ∧
          LeafReplayOutputsCorrespond parameter
            (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)
            leftResult.2 rightResult.2 ∧
          (leftBase.1 ++ leftResult.1, leftResult.2) ∈ support
            (treeValues parameter (unflattenSecret left.1.2)
              (treeValueIndicesBelow (height.val + 1)) left.2.2.2) ∧
          (rightBase.1 ++ rightResult.1, rightResult.2) ∈ support
            (treeValues parameter (unflattenSecret right.1.1.2)
              (treeValueIndicesBelow (height.val + 1)) right.1.2.2.2)) := by
  have hchildren : ∀ current ∈ treeValueIndicesAtHeight height,
      ∃ hcurrentPositive : 0 < current.1.val,
        TreeValueIndex.ofSubtree (current.1.val - 1)
          (Concrete.childNode current.node false) (by omega)
          (childNode_subtreeValid (current.1.val - 1) current.node false
            (by simpa [Nat.sub_add_cancel hcurrentPositive] using
              current.subtreeValid)) ∈ treeValueIndicesBelow height.val ∧
        TreeValueIndex.ofSubtree (current.1.val - 1)
          (Concrete.childNode current.node true) (by omega)
          (childNode_subtreeValid (current.1.val - 1) current.node true
            (by simpa [Nat.sub_add_cancel hcurrentPositive] using
              current.subtreeValid)) ∈ treeValueIndicesBelow height.val := by
    intro current hcurrent
    have hheight := (mem_treeValueIndicesAtHeight_iff height current).1 hcurrent
    have hvalue : current.1.val = height.val := congrArg Fin.val hheight
    have hcurrentPositive : 0 < current.1.val := by omega
    refine ⟨hcurrentPositive, ?_, ?_⟩
    · simpa only [hvalue] using
        (childTreeValueIndex_mem_below current hcurrentPositive false)
    · simpa only [hvalue] using
        (childTreeValueIndex_mem_below current hcurrentPositive true)
  have hordered : (treeValueIndicesAtHeight height).Pairwise
      TreeValueIndex.Precedes := by
    simp only [treeValueIndicesAtHeight, List.pairwise_ofFn]
    intro leftNode rightNode hlt
    exact Or.inr ⟨rfl, hlt⟩
  have hcoupling :=
    relTriple_fixedChainMaterial_merkleTreeValues_run_with_correspondence
      parameter selected left right (treeValueIndicesAtHeight height)
        (treeValueIndicesBelow height.val) leftBase rightBase hchildren hordered
          hleftBase hrightBase hbaseValues hleftFresh hrightFresh
            leftEndpoints rightEndpoints hcache hreplay
  apply relTriple_post_mono hcoupling
  intro leftResult rightResult hresult
  have hbelow := treeValueIndicesBelow_succ height.val height.isLt
  exact ⟨hresult.1, hresult.2.1, hresult.2.2.1,
    hbelow ▸ hresult.2.2.2.1, hbelow ▸ hresult.2.2.2.2⟩

def CoupledTreeValuesResult
    (parameter : PublicParameter) (selected : ChainIndex)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftResult rightResult : List Digest × QueryCache HashSpec) : Prop :=
  leftResult.1 = rightResult.1 ∧
    ∃ leftEndpoints rightEndpoints,
      CoupledTreeCacheCorrespondence parameter selected
        leftEndpoints rightEndpoints leftResult.2 rightResult.2 ∧
      LeafReplayOutputsCorrespond parameter leftSecret rightSecret
        leftResult.2 rightResult.2

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem relTriple_fixedChainMaterial_treeValuesBelow_one_with_correspondence
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hmaterial : CoupledFixedChainMaterialInvariant
      parameter selected left right) :
    RelTriple
      (treeValues parameter (unflattenSecret left.1.2)
        (treeValueIndicesBelow 1) left.2.2.2)
      (treeValues parameter (unflattenSecret right.1.1.2)
        (treeValueIndicesBelow 1) right.1.2.2.2)
      (CoupledTreeValuesResult parameter selected
        (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)) := by
  have hheight : treeValueIndicesBelow 1 = treeValueIndicesAtHeight 0 := by
    rw [treeValueIndicesBelow_succ 0 (by omega)]
    rw [treeValueIndicesBelow]
    exact List.nil_append _
  rw [hheight]
  apply relTriple_post_mono
    (relTriple_fixedChainMaterial_allLeafValues_run_with_correspondence
      parameter selected left right hmaterial)
  intro leftResult rightResult hresult
  exact hresult

set_option maxRecDepth 1000000 in
theorem relTriple_fixedChainMaterial_treeValuesBelow_succ_with_correspondence
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hmaterial : CoupledFixedChainMaterialInvariant
      parameter selected left right)
    (height : Nat) (hpositive : 1 ≤ height)
    (hcurrentBound : height < treeHeight + 1)
    (hprefix : RelTriple
      (treeValues parameter (unflattenSecret left.1.2)
        (treeValueIndicesBelow height) left.2.2.2)
      (treeValues parameter (unflattenSecret right.1.1.2)
        (treeValueIndicesBelow height) right.1.2.2.2)
      (CoupledTreeValuesResult parameter selected
        (unflattenSecret left.1.2) (unflattenSecret right.1.1.2))) :
    RelTriple
      (treeValues parameter (unflattenSecret left.1.2)
        (treeValueIndicesBelow (height + 1)) left.2.2.2)
      (treeValues parameter (unflattenSecret right.1.1.2)
        (treeValueIndicesBelow (height + 1)) right.1.2.2.2)
      (CoupledTreeValuesResult parameter selected
        (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)) := by
  let currentHeight : Fin (treeHeight + 1) := ⟨height, hcurrentBound⟩
  have hdecompose := treeValueIndicesBelow_succ height hcurrentBound
  rw [hdecompose, treeValues_append, treeValues_append]
  apply relTriple_bind (relTriple_with_support hprefix)
  intro leftBase rightBase hbase
  obtain ⟨hbaseRelation, hleftBase, hrightBase⟩ := hbase
  unfold CoupledTreeValuesResult at hbaseRelation
  obtain ⟨hbaseValues, leftEndpoints, rightEndpoints, hbaseCache,
    hbaseReplay⟩ :=
    hbaseRelation
  have hleftFresh := fixedChainMaterial_treeValuesBelow_fresh_at_height
    parameter selected left hmaterial.leftLeafFresh hmaterial.leftMerkleFresh
      currentHeight leftBase hleftBase
  have hrightFresh := fixedChainMaterial_treeValuesBelow_fresh_at_height
    parameter selected right.1 hmaterial.rightLeafFresh
      hmaterial.rightMerkleFresh currentHeight rightBase hrightBase
  have hheightCoupling :=
    relTriple_fixedChainMaterial_merkleHeight_run_with_correspondence
      parameter selected left right currentHeight (by
        dsimp [currentHeight]
        exact hpositive)
      leftBase rightBase hleftBase hrightBase hbaseValues hleftFresh
        hrightFresh leftEndpoints rightEndpoints hbaseCache hbaseReplay
  apply relTriple_bind hheightCoupling
  intro leftCurrent rightCurrent hcurrent
  obtain ⟨leftValues, leftCache⟩ := leftBase
  obtain ⟨rightValues, rightCache⟩ := rightBase
  obtain ⟨leftNewValues, leftNewCache⟩ := leftCurrent
  obtain ⟨rightNewValues, rightNewCache⟩ := rightCurrent
  dsimp only at hbaseValues hcurrent ⊢
  apply relTriple_pure_pure
  unfold CoupledTreeValuesResult
  exact ⟨congrArg₂ List.append hbaseValues hcurrent.1,
    leftEndpoints, rightEndpoints, hcurrent.2.1, hcurrent.2.2.1⟩

theorem relTriple_fixedChainMaterial_treeValuesBelow_run_with_correspondence
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hmaterial : CoupledFixedChainMaterialInvariant
      parameter selected left right) :
    ∀ (height : Nat), 1 ≤ height → height ≤ treeHeight + 1 →
      RelTriple
        (treeValues parameter (unflattenSecret left.1.2)
          (treeValueIndicesBelow height) left.2.2.2)
        (treeValues parameter (unflattenSecret right.1.1.2)
          (treeValueIndicesBelow height) right.1.2.2.2)
        (CoupledTreeValuesResult parameter selected
          (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)) := by
  intro height
  induction height with
  | zero => intro hpositive _hbound; omega
  | succ height ih =>
      intro _hpositive hbound
      by_cases hzero : height = 0
      · subst height
        exact relTriple_fixedChainMaterial_treeValuesBelow_one_with_correspondence
          parameter selected left right hmaterial
      · apply relTriple_fixedChainMaterial_treeValuesBelow_succ_with_correspondence
          parameter selected left right hmaterial height (by omega) (by omega)
        exact ih (by omega) (by omega)

theorem relTriple_fixedChainMaterial_allTreeValues_run_with_correspondence
    (parameter : PublicParameter) (selected : ChainIndex)
    (left : FixedChainMaterial)
    (right : FixedChainMaterial × (ChainValueIndex → Digest))
    (hmaterial : CoupledFixedChainMaterialInvariant
      parameter selected left right) :
    RelTriple
      (treeValues parameter (unflattenSecret left.1.2)
        allTreeValueIndices left.2.2.2)
      (treeValues parameter (unflattenSecret right.1.1.2)
        allTreeValueIndices right.1.2.2.2)
      (CoupledTreeValuesResult parameter selected
        (unflattenSecret left.1.2) (unflattenSecret right.1.1.2)) := by
  rw [← treeValueIndicesBelow_all]
  exact relTriple_fixedChainMaterial_treeValuesBelow_run_with_correspondence
    parameter selected left right hmaterial (treeHeight + 1) (by omega) le_rfl

def chainEndpointDigit : Digit :=
  ⟨chainLength - 1, by decide⟩

noncomputable def leafInputProbe?
    (parameter : PublicParameter) (selected : ChainIndex)
    (input : HashInput) : Option (ChainValueIndex × Digest) :=
  if h : ∃ data : Epoch × (ChainIndex → Digest),
      input = Concrete.CacheView.leafInput parameter data.1 data.2 then
    let data := h.choose
    some ((data.1, chainEndpointDigit), data.2 selected)
  else
    none

@[simp]
theorem leafInputProbe?_leafInput
    (parameter : PublicParameter) (selected : ChainIndex)
    (epoch : Epoch) (endpoints : ChainIndex → Digest) :
    leafInputProbe? parameter selected
      (Concrete.CacheView.leafInput parameter epoch endpoints) =
        some ((epoch, chainEndpointDigit), endpoints selected) := by
  unfold leafInputProbe?
  split
  · rename_i h
    let chosen := h.choose
    have hchosen := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq parameter hchosen
    simp only [HashDomain.leaf.injEq] at hdomain
    have hendpoints : chosen.2 = endpoints := by
      rw [← hdomain] at hchosen
      exact (Concrete.leafPayload_injective
        (payload_eq_of_tweakableHashInput_eq parameter (.leaf epoch)
          hchosen)).symm
    change some ((chosen.1, chainEndpointDigit), chosen.2 selected) = _
    rw [← hdomain, hendpoints]
  · rename_i h
    exact (h ⟨(epoch, endpoints), rfl⟩).elim

@[simp]
theorem leafInputProbe?_chainInput
    (parameter : PublicParameter) (selected chain : ChainIndex)
    (epoch : Epoch) (step : ChainStep) (value : Digest) :
    leafInputProbe? parameter selected
      (Concrete.CacheView.chainInput parameter epoch chain step value) = none := by
  unfold leafInputProbe?
  split
  · rename_i h
    obtain ⟨data, hdata⟩ := h
    have hdomain := domain_eq_of_tweakableHashInput_eq parameter hdata
    simp at hdomain
  · rfl

theorem programmedKeygen_selectedEndpoint_eq_table
    (selected : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hview : view ∈ support (programmedWarmedFixedChainKeygen selected))
    (epoch : Epoch) :
    Concrete.CacheReplay.oneTimePublicKey view.cache
        view.secretKey.parameter view.secretKey.chainStart epoch selected =
      view.table (epoch, chainEndpointDigit) := by
  calc
    _ = keygenChainValueTable view.cache view.secretKey selected
        (epoch, chainEndpointDigit) := rfl
    _ = view.table (epoch, chainEndpointDigit) :=
      congrFun (programmedWarmedFixedChainKeygen_support_table
        selected view hview) (epoch, chainEndpointDigit)

theorem programmedKeygen_leaf_cache_eq_none_of_selectedEndpoint_ne
    (selected : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hview : view ∈ support (programmedWarmedFixedChainKeygen selected))
    (epoch : Epoch) (endpoints : ChainIndex → Digest)
    (hne : endpoints selected ≠ view.table (epoch, chainEndpointDigit)) :
    view.cache (Concrete.CacheView.leafInput view.secretKey.parameter
      epoch endpoints) = none := by
  apply Concrete.keygen_cache_leafInput_eq_none_of_ne view.keyResult
    (programmedWarmedFixedChainKeygen_support_keyResult selected view hview)
      epoch endpoints
  intro heq
  apply hne
  rw [heq]
  exact programmedKeygen_selectedEndpoint_eq_table selected view hview epoch

end XmssSecurity
