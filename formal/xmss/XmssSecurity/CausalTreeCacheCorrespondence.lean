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
      leftEndpoints rightEndpoints leftCache rightCache) :
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
            leftEndpoints rightEndpoints leftResult.2 rightResult.2) := by
  simp only [Concrete.treeNode_succ_eq, simulateQ_bind, StateT.run_bind,
    hleftLeft, hleftRight, hrightLeft, hrightRight, pure_bind,
    hlevel, ↓reduceDIte]
  exact relTriple_nodeHash_run_of_treeCacheCorrespondence parameter selected
    leftEndpoints rightEndpoints leftCache rightCache hcache
      ⟨levels, hlevel⟩ node leftChild rightChild

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
              leftResult.2 rightResult.2) := by
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
  apply relTriple_post_mono
    (relTriple_leafHash_run_of_treeCacheCorrespondence parameter selected
      leftEndpoints rightEndpoints leftOneTimeResult.2 rightOneTimeResult.2
        hcorrespond epoch leftOneTimeResult.1 rightOneTimeResult.1
          hleftNone hrightNone)
  intro leftResult rightResult hresult
  exact ⟨hresult.1, leftOneTimeResult.1, rightOneTimeResult.1, hresult.2⟩

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
                  finalLeft finalRight leftResult.2 rightResult.2) := by
  intro indices
  induction indices with
  | nil =>
      intro _hzero _hordered leftEndpoints rightEndpoints leftCache rightCache
        _hleftFresh _hrightFresh hcache _hleftLe _hrightLe
      simp only [treeValues_nil]
      exact relTriple_pure_pure ⟨rfl, leftEndpoints, rightEndpoints, hcache⟩
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
                  leftResult.2 rightResult.2) := by
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
      obtain ⟨hheadValue, nextLeft, nextRight, hnextCache⟩ := hheadRelation
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
        (ih htailZero htailOrdered
          (Function.update leftEndpoints current.node nextLeft)
          (Function.update rightEndpoints current.node nextRight)
          leftHeadResult.2 rightHeadResult.2 hleftTailFresh hrightTailFresh
            hnextCache hleftNextLe hrightNextLe)
      intro leftTailResult rightTailResult htailResult
      apply relTriple_pure_pure
      exact ⟨congrArg₂ List.cons hheadValue htailResult.1,
        htailResult.2⟩

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
              finalLeft finalRight leftResult.2 rightResult.2) := by
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
  exact relTriple_fixedChainMaterial_leafTreeValues_run_with_correspondence
    parameter selected left right hmaterial (treeValueIndicesAtHeight 0)
      hzero hordered initialEndpoints initialEndpoints left.2.2.2 right.1.2.2.2
        hleftFresh hrightFresh
          (coupledFixedChainMaterialInvariant_initialTreeCacheCorrespondence
            parameter selected left right hmaterial initialEndpoints
              initialEndpoints) le_rfl le_rfl

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
