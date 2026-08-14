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
