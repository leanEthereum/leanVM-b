import XmssSecurity.Proof.CausalTreeCoupling
import XmssSecurity.Proof.TreeValueTraversal
import XmssSecurity.Proof.ChainOraclePresampling

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def TreeCacheStable
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (cache : QueryCache HashSpec) : Prop :=
  ∀ (levels : Nat) (node : MerkleNode),
    levels ≤ treeHeight → TreeSubtreeValid levels node →
    ∀ (largerCache : QueryCache HashSpec), cache ≤ largerCache →
    (simulateQ randomOracle
      (Concrete.treeNode parameter secret levels node :
        OracleComp HashSpec Digest)).run largerCache =
      pure (Concrete.CacheReplay.treeNode cache parameter secret levels node,
        largerCache)

theorem treeCacheStable_of_treeValues_support
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (initialCache : QueryCache HashSpec)
    (tree : List Digest × QueryCache HashSpec)
    (htree : tree ∈ support
      (treeValues parameter secret allTreeValueIndices initialCache)) :
    TreeCacheStable parameter secret tree.2 := by
  intro levels node hlevels hvalid largerCache hle
  let index := TreeValueIndex.ofSubtree levels node hlevels hvalid
  have hrun := treeValues_rerun_index_eq_pure parameter secret
    allTreeValueIndices initialCache tree htree index
      (mem_allTreeValueIndices index)
  have hmem :
      (Concrete.CacheReplay.treeNode tree.2 parameter secret levels node,
        tree.2) ∈ support
          ((simulateQ randomOracle
            (Concrete.treeNode parameter secret levels node :
              OracleComp HashSpec Digest)).run tree.2) := by
    change (Concrete.CacheReplay.treeNode tree.2 parameter secret
        index.1.val index.node, tree.2) ∈ support
      ((simulateQ randomOracle (index.computation parameter secret)).run tree.2)
    rw [hrun]
    simp
  exact Concrete.CacheReplay.randomOracle_rerun_largerCache_eq_pure_of_mem_support
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest)
    tree.2 tree.2 largerCache
      (Concrete.CacheReplay.treeNode tree.2 parameter secret levels node)
      hmem hle

theorem TreeCacheStable.treeNode_eq
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (cache : QueryCache HashSpec)
    (hstable : TreeCacheStable parameter secret cache)
    (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node)
    (largerCache : QueryCache HashSpec) (hle : cache ≤ largerCache) :
    Concrete.CacheReplay.treeNode cache parameter secret levels node =
      Concrete.CacheReplay.treeNode largerCache parameter secret levels node := by
  have hrun := hstable levels node hlevels hvalid largerCache hle
  have hmem :
      (Concrete.CacheReplay.treeNode cache parameter secret levels node,
        largerCache) ∈ support
          ((simulateQ randomOracle
            (Concrete.treeNode parameter secret levels node :
              OracleComp HashSpec Digest)).run largerCache) := by
    rw [hrun]
    simp
  have hreplay := Concrete.CacheReplay.eval_answerFn_finalCache_eq_of_mem_support
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest)
    largerCache largerCache
      (Concrete.CacheReplay.treeNode cache parameter secret levels node) hmem
  rw [Concrete.CacheReplay.eval_treeNode] at hreplay
  exact hreplay.symm

theorem TreeCacheStable.authenticationPath_eq
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (hstable : TreeCacheStable secretKey.parameter secretKey.chainStart cache)
    (largerCache : QueryCache HashSpec) (hle : cache ≤ largerCache)
    (epoch : Epoch) :
    Concrete.CacheReplay.authenticationPath cache secretKey epoch =
      Concrete.CacheReplay.authenticationPath largerCache secretKey epoch := by
  funext level
  exact TreeCacheStable.treeNode_eq secretKey.parameter secretKey.chainStart
    cache hstable level.val (Concrete.authenticationPathNode epoch level)
      (by omega) (authenticationPathNode_subtreeValid epoch level)
        largerCache hle

theorem coupledWarmedKeygenExperiment_support_treeCacheStable
    (parameter : PublicParameter) (chain : ChainIndex)
    (view : CoupledWarmedKeygenView)
    (hview : view ∈ support
      (coupledWarmedKeygenExperiment parameter chain)) :
    TreeCacheStable parameter view.secret view.cache := by
  unfold coupledWarmedKeygenExperiment at hview
  rw [mem_support_bind_iff] at hview
  obtain ⟨material, _hmaterial, htreeBind⟩ := hview
  rw [mem_support_bind_iff] at htreeBind
  obtain ⟨tree, htree, hpure⟩ := htreeBind
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst view
  exact treeCacheStable_of_treeValues_support parameter
    (unflattenSecret material.1.2) material.2.2 tree htree

theorem coupledWarmedFixedChainKeygen_support_treeCacheStable
    (chain : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hview : view ∈ support (coupledWarmedFixedChainKeygen chain)) :
    TreeCacheStable view.secretKey.parameter view.secretKey.chainStart
      view.cache := by
  unfold coupledWarmedFixedChainKeygen at hview
  rw [mem_support_bind_iff] at hview
  obtain ⟨parameter, _hparameter, hviewBind⟩ := hview
  rw [mem_support_bind_iff] at hviewBind
  obtain ⟨coupledView, hcoupledView, hpure⟩ := hviewBind
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst view
  exact coupledWarmedKeygenExperiment_support_treeCacheStable
    parameter chain coupledView hcoupledView

theorem programmedWarmedFixedChainKeygen_support_treeCacheStable
    (chain : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hview : view ∈ support (programmedWarmedFixedChainKeygen chain)) :
    TreeCacheStable view.secretKey.parameter view.secretKey.chainStart
      view.cache := by
  apply coupledWarmedFixedChainKeygen_support_treeCacheStable chain view
  exact (mem_support_iff_of_evalDist_eq
    (evalDist_coupledWarmedFixedChainKeygen_eq_programmed chain) view).mpr hview

theorem actualFixedChainKeygen_support_treeCacheStable
    (chain : ChainIndex) (view : ProgrammedFixedChainKeygenView)
    (hview : view ∈ support (actualFixedChainKeygen chain)) :
    TreeCacheStable view.secretKey.parameter view.secretKey.chainStart
      view.cache := by
  apply programmedWarmedFixedChainKeygen_support_treeCacheStable chain view
  exact (mem_support_iff_of_evalDist_eq
    (evalDist_actualFixedChainKeygen_eq_programmedWarmed chain) view).mp hview

end XmssSecurity.CappedChain
