import XmssSecurity.CappedGlobalChainKeygenCoupling
import XmssSecurity.CausalTreeTableIndependence

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem Concrete.fixedSeedChainTrajectoriesFromCache_avoids_leaf
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (targetEpoch : Epoch)
    (input : HashInput)
    (hinput : AtHashAddress parameter (.leaf targetEpoch) input) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec)
      (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec),
      cache input = none →
      result ∈ support
        (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
          steps cache epochs) →
      result.2 input = none := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache result hcache hresult
      simp only [Concrete.fixedSeedChainTrajectoriesFromCache_nil,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hcache
  | cons epoch epochs ih =>
      intro cache result hcache hresult
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      apply ih first.2 rest
      · apply Concrete.CacheReplay.cache_none_of_zero_query_bound
          (Concrete.chainTrajectory parameter epoch chain 0 steps
            (secret epoch chain)) input cache first.2 first.1
        · apply OracleComp.IsQueryBoundP.of_imp
            (p' := AtHashAddress parameter (.leaf targetEpoch))
          · intro candidate heq
            subst candidate
            exact hinput
          · apply Concrete.chainTrajectory_queryBound_zero_of_avoids
            intro offset hoffset hvalid heq
            simp at heq
        · exact hcache
        · exact hfirst
      · exact hrest

theorem Concrete.fixedSeedChainTrajectoriesFromCache_avoids_merkle
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (level : MerkleLevel)
    (node : MerkleNode) (input : HashInput)
    (hinput : AtHashAddress parameter (.merkle level node) input) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec)
      (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec),
      cache input = none →
      result ∈ support
        (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
          steps cache epochs) →
      result.2 input = none := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache result hcache hresult
      simp only [Concrete.fixedSeedChainTrajectoriesFromCache_nil,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hcache
  | cons epoch epochs ih =>
      intro cache result hcache hresult
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      apply ih first.2 rest
      · apply Concrete.CacheReplay.cache_none_of_zero_query_bound
          (Concrete.chainTrajectory parameter epoch chain 0 steps
            (secret epoch chain)) input cache first.2 first.1
        · apply OracleComp.IsQueryBoundP.of_imp
            (p' := AtHashAddress parameter (.merkle level node))
          · intro candidate heq
            subst candidate
            exact hinput
          · apply Concrete.chainTrajectory_queryBound_zero_of_avoids
            intro offset hoffset hvalid heq
            simp at heq
        · exact hcache
        · exact hfirst
      · exact hrest

theorem Concrete.allChainTrajectoriesFromCache_avoids_leaf
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (targetEpoch : Epoch) (input : HashInput)
    (hinput : AtHashAddress parameter (.leaf targetEpoch) input) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec)
      (result : AllChainTrajectories × QueryCache HashSpec),
      cache input = none →
      result ∈ support
        (Concrete.allChainTrajectoriesFromCache parameter secret cache chains) →
      result.2 input = none := by
  intro chains
  induction chains with
  | nil =>
      intro cache result hcache hresult
      simp only [Concrete.allChainTrajectoriesFromCache_nil, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact hcache
  | cons chain chains ih =>
      intro cache result hcache hresult
      rw [Concrete.allChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      apply ih first.2 rest
      · exact Concrete.fixedSeedChainTrajectoriesFromCache_avoids_leaf
          parameter secret chain (chainLength - 1) targetEpoch input hinput
            allEpochs cache first hcache hfirst
      · exact hrest

theorem Concrete.allChainTrajectoriesFromCache_avoids_merkle
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (level : MerkleLevel) (node : MerkleNode) (input : HashInput)
    (hinput : AtHashAddress parameter (.merkle level node) input) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec)
      (result : AllChainTrajectories × QueryCache HashSpec),
      cache input = none →
      result ∈ support
        (Concrete.allChainTrajectoriesFromCache parameter secret cache chains) →
      result.2 input = none := by
  intro chains
  induction chains with
  | nil =>
      intro cache result hcache hresult
      simp only [Concrete.allChainTrajectoriesFromCache_nil, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact hcache
  | cons chain chains ih =>
      intro cache result hcache hresult
      rw [Concrete.allChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      apply ih first.2 rest
      · exact Concrete.fixedSeedChainTrajectoriesFromCache_avoids_merkle
          parameter secret chain (chainLength - 1) level node input hinput
            allEpochs cache first hcache hfirst
      · exact hrest

theorem programmedAllChainTrajectories_treeValuesFresh
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (result : AllChainTrajectories × QueryCache HashSpec)
    (hresult : result ∈ support
      (programmedAllChainTrajectoriesFromCache parameter secret ∅
        allChains)) :
    TreeValuesFresh parameter allTreeValueIndices result.2 := by
  have hactual : result ∈ support
      (Concrete.allChainTrajectoriesFromCache parameter secret ∅
        allChains) := by
    apply (mem_support_iff_of_evalDist_eq
      (evalDist_allChainTrajectories_eq_programmed parameter secret allChains ∅
        allChains_nodup (by simp [AllChainAddressesAbsent])) result).mpr
    exact hresult
  intro index _hindex input hinput
  by_cases hzero : index.1.val = 0
  · unfold TreeValueIndex.domain at hinput
    rw [dif_pos hzero] at hinput
    exact Concrete.allChainTrajectoriesFromCache_avoids_leaf parameter secret
      index.node input hinput allChains ∅ result (by simp) hactual
  · unfold TreeValueIndex.domain at hinput
    rw [dif_neg hzero] at hinput
    exact Concrete.allChainTrajectoriesFromCache_avoids_merkle parameter secret
      ⟨index.1.val - 1, by omega⟩ index.node input hinput allChains ∅
        result (by simp) hactual

theorem relTriple_programmedAllChainTreeValues_same_values
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (left right : AllChainTrajectories × QueryCache HashSpec)
    (hleft : left ∈ support
      (programmedAllChainTrajectoriesFromCache parameter leftSecret ∅
        allChains))
    (hright : right ∈ support
      (programmedAllChainTrajectoriesFromCache parameter rightSecret ∅
        allChains)) :
    RelTriple
      (treeValues parameter leftSecret allTreeValueIndices left.2)
      (treeValues parameter rightSecret allTreeValueIndices right.2)
      (fun leftTree rightTree =>
        leftTree.1 = rightTree.1 ∧
          TreeValuesReplay parameter leftSecret leftTree.2
            allTreeValueIndices leftTree.1 ∧
          TreeValuesReplay parameter rightSecret rightTree.2
            allTreeValueIndices rightTree.1) := by
  exact relTriple_treeValues_same_values parameter parameter
    leftSecret rightSecret allTreeValueIndices left.2 right.2
      allTreeValueIndices_pairwise
      (programmedAllChainTrajectories_treeValuesFresh parameter leftSecret
        left hleft)
      (programmedAllChainTrajectories_treeValuesFresh parameter rightSecret
        right hright)

set_option maxRecDepth 1000000 in
theorem relTriple_programmedAllChainTreeValues_same_root_and_paths
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (left right : AllChainTrajectories × QueryCache HashSpec)
    (hleft : left ∈ support
      (programmedAllChainTrajectoriesFromCache parameter leftSecret ∅
        allChains))
    (hright : right ∈ support
      (programmedAllChainTrajectoriesFromCache parameter rightSecret ∅
        allChains)) :
    RelTriple
      (treeValues parameter leftSecret allTreeValueIndices left.2)
      (treeValues parameter rightSecret allTreeValueIndices right.2)
      (fun leftTree rightTree =>
        leftTree.1 = rightTree.1 ∧
          TreeValuesReplay parameter leftSecret leftTree.2
            allTreeValueIndices leftTree.1 ∧
          TreeValuesReplay parameter rightSecret rightTree.2
            allTreeValueIndices rightTree.1 ∧
          Concrete.CacheReplay.treeNode leftTree.2 parameter leftSecret
              treeHeight Concrete.rootNode =
            Concrete.CacheReplay.treeNode rightTree.2 parameter rightSecret
              treeHeight Concrete.rootNode ∧
          ∀ epoch,
            Concrete.CacheReplay.authenticationPath leftTree.2
                ⟨parameter, leftSecret⟩ epoch =
              Concrete.CacheReplay.authenticationPath rightTree.2
                ⟨parameter, rightSecret⟩ epoch) := by
  apply relTriple_post_mono
    (relTriple_programmedAllChainTreeValues_same_values parameter
      leftSecret rightSecret left right hleft hright)
  intro leftTree rightTree hrelation
  obtain ⟨hvalues, hleftReplay, hrightReplay⟩ := hrelation
  refine ⟨hvalues, hleftReplay, hrightReplay, ?_, ?_⟩
  · exact globalTreeValuesReplay_eq_root parameter leftSecret rightSecret
      leftTree.2 rightTree.2 leftTree.1 hleftReplay
        (hvalues ▸ hrightReplay)
  · intro epoch
    exact globalTreeValuesReplay_eq_authenticationPath parameter
      leftSecret rightSecret leftTree.2 rightTree.2 leftTree.1 hleftReplay
        (hvalues ▸ hrightReplay) epoch

end XmssSecurity.CappedChain
