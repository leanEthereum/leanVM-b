import XmssSecurity.Proof.CappedGlobalKeygen
import XmssSecurity.Proof.CappedChain.CausalSigningKeygenCoupling
import XmssSecurity.Proof.TreeCacheVocabulary
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem Concrete.fixedSeedChainTrajectoriesFromCache_component_support_global
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec)
      (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec)
      (target : Epoch),
      target ∈ epochs →
      result ∈ support
        (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
          steps cache epochs) →
      ∃ before after trajectory,
        (trajectory, after) ∈ support
          ((simulateQ randomOracle
            (Concrete.chainTrajectory parameter target chain 0 steps
              (secret target chain))).run before) ∧
        after ≤ result.2 := by
  intro epochs
  induction epochs with
  | nil =>
      intro _cache _result target htarget _hresult
      simp at htarget
  | cons epoch epochs ih =>
      intro cache result target htarget hresult
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      rw [List.mem_cons] at htarget
      rcases htarget with rfl | htarget
      · have hrestInfo :=
          Concrete.fixedSeedChainTrajectoriesFromCache_support_info parameter
            secret chain steps epochs first.2 rest hrest
        exact ⟨cache, first.2, first.1, hfirst, hrestInfo.1⟩
      · exact ih first.2 rest target htarget hrest

theorem Concrete.allChainTrajectoriesFromCache_chain_component_support
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec)
      (result : AllChainTrajectories × QueryCache HashSpec)
      (selected : ChainIndex),
      chains.Nodup →
      selected ∈ chains →
      result ∈ support
        (Concrete.allChainTrajectoriesFromCache parameter secret cache chains) →
      ∃ before after trajectories,
        (trajectories, after) ∈ support
          (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret
            selected (chainLength - 1) before allEpochs) ∧
        after ≤ result.2 := by
  intro chains
  induction chains with
  | nil =>
      intro _cache _result selected _hnodup hselected _hresult
      simp at hselected
  | cons chain chains ih =>
      intro cache result selected hnodup hselected hresult
      obtain ⟨_hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [Concrete.allChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      rw [List.mem_cons] at hselected
      rcases hselected with rfl | hselected
      · have hrestInfo :=
          Concrete.allChainTrajectoriesFromCache_support_info parameter secret
            chains first.2 rest htailNodup hrest
        exact ⟨cache, first.2, first.1, hfirst, hrestInfo.1⟩
      · exact ih first.2 rest selected htailNodup hselected hrest

theorem Concrete.allChainTrajectoriesFromCache_chainWalk_run_eq_pure
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (result : AllChainTrajectories × QueryCache HashSpec)
    (hresult : result ∈ support
      (Concrete.allChainTrajectoriesFromCache parameter secret ∅ allChains))
    (largerCache : QueryCache HashSpec) (hle : result.2 ≤ largerCache)
    (epoch : Epoch) (chain : ChainIndex) :
    (simulateQ randomOracle
      (Concrete.chainWalk parameter epoch chain 0 (chainLength - 1)
        (secret epoch chain))).run largerCache =
      pure (Concrete.CacheReplay.oneTimePublicKey largerCache parameter secret
        epoch chain, largerCache) := by
  obtain ⟨before, after, trajectories, htrajectories, hafter⟩ :=
    Concrete.allChainTrajectoriesFromCache_chain_component_support
      parameter secret allChains ∅ result chain allChains_nodup
        (mem_allChains chain) hresult
  obtain ⟨walkBefore, walkAfter, trajectory, htrajectory, hwalkAfter⟩ :=
    Concrete.fixedSeedChainTrajectoriesFromCache_component_support_global
      parameter secret chain (chainLength - 1) allEpochs before
        (trajectories, after) epoch (mem_allEpochs epoch) htrajectories
  have hmapped : (trajectory.back, walkAfter) ∈ support
      ((fun value : FullChainTrajectory × QueryCache HashSpec =>
        (value.1.back, value.2)) <$>
          (simulateQ randomOracle
            (Concrete.chainTrajectory parameter epoch chain 0
              (chainLength - 1) (secret epoch chain))).run walkBefore) := by
    rw [support_map]
    exact ⟨(trajectory, walkAfter), htrajectory, rfl⟩
  have hwalk : (trajectory.back, walkAfter) ∈ support
      ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch chain 0 (chainLength - 1)
          (secret epoch chain) : OracleComp HashSpec Digest)).run walkBefore) :=
    (mem_support_iff_of_evalDist_eq
      (evalDist_chainTrajectory_run_cache_eq_chainWalk_run_cache
        parameter epoch chain 0 (chainLength - 1) (secret epoch chain)
          walkBefore) (trajectory.back, walkAfter)).mp hmapped
  have hwalkLe : walkAfter ≤ largerCache :=
    hwalkAfter.trans (hafter.trans hle)
  have hreplay :=
    Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
      (Concrete.chainWalk parameter epoch chain 0 (chainLength - 1)
        (secret epoch chain) : OracleComp HashSpec Digest)
      walkBefore walkAfter largerCache trajectory.back hwalk hwalkLe
  rw [Concrete.CacheReplay.eval_chainWalk] at hreplay
  rw [Concrete.CacheReplay.randomOracle_rerun_largerCache_eq_pure_of_mem_support
    (Concrete.chainWalk parameter epoch chain 0 (chainLength - 1)
      (secret epoch chain) : OracleComp HashSpec Digest)
    walkBefore walkAfter largerCache trajectory.back hwalk hwalkLe]
  rw [← hreplay]
  rfl

theorem Concrete.allChainTrajectoriesFromCache_oneTimePublicKey_run_eq_pure
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (result : AllChainTrajectories × QueryCache HashSpec)
    (hresult : result ∈ support
      (Concrete.allChainTrajectoriesFromCache parameter secret ∅ allChains))
    (largerCache : QueryCache HashSpec) (hle : result.2 ≤ largerCache)
    (epoch : Epoch) :
    (simulateQ randomOracle
      (Concrete.oneTimePublicKey parameter secret epoch)).run largerCache =
      pure (Concrete.CacheReplay.oneTimePublicKey largerCache parameter secret
        epoch, largerCache) := by
  have hrun : ∀ chain,
      (simulateQ randomOracle
        (Concrete.chainWalk parameter epoch chain 0 (chainLength - 1)
          (secret epoch chain))).run largerCache =
        pure (Concrete.CacheReplay.oneTimePublicKey largerCache parameter secret
          epoch chain, largerCache) := by
    intro chain
    exact Concrete.allChainTrajectoriesFromCache_chainWalk_run_eq_pure
      parameter secret result hresult largerCache hle epoch chain
  simpa [Concrete.oneTimePublicKey] using
    (simulate_sequenceFin_run_eq_pure
      (fun chain => Concrete.chainWalk parameter epoch chain 0
        (chainLength - 1) (secret epoch chain)) largerCache
      (Concrete.CacheReplay.oneTimePublicKey largerCache parameter secret epoch)
      hrun)

structure GlobalTreeCacheCorrespondence
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec) : Prop where
  merkle : HashCachesAgreeOn (MerkleHashInput parameter) leftCache rightCache
  leaves : LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
    leftCache rightCache

def TreeCacheResult
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    {Result : Type}
    (leftResult rightResult : Result × QueryCache HashSpec) : Prop :=
  leftResult.1 = rightResult.1 ∧
    GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
      leftResult.2 rightResult.2 ∧
    ReplayEndpointsMatch parameter leftSecret leftEndpoints leftResult.2 ∧
    ReplayEndpointsMatch parameter rightSecret rightEndpoints rightResult.2

def GlobalTreeValuesResult
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftResult rightResult : List Digest × QueryCache HashSpec) : Prop :=
  leftResult.1 = rightResult.1 ∧
    ∃ leftEndpoints rightEndpoints,
      GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
        leftResult.2 rightResult.2 ∧
      ReplayEndpointsMatch parameter leftSecret leftEndpoints leftResult.2 ∧
      ReplayEndpointsMatch parameter rightSecret rightEndpoints rightResult.2

theorem GlobalTreeCacheCorrespondence.replayLeaves
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (htree : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
    (hleftReplay : ReplayEndpointsMatch parameter leftSecret leftEndpoints
      leftCache)
    (hrightReplay : ReplayEndpointsMatch parameter rightSecret rightEndpoints
      rightCache) :
    LeafReplayOutputsCorrespond parameter leftSecret rightSecret leftCache
      rightCache := by
  intro epoch
  calc
    hashCacheLookup leftCache (Concrete.CacheView.leafInput parameter epoch
        (Concrete.CacheReplay.oneTimePublicKey leftCache parameter leftSecret
          epoch)) =
        hashCacheLookup leftCache (Concrete.CacheView.leafInput parameter epoch
          (leftEndpoints epoch)) := by rw [hleftReplay epoch]
    _ = hashCacheLookup rightCache (Concrete.CacheView.leafInput parameter epoch
        (rightEndpoints epoch)) := htree.leaves epoch
    _ = hashCacheLookup rightCache (Concrete.CacheView.leafInput parameter epoch
        (Concrete.CacheReplay.oneTimePublicKey rightCache parameter rightSecret
          epoch)) := by rw [hrightReplay epoch]

theorem merkleHashInput_ne_leafInput
    (parameter : PublicParameter) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) (input : HashInput)
    (hinput : MerkleHashInput parameter input) :
    input ≠ Concrete.CacheView.leafInput parameter epoch endpoints := by
  obtain ⟨level, node, hmerkle⟩ := hinput
  intro heq
  have hleaf : AtHashAddress parameter (.leaf epoch) input := by
    rw [heq]
    simp [Concrete.CacheView.leafInput]
  have hdomain := atHashAddress_unique parameter (.merkle level node)
    (.leaf epoch) input hmerkle hleaf
  simp at hdomain

theorem GlobalTreeCacheCorrespondence.cacheQuery_merkle
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
    (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) (output : HashOutput) :
    GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
      (leftCache.cacheQuery
        (Concrete.CacheView.merkleInput parameter level node left right) output)
      (rightCache.cacheQuery
        (Concrete.CacheView.merkleInput parameter level node left right)
          output) := by
  constructor
  · exact hrel.merkle.cacheQuery (MerkleHashInput parameter) leftCache
      rightCache _ output
  · apply hrel.leaves.cacheQuery_distinct
    · intro epoch heq
      exact Concrete.CacheView.leafInput_ne_merkleInput parameter epoch
        (leftEndpoints epoch) level node left right heq.symm
    · intro epoch heq
      exact Concrete.CacheView.leafInput_ne_merkleInput parameter epoch
        (rightEndpoints epoch) level node left right heq.symm

theorem GlobalTreeCacheCorrespondence.cacheQuery_leafPair
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
    (epoch : Epoch) (output : HashOutput) :
    GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
      (leftCache.cacheQuery
        (Concrete.CacheView.leafInput parameter epoch (leftEndpoints epoch))
          output)
      (rightCache.cacheQuery
        (Concrete.CacheView.leafInput parameter epoch (rightEndpoints epoch))
          output) := by
  constructor
  · apply HashCachesAgreeOn.cacheQuery_distinct
      (MerkleHashInput parameter) leftCache rightCache hrel.merkle
    · intro input hinput
      exact merkleHashInput_ne_leafInput parameter epoch (leftEndpoints epoch)
        input hinput
    · intro input hinput
      exact merkleHashInput_ne_leafInput parameter epoch (rightEndpoints epoch)
        input hinput
  · exact hrel.leaves.cacheQuery_pair parameter leftEndpoints
      rightEndpoints leftCache rightCache epoch output

theorem relTriple_randomOracle_globalLeaf_fixed
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hcache : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
    (hleftReplay : ReplayEndpointsMatch parameter leftSecret leftEndpoints
      leftCache)
    (hrightReplay : ReplayEndpointsMatch parameter rightSecret rightEndpoints
      rightCache)
    (epoch : Epoch)
    (hleftNone : leftCache
      (Concrete.CacheView.leafInput parameter epoch (leftEndpoints epoch)) =
        none)
    (hrightNone : rightCache
      (Concrete.CacheView.leafInput parameter epoch (rightEndpoints epoch)) =
        none) :
    RelTriple
      ((randomOracle (Concrete.CacheView.leafInput parameter epoch
        (leftEndpoints epoch))).run leftCache)
      ((randomOracle (Concrete.CacheView.leafInput parameter epoch
        (rightEndpoints epoch))).run rightCache)
      (TreeCacheResult parameter leftSecret rightSecret leftEndpoints
        rightEndpoints) := by
  rw [randomOracle, QueryImpl.withCaching_run_none _ hleftNone,
    QueryImpl.withCaching_run_none _ hrightNone,
    map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
  intro leftOutput rightOutput houtput
  subst rightOutput
  apply relTriple_pure_pure
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact hcache.cacheQuery_leafPair parameter leftEndpoints rightEndpoints
      leftCache rightCache epoch leftOutput
  · exact hleftReplay.cacheQuery_leafInput parameter leftSecret
      leftEndpoints leftCache epoch (leftEndpoints epoch) leftOutput
  · exact hrightReplay.cacheQuery_leafInput parameter rightSecret
      rightEndpoints rightCache epoch (rightEndpoints epoch) leftOutput

theorem relTriple_globalLeafHash_fixed_run
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hcache : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
    (hleftReplay : ReplayEndpointsMatch parameter leftSecret leftEndpoints
      leftCache)
    (hrightReplay : ReplayEndpointsMatch parameter rightSecret rightEndpoints
      rightCache)
    (epoch : Epoch)
    (hleftNone : leftCache
      (Concrete.CacheView.leafInput parameter epoch (leftEndpoints epoch)) =
        none)
    (hrightNone : rightCache
      (Concrete.CacheView.leafInput parameter epoch (rightEndpoints epoch)) =
        none) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.leafHash parameter epoch (leftEndpoints epoch) :
          OracleComp HashSpec Digest)).run leftCache)
      ((simulateQ randomOracle
        (Concrete.leafHash parameter epoch (rightEndpoints epoch) :
          OracleComp HashSpec Digest)).run rightCache)
      (TreeCacheResult parameter leftSecret rightSecret leftEndpoints
        rightEndpoints) := by
  change RelTriple
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$>
        (randomOracle (Concrete.CacheView.leafInput parameter epoch
          (leftEndpoints epoch))).run leftCache)
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$>
        (randomOracle (Concrete.CacheView.leafInput parameter epoch
          (rightEndpoints epoch))).run rightCache) _
  apply relTriple_map
  apply relTriple_post_mono
    (relTriple_randomOracle_globalLeaf_fixed parameter leftEndpoints
      rightEndpoints leftSecret rightSecret leftCache rightCache hcache
        hleftReplay hrightReplay epoch hleftNone hrightNone)
  intro leftResult rightResult hresult
  exact ⟨congrArg truncateHash hresult.1, hresult.2⟩

theorem programmedGlobalChainTrajectoryMaterial_support_as_actual
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter)) :
    material.2 ∈ support
      (Concrete.allChainTrajectoriesFromCache parameter material.1 ∅
        allChains) := by
  apply (mem_support_iff_of_evalDist_eq
    (evalDist_allChainTrajectories_eq_programmed parameter material.1
      allChains ∅ allChains_nodup (by
        simp [AllChainAddressesAbsent])) material.2).mpr
  exact programmedGlobalChainTrajectoryMaterial_support_trajectories
    parameter material hmaterial

theorem programmedGlobalChainTrajectoryMaterial_initialTreeCacheCorrespondence
    (parameter : PublicParameter)
    (left right : GlobalChainTrajectoryMaterial)
    (hleft : left ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (hright : right ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest) :
    GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
      left.2.2 right.2.2 := by
  have hleftActual :=
    programmedGlobalChainTrajectoryMaterial_support_as_actual parameter left
      hleft
  have hrightActual :=
    programmedGlobalChainTrajectoryMaterial_support_as_actual parameter right
      hright
  constructor
  · intro input hinput
    obtain ⟨level, node, haddress⟩ := hinput
    rw [Concrete.allChainTrajectoriesFromCache_avoids_merkle parameter left.1
        level node input haddress allChains ∅ left.2 (by simp) hleftActual,
      Concrete.allChainTrajectoriesFromCache_avoids_merkle parameter right.1
        level node input haddress allChains ∅ right.2 (by simp) hrightActual]
  · intro epoch
    unfold hashCacheLookup
    rw [Concrete.allChainTrajectoriesFromCache_avoids_leaf parameter left.1
        epoch _ (by simp [Concrete.CacheView.leafInput]) allChains ∅ left.2
          (by simp) hleftActual,
      Concrete.allChainTrajectoriesFromCache_avoids_leaf parameter right.1
        epoch _ (by simp [Concrete.CacheView.leafInput]) allChains ∅ right.2
          (by simp) hrightActual]

theorem relTriple_globalMaterial_leafAt_fixed_run
    (parameter : PublicParameter)
    (left right : GlobalChainTrajectoryMaterial)
    (hleft : left ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (hright : right ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (leftCache rightCache : QueryCache HashSpec)
    (hcache : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
    (hleftReplay : ReplayEndpointsMatch parameter left.1 leftEndpoints
      leftCache)
    (hrightReplay : ReplayEndpointsMatch parameter right.1 rightEndpoints
      rightCache)
    (hleftLe : left.2.2 ≤ leftCache) (hrightLe : right.2.2 ≤ rightCache)
    (hleftAbsent : ∀ input, AtHashAddress parameter (.leaf epoch) input →
      leftCache input = none)
    (hrightAbsent : ∀ input, AtHashAddress parameter (.leaf epoch) input →
      rightCache input = none) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.leafAt parameter left.1 epoch :
          OracleComp HashSpec Digest)).run leftCache)
      ((simulateQ randomOracle
        (Concrete.leafAt parameter right.1 epoch :
          OracleComp HashSpec Digest)).run rightCache)
      (TreeCacheResult parameter left.1 right.1 leftEndpoints
        rightEndpoints) := by
  have hleftActual :=
    programmedGlobalChainTrajectoryMaterial_support_as_actual parameter left
      hleft
  have hrightActual :=
    programmedGlobalChainTrajectoryMaterial_support_as_actual parameter right
      hright
  have hleftOneTime :=
    Concrete.allChainTrajectoriesFromCache_oneTimePublicKey_run_eq_pure
      parameter left.1 left.2 hleftActual leftCache hleftLe epoch
  have hrightOneTime :=
    Concrete.allChainTrajectoriesFromCache_oneTimePublicKey_run_eq_pure
      parameter right.1 right.2 hrightActual rightCache hrightLe epoch
  unfold Concrete.leafAt
  simp only [simulateQ_bind, StateT.run_bind, hleftOneTime, hrightOneTime,
    pure_bind]
  rw [← hleftReplay epoch, ← hrightReplay epoch]
  apply relTriple_globalLeafHash_fixed_run parameter leftEndpoints
    rightEndpoints left.1 right.1 leftCache rightCache hcache hleftReplay
      hrightReplay epoch
  · exact hleftAbsent _ (by simp [Concrete.CacheView.leafInput])
  · exact hrightAbsent _ (by simp [Concrete.CacheView.leafInput])

theorem relTriple_randomOracle_globalMerkle_with_endpoint_matches
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hcache : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
    (hleftReplay : ReplayEndpointsMatch parameter leftSecret leftEndpoints
      leftCache)
    (hrightReplay : ReplayEndpointsMatch parameter rightSecret rightEndpoints
      rightCache)
    (level : MerkleLevel) (node : MerkleNode)
    (leftChild rightChild : Digest) :
    RelTriple
      ((randomOracle (Concrete.CacheView.merkleInput parameter level node
        leftChild rightChild)).run leftCache)
      ((randomOracle (Concrete.CacheView.merkleInput parameter level node
        leftChild rightChild)).run rightCache)
      (TreeCacheResult parameter leftSecret rightSecret leftEndpoints
        rightEndpoints) := by
  let input := Concrete.CacheView.merkleInput parameter level node
    leftChild rightChild
  have hinput : MerkleHashInput parameter input :=
    ⟨level, node, by simp [input, Concrete.CacheView.merkleInput]⟩
  cases hleft : leftCache input with
  | none =>
      have hright : rightCache input = none := by
        rw [← hcache.merkle input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft,
        QueryImpl.withCaching_run_none _ hright,
        map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
      intro leftOutput rightOutput houtput
      subst rightOutput
      apply relTriple_pure_pure
      exact ⟨rfl, hcache.cacheQuery_merkle parameter leftEndpoints
          rightEndpoints leftCache rightCache level node leftChild rightChild
            leftOutput,
        hleftReplay.cacheQuery_merkleInput parameter leftSecret leftEndpoints
          leftCache level node leftChild rightChild leftOutput,
        hrightReplay.cacheQuery_merkleInput parameter rightSecret rightEndpoints
          rightCache level node leftChild rightChild leftOutput⟩
  | some output =>
      have hright : rightCache input = some output := by
        rw [← hcache.merkle input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
        QueryImpl.withCaching_run_some _ hright]
      exact relTriple_pure_pure ⟨rfl, hcache, hleftReplay, hrightReplay⟩

theorem relTriple_globalNodeHash_run_with_endpoint_matches
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hcache : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
    (hleftReplay : ReplayEndpointsMatch parameter leftSecret leftEndpoints
      leftCache)
    (hrightReplay : ReplayEndpointsMatch parameter rightSecret rightEndpoints
      rightCache)
    (level : MerkleLevel) (node : MerkleNode)
    (leftChild rightChild : Digest) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.nodeHash parameter level node leftChild rightChild :
          OracleComp HashSpec Digest)).run leftCache)
      ((simulateQ randomOracle
        (Concrete.nodeHash parameter level node leftChild rightChild :
          OracleComp HashSpec Digest)).run rightCache)
      (TreeCacheResult parameter leftSecret rightSecret leftEndpoints
        rightEndpoints) := by
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
    (relTriple_randomOracle_globalMerkle_with_endpoint_matches parameter
      leftEndpoints rightEndpoints leftSecret rightSecret leftCache rightCache
        hcache hleftReplay hrightReplay level node leftChild rightChild)
  intro leftResult rightResult hresult
  exact ⟨congrArg truncateHash hresult.1, hresult.2⟩

theorem relTriple_globalTreeNode_succ_run
    (parameter : PublicParameter)
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
    (hcache : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
    (hleftReplay : ReplayEndpointsMatch parameter leftSecret leftEndpoints
      leftCache)
    (hrightReplay : ReplayEndpointsMatch parameter rightSecret rightEndpoints
      rightCache) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.treeNode parameter leftSecret (levels + 1) node :
          OracleComp HashSpec Digest)).run leftCache)
      ((simulateQ randomOracle
        (Concrete.treeNode parameter rightSecret (levels + 1) node :
          OracleComp HashSpec Digest)).run rightCache)
      (TreeCacheResult parameter leftSecret rightSecret leftEndpoints
        rightEndpoints) := by
  simp only [Concrete.treeNode_succ_eq, simulateQ_bind, StateT.run_bind,
    hleftLeft, hleftRight, hrightLeft, hrightRight, pure_bind,
    hlevel, ↓reduceDIte]
  exact relTriple_globalNodeHash_run_with_endpoint_matches parameter
    leftEndpoints rightEndpoints leftSecret rightSecret leftCache rightCache
      hcache hleftReplay hrightReplay ⟨levels, hlevel⟩ node leftChild
        rightChild

theorem relTriple_globalMaterial_leafTreeValues_run
    (parameter : PublicParameter)
    (left right : GlobalChainTrajectoryMaterial)
    (hleft : left ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (hright : right ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter)) :
    ∀ (indices : List TreeValueIndex),
      (∀ index ∈ indices, index.1.val = 0) →
      indices.Pairwise TreeValueIndex.Precedes →
      ∀ (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
        (leftCache rightCache : QueryCache HashSpec),
        TreeValuesFresh parameter indices leftCache →
        TreeValuesFresh parameter indices rightCache →
        GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
          leftCache rightCache →
        ReplayEndpointsMatch parameter left.1 leftEndpoints leftCache →
        ReplayEndpointsMatch parameter right.1 rightEndpoints rightCache →
        left.2.2 ≤ leftCache → right.2.2 ≤ rightCache →
        RelTriple
          (treeValues parameter left.1 indices leftCache)
          (treeValues parameter right.1 indices rightCache)
          (TreeCacheResult parameter left.1 right.1 leftEndpoints
            rightEndpoints) := by
  intro indices
  induction indices with
  | nil =>
      intro _hzero _hordered leftEndpoints rightEndpoints leftCache rightCache
        _hleftFresh _hrightFresh hcache hleftReplay hrightReplay _hleftLe
          _hrightLe
      simp only [treeValues_nil]
      exact relTriple_pure_pure ⟨rfl, hcache, hleftReplay, hrightReplay⟩
  | cons current indices ih =>
      intro hzero hordered leftEndpoints rightEndpoints leftCache rightCache
        hleftFresh hrightFresh hcache hleftReplay hrightReplay hleftLe hrightLe
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
            (current.computation parameter left.1)).run leftCache)
          ((simulateQ randomOracle
            (current.computation parameter right.1)).run rightCache)
          (TreeCacheResult parameter left.1 right.1 leftEndpoints
            rightEndpoints) := by
        simpa [TreeValueIndex.computation, hcurrentZero] using
          (relTriple_globalMaterial_leafAt_fixed_run parameter left right hleft
            hright leftEndpoints rightEndpoints current.node leftCache
              rightCache hcache hleftReplay hrightReplay hleftLe hrightLe
                hleftAbsent hrightAbsent)
      simp only [treeValues_cons]
      apply relTriple_bind (relTriple_with_support hhead)
      intro leftHeadResult rightHeadResult hheadResult
      obtain ⟨hheadRelation, hleftHeadSupport, hrightHeadSupport⟩ := hheadResult
      have hleftTailFresh := treeValue_preserves_tail_fresh parameter left.1
        current indices hcurrentBefore leftCache hleftFresh leftHeadResult
          hleftHeadSupport
      have hrightTailFresh := treeValue_preserves_tail_fresh parameter right.1
        current indices hcurrentBefore rightCache hrightFresh rightHeadResult
          hrightHeadSupport
      have hleftNextLe : left.2.2 ≤ leftHeadResult.2 := hleftLe.trans
        (Concrete.CacheReplay.randomOracle_cache_le
          (current.computation parameter left.1) leftCache leftHeadResult
            hleftHeadSupport)
      have hrightNextLe : right.2.2 ≤ rightHeadResult.2 := hrightLe.trans
        (Concrete.CacheReplay.randomOracle_cache_le
          (current.computation parameter right.1) rightCache rightHeadResult
            hrightHeadSupport)
      apply relTriple_bind
        (ih htailZero htailOrdered leftEndpoints rightEndpoints
          leftHeadResult.2 rightHeadResult.2 hleftTailFresh hrightTailFresh
            hheadRelation.2.1 hheadRelation.2.2.1 hheadRelation.2.2.2
              hleftNextLe hrightNextLe)
      intro leftTailResult rightTailResult htailRelation
      apply relTriple_pure_pure
      exact ⟨congrArg₂ List.cons hheadRelation.1 htailRelation.1,
        htailRelation.2⟩


theorem relTriple_globalMaterial_allLeafValues_run
    (parameter : PublicParameter)
    (left right : GlobalChainTrajectoryMaterial)
    (hleft : left ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (hright : right ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter)) :
    RelTriple
      (treeValues parameter left.1 (treeValueIndicesAtHeight 0) left.2.2)
      (treeValues parameter right.1 (treeValueIndicesAtHeight 0) right.2.2)
      (GlobalTreeValuesResult parameter left.1 right.1) := by
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
      (treeValueIndicesAtHeight 0) left.2.2 := by
    have hall := programmedAllChainTrajectories_treeValuesFresh parameter left.1
      left.2
        (programmedGlobalChainTrajectoryMaterial_support_trajectories
          parameter left hleft)
    intro index _hindex input hinput
    exact hall index (mem_allTreeValueIndices index) input hinput
  have hrightFresh : TreeValuesFresh parameter
      (treeValueIndicesAtHeight 0) right.2.2 := by
    have hall := programmedAllChainTrajectories_treeValuesFresh parameter right.1
      right.2
        (programmedGlobalChainTrajectoryMaterial_support_trajectories
          parameter right hright)
    intro index _hindex input hinput
    exact hall index (mem_allTreeValueIndices index) input hinput
  let leftEndpoints := fun epoch =>
    Concrete.CacheReplay.oneTimePublicKey left.2.2 parameter left.1 epoch
  let rightEndpoints := fun epoch =>
    Concrete.CacheReplay.oneTimePublicKey right.2.2 parameter right.1 epoch
  apply relTriple_post_mono
    (relTriple_globalMaterial_leafTreeValues_run parameter left right hleft
      hright (treeValueIndicesAtHeight 0) hzero hordered leftEndpoints
        rightEndpoints left.2.2 right.2.2 hleftFresh hrightFresh
          (programmedGlobalChainTrajectoryMaterial_initialTreeCacheCorrespondence
            parameter left right hleft hright leftEndpoints rightEndpoints)
          (fun _ => rfl) (fun _ => rfl) le_rfl le_rfl)
  intro leftResult rightResult hresult
  exact ⟨hresult.1, leftEndpoints, rightEndpoints, hresult.2⟩

theorem relTriple_globalMaterial_merkleTreeValue_run
    (parameter : PublicParameter)
    (left right : GlobalChainTrajectoryMaterial)
    (processed : List TreeValueIndex)
    (leftPrefix rightPrefix : List Digest × QueryCache HashSpec)
    (hleftPrefix : leftPrefix ∈ support
      (treeValues parameter left.1 processed left.2.2))
    (hrightPrefix : rightPrefix ∈ support
      (treeValues parameter right.1 processed right.2.2))
    (hprefixValues : leftPrefix.1 = rightPrefix.1)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (hcache : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftPrefix.2 rightPrefix.2)
    (hleftReplay : ReplayEndpointsMatch parameter left.1 leftEndpoints
      leftPrefix.2)
    (hrightReplay : ReplayEndpointsMatch parameter right.1 rightEndpoints
      rightPrefix.2)
    (current : TreeValueIndex) (hpositive : 0 < current.1.val)
    (hleftChild : current.child hpositive false ∈ processed)
    (hrightChild : current.child hpositive true ∈ processed) :
    RelTriple
      ((simulateQ randomOracle
        (current.computation parameter left.1)).run leftPrefix.2)
      ((simulateQ randomOracle
        (current.computation parameter right.1)).run rightPrefix.2)
      (TreeCacheResult parameter left.1 right.1 leftEndpoints
        rightEndpoints) := by
  let levels := current.1.val - 1
  have hsucc : current.1.val = levels + 1 := by
    dsimp [levels]
    omega
  have hlevel : levels < treeHeight := by
    dsimp [levels]
    omega
  let leftIndex := current.child hpositive false
  let rightIndex := current.child hpositive true
  have hleftIndex : leftIndex ∈ processed := hleftChild
  have hrightIndex : rightIndex ∈ processed := hrightChild
  have hleftTreeReplay := treeValues_support_replay parameter left.1 processed
    left.2.2 leftPrefix hleftPrefix
  have hrightTreeReplay := treeValues_support_replay parameter right.1 processed
    right.2.2 rightPrefix hrightPrefix
  have hleftChildEq := treeValuesReplay_eq_at_mem parameter parameter left.1
    right.1 leftPrefix.2 rightPrefix.2 processed leftPrefix.1 hleftTreeReplay
      (hprefixValues ▸ hrightTreeReplay) leftIndex hleftIndex
  have hrightChildEq := treeValuesReplay_eq_at_mem parameter parameter left.1
    right.1 leftPrefix.2 rightPrefix.2 processed leftPrefix.1 hleftTreeReplay
      (hprefixValues ▸ hrightTreeReplay) rightIndex hrightIndex
  let leftChild := Concrete.CacheReplay.treeNode leftPrefix.2 parameter left.1
    levels (Concrete.childNode current.node false)
  let rightChild := Concrete.CacheReplay.treeNode leftPrefix.2 parameter left.1
    levels (Concrete.childNode current.node true)
  have hleftLeft := treeValues_rerun_index_eq_pure parameter left.1 processed
    left.2.2 leftPrefix hleftPrefix leftIndex hleftIndex
  have hleftRight := treeValues_rerun_index_eq_pure parameter right.1 processed
    right.2.2 rightPrefix hrightPrefix leftIndex hleftIndex
  have hrightLeft := treeValues_rerun_index_eq_pure parameter left.1 processed
    left.2.2 leftPrefix hleftPrefix rightIndex hrightIndex
  have hrightRight := treeValues_rerun_index_eq_pure parameter right.1 processed
    right.2.2 rightPrefix hrightPrefix rightIndex hrightIndex
  have hleftChildEq' : leftChild =
      Concrete.CacheReplay.treeNode rightPrefix.2 parameter right.1 levels
        (Concrete.childNode current.node false) := by
    simpa [leftIndex, leftChild, TreeValueIndex.child, levels] using
      hleftChildEq
  have hrightChildEq' : rightChild =
      Concrete.CacheReplay.treeNode rightPrefix.2 parameter right.1 levels
        (Concrete.childNode current.node true) := by
    simpa [rightIndex, rightChild, TreeValueIndex.child, levels] using
      hrightChildEq
  have hleftLeft' :
      (simulateQ randomOracle
        (Concrete.treeNode parameter left.1 levels
          (Concrete.childNode current.node false) :
          OracleComp HashSpec Digest)).run leftPrefix.2 =
        pure (leftChild, leftPrefix.2) := by
    change (simulateQ randomOracle
      (Concrete.treeNode parameter left.1 levels
        (Concrete.childNode current.node false))).run leftPrefix.2 = _
      at hleftLeft
    exact hleftLeft
  have hleftRight' :
      (simulateQ randomOracle
        (Concrete.treeNode parameter right.1 levels
          (Concrete.childNode current.node false) :
          OracleComp HashSpec Digest)).run rightPrefix.2 =
        pure (leftChild, rightPrefix.2) := by
    change (simulateQ randomOracle
      (Concrete.treeNode parameter right.1 levels
        (Concrete.childNode current.node false))).run rightPrefix.2 =
      pure (Concrete.CacheReplay.treeNode rightPrefix.2 parameter right.1
        levels (Concrete.childNode current.node false), rightPrefix.2)
      at hleftRight
    rw [hleftChildEq']
    exact hleftRight
  have hrightLeft' :
      (simulateQ randomOracle
        (Concrete.treeNode parameter left.1 levels
          (Concrete.childNode current.node true) :
          OracleComp HashSpec Digest)).run leftPrefix.2 =
        pure (rightChild, leftPrefix.2) := by
    change (simulateQ randomOracle
      (Concrete.treeNode parameter left.1 levels
        (Concrete.childNode current.node true))).run leftPrefix.2 = _
      at hrightLeft
    exact hrightLeft
  have hrightRight' :
      (simulateQ randomOracle
        (Concrete.treeNode parameter right.1 levels
          (Concrete.childNode current.node true) :
          OracleComp HashSpec Digest)).run rightPrefix.2 =
        pure (rightChild, rightPrefix.2) := by
    change (simulateQ randomOracle
      (Concrete.treeNode parameter right.1 levels
        (Concrete.childNode current.node true))).run rightPrefix.2 =
      pure (Concrete.CacheReplay.treeNode rightPrefix.2 parameter right.1
        levels (Concrete.childNode current.node true), rightPrefix.2)
      at hrightRight
    rw [hrightChildEq']
    exact hrightRight
  change RelTriple
    ((simulateQ randomOracle
      (Concrete.treeNode parameter left.1 current.1.val current.node)).run
        leftPrefix.2)
    ((simulateQ randomOracle
      (Concrete.treeNode parameter right.1 current.1.val current.node)).run
        rightPrefix.2) _
  rw [hsucc]
  exact relTriple_globalTreeNode_succ_run parameter leftEndpoints
    rightEndpoints left.1 right.1 levels current.node hlevel leftChild
      rightChild leftPrefix.2 rightPrefix.2 hleftLeft' hleftRight'
        hrightLeft' hrightRight' hcache hleftReplay hrightReplay

set_option maxRecDepth 100000 in
theorem relTriple_globalMaterial_merkleTreeValues_run
    (parameter : PublicParameter)
    (left right : GlobalChainTrajectoryMaterial) :
    ∀ (indices base : List TreeValueIndex)
      (leftBase rightBase : List Digest × QueryCache HashSpec),
      (∀ current ∈ indices, ∃ hpositive : 0 < current.1.val,
        current.child hpositive false ∈ base ∧
          current.child hpositive true ∈ base) →
      indices.Pairwise TreeValueIndex.Precedes →
      leftBase ∈ support (treeValues parameter left.1 base left.2.2) →
      rightBase ∈ support (treeValues parameter right.1 base right.2.2) →
      leftBase.1 = rightBase.1 →
      TreeValuesFresh parameter indices leftBase.2 →
      TreeValuesFresh parameter indices rightBase.2 →
      ∀ (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest),
      GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
        leftBase.2 rightBase.2 →
      ReplayEndpointsMatch parameter left.1 leftEndpoints leftBase.2 →
      ReplayEndpointsMatch parameter right.1 rightEndpoints rightBase.2 →
      RelTriple
        (treeValues parameter left.1 indices leftBase.2)
        (treeValues parameter right.1 indices rightBase.2)
        (fun leftResult rightResult =>
          leftResult.1 = rightResult.1 ∧
            GlobalTreeCacheCorrespondence parameter leftEndpoints
              rightEndpoints leftResult.2 rightResult.2 ∧
            ReplayEndpointsMatch parameter left.1 leftEndpoints leftResult.2 ∧
            ReplayEndpointsMatch parameter right.1 rightEndpoints
              rightResult.2 ∧
            (leftBase.1 ++ leftResult.1, leftResult.2) ∈ support
              (treeValues parameter left.1 (base ++ indices) left.2.2) ∧
            (rightBase.1 ++ rightResult.1, rightResult.2) ∈ support
              (treeValues parameter right.1 (base ++ indices) right.2.2)) := by
  intro indices
  induction indices with
  | nil =>
      intro base leftBase rightBase _hchildren _hordered hleftBase hrightBase
        _hbaseValues _hleftFresh _hrightFresh leftEndpoints rightEndpoints
          hcache hleftReplay hrightReplay
      simp only [treeValues_nil]
      apply relTriple_pure_pure
      refine ⟨rfl, hcache, hleftReplay, hrightReplay, ?_, ?_⟩
      · simpa using hleftBase
      · simpa using hrightBase
  | cons current indices ih =>
      intro base leftBase rightBase hchildren hordered hleftBase hrightBase
        hbaseValues hleftFresh hrightFresh leftEndpoints rightEndpoints hcache
          hleftReplay hrightReplay
      obtain ⟨hpositive, hleftChild, hrightChild⟩ :=
        hchildren current (by simp)
      have htailChildren : ∀ target ∈ indices,
          ∃ hpositive : 0 < target.1.val,
            target.child hpositive false ∈ base ∧
              target.child hpositive true ∈ base := by
        intro target htarget
        exact hchildren target (by simp [htarget])
      have hcurrentBefore : ∀ target ∈ indices,
          current.Precedes target := (List.pairwise_cons.mp hordered).1
      have htailOrdered : indices.Pairwise TreeValueIndex.Precedes :=
        (List.pairwise_cons.mp hordered).2
      have hhead := relTriple_globalMaterial_merkleTreeValue_run parameter
        left right base leftBase rightBase hleftBase hrightBase hbaseValues
          leftEndpoints rightEndpoints hcache hleftReplay hrightReplay current
            hpositive hleftChild hrightChild
      let LeftProperty := fun result : Digest × QueryCache HashSpec =>
        TreeValuesFresh parameter indices result.2 ∧
          (leftBase.1 ++ [result.1], result.2) ∈ support
            (treeValues parameter left.1 (base ++ [current]) left.2.2)
      let RightProperty := fun result : Digest × QueryCache HashSpec =>
        TreeValuesFresh parameter indices result.2 ∧
          (rightBase.1 ++ [result.1], result.2) ∈ support
            (treeValues parameter right.1 (base ++ [current]) right.2.2)
      have hleftProperty : ∀ result ∈ support
          ((simulateQ randomOracle
            (current.computation parameter left.1)).run leftBase.2),
          LeftProperty result := by
        intro result hresult
        exact ⟨treeValue_preserves_tail_fresh parameter left.1 current
            indices hcurrentBefore leftBase.2 hleftFresh result hresult,
          treeValues_append_support parameter left.1 base [current] left.2.2
            leftBase ([result.1], result.2) hleftBase
              (treeValues_singleton_support parameter left.1 current
                leftBase.2 result hresult)⟩
      have hrightProperty : ∀ result ∈ support
          ((simulateQ randomOracle
            (current.computation parameter right.1)).run rightBase.2),
          RightProperty result := by
        intro result hresult
        exact ⟨treeValue_preserves_tail_fresh parameter right.1 current
            indices hcurrentBefore rightBase.2 hrightFresh result hresult,
          treeValues_append_support parameter right.1 base [current] right.2.2
            rightBase ([result.1], result.2) hrightBase
              (treeValues_singleton_support parameter right.1 current
                rightBase.2 result hresult)⟩
      have hheadExtended := relTriple_strengthen_support
        (leftProperty := LeftProperty) (rightProperty := RightProperty)
        hhead hleftProperty hrightProperty
      simp only [treeValues_cons]
      apply relTriple_bind hheadExtended
      intro leftHeadResult rightHeadResult hheadResult
      obtain ⟨hheadRelation, hleftProperties, hrightProperties⟩ :=
        hheadResult
      obtain ⟨leftHead, leftHeadCache⟩ := leftHeadResult
      obtain ⟨rightHead, rightHeadCache⟩ := rightHeadResult
      dsimp only at hheadRelation hleftProperties hrightProperties ⊢
      unfold TreeCacheResult at hheadRelation
      simp only at hheadRelation
      let nextLeftBase : List Digest × QueryCache HashSpec :=
        (leftBase.1 ++ [leftHead], leftHeadCache)
      let nextRightBase : List Digest × QueryCache HashSpec :=
        (rightBase.1 ++ [rightHead], rightHeadCache)
      have hnextValues : nextLeftBase.1 = nextRightBase.1 := by
        simp [nextLeftBase, nextRightBase, hbaseValues, hheadRelation.1]
      have hnextChildren : ∀ target ∈ indices,
          ∃ hpositive : 0 < target.1.val,
            target.child hpositive false ∈ base ++ [current] ∧
              target.child hpositive true ∈ base ++ [current] := by
        intro target htarget
        obtain ⟨hpos, hleft, hright⟩ := htailChildren target htarget
        exact ⟨hpos, List.mem_append_left [current] hleft,
          List.mem_append_left [current] hright⟩
      apply relTriple_bind
        (ih (base ++ [current]) nextLeftBase nextRightBase hnextChildren
          htailOrdered hleftProperties.2 hrightProperties.2 hnextValues
            hleftProperties.1 hrightProperties.1 leftEndpoints rightEndpoints
              hheadRelation.2.1 hheadRelation.2.2.1
                hheadRelation.2.2.2)
      intro leftTailResult rightTailResult htailResult
      apply relTriple_pure_pure
      refine ⟨congrArg₂ List.cons hheadRelation.1 htailResult.1,
        htailResult.2.1, htailResult.2.2.1, htailResult.2.2.2.1, ?_, ?_⟩
      · simpa [nextLeftBase, List.append_assoc] using
          htailResult.2.2.2.2.1
      · simpa [nextRightBase, List.append_assoc] using
          htailResult.2.2.2.2.2

theorem relTriple_globalMaterial_merkleHeight_run
    (parameter : PublicParameter)
    (left right : GlobalChainTrajectoryMaterial)
    (height : Fin (treeHeight + 1)) (hpositive : 0 < height.val)
    (leftBase rightBase : List Digest × QueryCache HashSpec)
    (hleftBase : leftBase ∈ support
      (treeValues parameter left.1 (treeValueIndicesBelow height.val)
        left.2.2))
    (hrightBase : rightBase ∈ support
      (treeValues parameter right.1 (treeValueIndicesBelow height.val)
        right.2.2))
    (hbaseValues : leftBase.1 = rightBase.1)
    (hleftFresh : TreeValuesFresh parameter
      (treeValueIndicesAtHeight height) leftBase.2)
    (hrightFresh : TreeValuesFresh parameter
      (treeValueIndicesAtHeight height) rightBase.2)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (hcache : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftBase.2 rightBase.2)
    (hleftReplay : ReplayEndpointsMatch parameter left.1 leftEndpoints
      leftBase.2)
    (hrightReplay : ReplayEndpointsMatch parameter right.1 rightEndpoints
      rightBase.2) :
    RelTriple
      (treeValues parameter left.1 (treeValueIndicesAtHeight height)
        leftBase.2)
      (treeValues parameter right.1 (treeValueIndicesAtHeight height)
        rightBase.2)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
            leftResult.2 rightResult.2 ∧
          ReplayEndpointsMatch parameter left.1 leftEndpoints leftResult.2 ∧
          ReplayEndpointsMatch parameter right.1 rightEndpoints
            rightResult.2 ∧
          (leftBase.1 ++ leftResult.1, leftResult.2) ∈ support
            (treeValues parameter left.1
              (treeValueIndicesBelow (height.val + 1)) left.2.2) ∧
          (rightBase.1 ++ rightResult.1, rightResult.2) ∈ support
            (treeValues parameter right.1
              (treeValueIndicesBelow (height.val + 1)) right.2.2)) := by
  have hchildren : ∀ current ∈ treeValueIndicesAtHeight height,
      ∃ hcurrentPositive : 0 < current.1.val,
        current.child hcurrentPositive false ∈
            treeValueIndicesBelow height.val ∧
          current.child hcurrentPositive true ∈
            treeValueIndicesBelow height.val := by
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
  have hcoupling := relTriple_globalMaterial_merkleTreeValues_run parameter
    left right (treeValueIndicesAtHeight height)
      (treeValueIndicesBelow height.val) leftBase rightBase hchildren hordered
        hleftBase hrightBase hbaseValues hleftFresh hrightFresh leftEndpoints
          rightEndpoints hcache hleftReplay hrightReplay
  apply relTriple_post_mono hcoupling
  intro leftResult rightResult hresult
  have hbelow := treeValueIndicesBelow_succ height.val height.isLt
  exact ⟨hresult.1, hresult.2.1, hresult.2.2.1,
    hresult.2.2.2.1, hbelow ▸ hresult.2.2.2.2.1,
      hbelow ▸ hresult.2.2.2.2.2⟩

theorem globalMaterial_treeValuesBelow_fresh_at_height
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (height : Fin (treeHeight + 1))
    (result : List Digest × QueryCache HashSpec)
    (hresult : result ∈ support
      (treeValues parameter material.1
        (treeValueIndicesBelow height.val) material.2.2)) :
    TreeValuesFresh parameter (treeValueIndicesAtHeight height) result.2 := by
  have hbefore : ∀ current ∈ treeValueIndicesBelow height.val,
      ∀ target ∈ treeValueIndicesAtHeight height,
        current.Precedes target := by
    intro current hcurrent target htarget
    have hcurrentLt := treeValueIndicesBelow_height_lt height.val
      (by omega) current hcurrent
    have htargetHeight :=
      (mem_treeValueIndicesAtHeight_iff height target).1 htarget
    left
    simpa [congrArg Fin.val htargetHeight] using hcurrentLt
  have hinitialFresh : TreeValuesFresh parameter
      (treeValueIndicesAtHeight height) material.2.2 := by
    have hall := programmedAllChainTrajectories_treeValuesFresh parameter
      material.1 material.2
        (programmedGlobalChainTrajectoryMaterial_support_trajectories
          parameter material hmaterial)
    intro index _hindex input hinput
    exact hall index (mem_allTreeValueIndices index) input hinput
  exact treeValues_preserves_fresh_after parameter material.1
    (treeValueIndicesBelow height.val) (treeValueIndicesAtHeight height)
    hbefore material.2.2 hinitialFresh result hresult

theorem relTriple_globalMaterial_treeValuesBelow_one
    (parameter : PublicParameter)
    (left right : GlobalChainTrajectoryMaterial)
    (hleft : left ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (hright : right ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter)) :
    RelTriple
      (treeValues parameter left.1 (treeValueIndicesBelow 1) left.2.2)
      (treeValues parameter right.1 (treeValueIndicesBelow 1) right.2.2)
      (GlobalTreeValuesResult parameter left.1 right.1) := by
  have hheight : treeValueIndicesBelow 1 = treeValueIndicesAtHeight 0 := by
    rw [treeValueIndicesBelow_succ 0 (by omega)]
    rw [treeValueIndicesBelow]
    exact List.nil_append _
  rw [hheight]
  exact relTriple_globalMaterial_allLeafValues_run parameter left right hleft
    hright

set_option maxRecDepth 1000000 in
theorem relTriple_globalMaterial_treeValuesBelow_succ
    (parameter : PublicParameter)
    (left right : GlobalChainTrajectoryMaterial)
    (hleft : left ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (hright : right ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (height : Nat) (hpositive : 1 ≤ height)
    (hcurrentBound : height < treeHeight + 1)
    (hprefix : RelTriple
      (treeValues parameter left.1 (treeValueIndicesBelow height) left.2.2)
      (treeValues parameter right.1 (treeValueIndicesBelow height) right.2.2)
      (GlobalTreeValuesResult parameter left.1 right.1)) :
    RelTriple
      (treeValues parameter left.1 (treeValueIndicesBelow (height + 1))
        left.2.2)
      (treeValues parameter right.1 (treeValueIndicesBelow (height + 1))
        right.2.2)
      (GlobalTreeValuesResult parameter left.1 right.1) := by
  let currentHeight : Fin (treeHeight + 1) := ⟨height, hcurrentBound⟩
  have hdecompose := treeValueIndicesBelow_succ height hcurrentBound
  rw [hdecompose, treeValues_append, treeValues_append]
  apply relTriple_bind (relTriple_with_support hprefix)
  intro leftBase rightBase hbase
  obtain ⟨hbaseRelation, hleftBase, hrightBase⟩ := hbase
  unfold GlobalTreeValuesResult at hbaseRelation
  obtain ⟨hbaseValues, leftEndpoints, rightEndpoints, hbaseCache,
    hleftReplay, hrightReplay⟩ := hbaseRelation
  have hleftFresh := globalMaterial_treeValuesBelow_fresh_at_height parameter
    left hleft currentHeight leftBase hleftBase
  have hrightFresh := globalMaterial_treeValuesBelow_fresh_at_height parameter
    right hright currentHeight rightBase hrightBase
  have hheightCoupling := relTriple_globalMaterial_merkleHeight_run parameter
    left right currentHeight (by
      dsimp [currentHeight]
      exact hpositive)
    leftBase rightBase hleftBase hrightBase hbaseValues hleftFresh hrightFresh
      leftEndpoints rightEndpoints hbaseCache hleftReplay hrightReplay
  apply relTriple_bind hheightCoupling
  intro leftCurrent rightCurrent hcurrent
  obtain ⟨leftValues, leftCache⟩ := leftBase
  obtain ⟨rightValues, rightCache⟩ := rightBase
  obtain ⟨leftNewValues, leftNewCache⟩ := leftCurrent
  obtain ⟨rightNewValues, rightNewCache⟩ := rightCurrent
  dsimp only at hbaseValues hcurrent ⊢
  apply relTriple_pure_pure
  unfold GlobalTreeValuesResult
  exact ⟨congrArg₂ List.append hbaseValues hcurrent.1,
    leftEndpoints, rightEndpoints, hcurrent.2.1, hcurrent.2.2.1,
      hcurrent.2.2.2.1⟩

theorem relTriple_globalMaterial_treeValuesBelow
    (parameter : PublicParameter)
    (left right : GlobalChainTrajectoryMaterial)
    (hleft : left ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (hright : right ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter)) :
    ∀ (height : Nat), 1 ≤ height → height ≤ treeHeight + 1 →
      RelTriple
        (treeValues parameter left.1 (treeValueIndicesBelow height) left.2.2)
        (treeValues parameter right.1 (treeValueIndicesBelow height) right.2.2)
        (GlobalTreeValuesResult parameter left.1 right.1) := by
  intro height
  induction height with
  | zero => intro hpositive _hbound; omega
  | succ height ih =>
      intro _hpositive hbound
      by_cases hzero : height = 0
      · subst height
        exact relTriple_globalMaterial_treeValuesBelow_one parameter left right
          hleft hright
      · apply relTriple_globalMaterial_treeValuesBelow_succ parameter left
          right hleft hright height (by omega) (by omega)
        exact ih (by omega) (by omega)

theorem relTriple_globalMaterial_allTreeValues_run
    (parameter : PublicParameter)
    (left right : GlobalChainTrajectoryMaterial)
    (hleft : left ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (hright : right ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter)) :
    RelTriple
      (treeValues parameter left.1 allTreeValueIndices left.2.2)
      (treeValues parameter right.1 allTreeValueIndices right.2.2)
      (GlobalTreeValuesResult parameter left.1 right.1) := by
  rw [← treeValueIndicesBelow_all]
  exact relTriple_globalMaterial_treeValuesBelow parameter left right hleft
    hright (treeHeight + 1) (by omega) le_rfl

end XmssSecurity.CappedChain
