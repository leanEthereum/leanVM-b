import XmssSecurity.CappedGlobalTreeCoupling
import XmssSecurity.CappedChain.CausalSigningKeygenCoupling
import XmssSecurity.CausalTreeCacheCorrespondence

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

theorem GlobalTreeCacheCorrespondence.cacheQuery_leafPair_update
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
    (epoch : Epoch) (newLeft newRight : ChainIndex → Digest)
    (output : HashOutput) :
    GlobalTreeCacheCorrespondence parameter
      (Function.update leftEndpoints epoch newLeft)
      (Function.update rightEndpoints epoch newRight)
      (leftCache.cacheQuery
        (Concrete.CacheView.leafInput parameter epoch newLeft) output)
      (rightCache.cacheQuery
        (Concrete.CacheView.leafInput parameter epoch newRight) output) := by
  constructor
  · apply HashCachesAgreeOn.cacheQuery_distinct
      (MerkleHashInput parameter) leftCache rightCache hrel.merkle
    · intro input hinput
      exact merkleHashInput_ne_leafInput parameter epoch newLeft input hinput
    · intro input hinput
      exact merkleHashInput_ne_leafInput parameter epoch newRight input hinput
  · exact hrel.leaves.cacheQuery_pair_update parameter leftEndpoints
      rightEndpoints leftCache rightCache epoch newLeft newRight output

theorem relTriple_randomOracle_globalLeafPair_of_both_none
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
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
          GlobalTreeCacheCorrespondence parameter
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
  exact ⟨rfl, hrel.cacheQuery_leafPair_update parameter leftEndpoints
    rightEndpoints leftCache rightCache epoch newLeft newRight leftOutput⟩

theorem relTriple_globalLeafHash_run
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
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
          GlobalTreeCacheCorrespondence parameter
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
    (relTriple_randomOracle_globalLeafPair_of_both_none parameter
      leftEndpoints rightEndpoints leftCache rightCache hrel epoch
        newLeft newRight hleftNone hrightNone)
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
    rw [Concrete.allChainTrajectoriesFromCache_avoids_leaf parameter left.1
        epoch _ (by simp [Concrete.CacheView.leafInput]) allChains ∅ left.2
          (by simp) hleftActual,
      Concrete.allChainTrajectoriesFromCache_avoids_leaf parameter right.1
        epoch _ (by simp [Concrete.CacheView.leafInput]) allChains ∅ right.2
          (by simp) hrightActual]

theorem relTriple_globalMaterial_leafAt_run
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
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          ∃ newLeft newRight,
            GlobalTreeCacheCorrespondence parameter
              (Function.update leftEndpoints epoch newLeft)
              (Function.update rightEndpoints epoch newRight)
              leftResult.2 rightResult.2 ∧
            newLeft = Concrete.CacheReplay.oneTimePublicKey leftResult.2
              parameter left.1 epoch ∧
            newRight = Concrete.CacheReplay.oneTimePublicKey rightResult.2
              parameter right.1 epoch) := by
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
  let newLeft := Concrete.CacheReplay.oneTimePublicKey leftCache parameter
    left.1 epoch
  let newRight := Concrete.CacheReplay.oneTimePublicKey rightCache parameter
    right.1 epoch
  have hleftNone : leftCache
      (Concrete.CacheView.leafInput parameter epoch newLeft) = none :=
    hleftAbsent _ (by simp [Concrete.CacheView.leafInput])
  have hrightNone : rightCache
      (Concrete.CacheView.leafInput parameter epoch newRight) = none :=
    hrightAbsent _ (by simp [Concrete.CacheView.leafInput])
  apply relTriple_post_mono (relTriple_with_support
    (relTriple_globalLeafHash_run parameter leftEndpoints rightEndpoints
      leftCache rightCache hcache epoch newLeft newRight hleftNone hrightNone))
  intro leftResult rightResult hresult
  obtain ⟨hleaf, hleftLeaf, hrightLeaf⟩ := hresult
  have hleftLeafLe := Concrete.CacheReplay.randomOracle_cache_le
    (Concrete.leafHash parameter epoch newLeft : OracleComp HashSpec Digest)
      leftCache leftResult hleftLeaf
  have hrightLeafLe := Concrete.CacheReplay.randomOracle_cache_le
    (Concrete.leafHash parameter epoch newRight : OracleComp HashSpec Digest)
      rightCache rightResult hrightLeaf
  have hleftSupport : (newLeft, leftCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.oneTimePublicKey parameter left.1 epoch)).run leftCache) := by
    rw [hleftOneTime]
    simp [newLeft]
  have hrightSupport : (newRight, rightCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.oneTimePublicKey parameter right.1 epoch)).run rightCache) := by
    rw [hrightOneTime]
    simp [newRight]
  have hleftReplay :=
    Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
      (Concrete.oneTimePublicKey parameter left.1 epoch :
        OracleComp HashSpec (ChainIndex → Digest)) leftCache leftCache
          leftResult.2 newLeft hleftSupport hleftLeafLe
  have hrightReplay :=
    Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
      (Concrete.oneTimePublicKey parameter right.1 epoch :
        OracleComp HashSpec (ChainIndex → Digest)) rightCache rightCache
          rightResult.2 newRight hrightSupport hrightLeafLe
  rw [Concrete.CacheReplay.eval_oneTimePublicKey] at hleftReplay hrightReplay
  exact ⟨hleaf.1, newLeft, newRight, hleaf.2, hleftReplay.symm,
    hrightReplay.symm⟩

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
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
            leftResult.2 rightResult.2 ∧
          ReplayEndpointsMatch parameter leftSecret leftEndpoints
            leftResult.2 ∧
          ReplayEndpointsMatch parameter rightSecret rightEndpoints
            rightResult.2) := by
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
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
            leftResult.2 rightResult.2 ∧
          ReplayEndpointsMatch parameter leftSecret leftEndpoints
            leftResult.2 ∧
          ReplayEndpointsMatch parameter rightSecret rightEndpoints
            rightResult.2) := by
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
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
            leftResult.2 rightResult.2 ∧
          ReplayEndpointsMatch parameter leftSecret leftEndpoints
            leftResult.2 ∧
          ReplayEndpointsMatch parameter rightSecret rightEndpoints
            rightResult.2) := by
  simp only [Concrete.treeNode_succ_eq, simulateQ_bind, StateT.run_bind,
    hleftLeft, hleftRight, hrightLeft, hrightRight, pure_bind,
    hlevel, ↓reduceDIte]
  exact relTriple_globalNodeHash_run_with_endpoint_matches parameter
    leftEndpoints rightEndpoints leftSecret rightSecret leftCache rightCache
      hcache hleftReplay hrightReplay ⟨levels, hlevel⟩ node leftChild
        rightChild

end XmssSecurity.CappedChain
