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

set_option maxHeartbeats 800000 in
set_option maxRecDepth 100000 in
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
        left.2.2 ≤ leftCache → right.2.2 ≤ rightCache →
        RelTriple
          (treeValues parameter left.1 indices leftCache)
          (treeValues parameter right.1 indices rightCache)
          (fun leftResult rightResult =>
            leftResult.1 = rightResult.1 ∧
              ∃ finalLeft finalRight,
                GlobalTreeCacheCorrespondence parameter finalLeft finalRight
                  leftResult.2 rightResult.2 ∧
                LeafReplayOutputsCorrespondOn parameter left.1 right.1 indices
                  leftResult.2 rightResult.2) := by
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
            (current.computation parameter left.1)).run leftCache)
          ((simulateQ randomOracle
            (current.computation parameter right.1)).run rightCache)
          (fun leftResult rightResult =>
            leftResult.1 = rightResult.1 ∧
              ∃ newLeft newRight,
                GlobalTreeCacheCorrespondence parameter
                  (Function.update leftEndpoints current.node newLeft)
                  (Function.update rightEndpoints current.node newRight)
                  leftResult.2 rightResult.2 ∧
                newLeft = Concrete.CacheReplay.oneTimePublicKey leftResult.2
                  parameter left.1 current.node ∧
                newRight = Concrete.CacheReplay.oneTimePublicKey rightResult.2
                  parameter right.1 current.node) := by
        simpa [TreeValueIndex.computation, hcurrentZero] using
          (relTriple_globalMaterial_leafAt_run parameter left right hleft hright
            leftEndpoints rightEndpoints current.node leftCache rightCache
              hcache hleftLe hrightLe hleftAbsent hrightAbsent)
      have hheadSupport := relTriple_with_support hhead
      simp only [treeValues_cons]
      apply relTriple_bind hheadSupport
      intro leftHeadResult rightHeadResult hheadResult
      obtain ⟨hheadRelation, hleftHeadSupport, hrightHeadSupport⟩ :=
        hheadResult
      obtain ⟨hheadValue, nextLeft, nextRight, hnextCache,
        hnextLeft, hnextRight⟩ := hheadRelation
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
        (relTriple_with_support (ih htailZero htailOrdered
          (Function.update leftEndpoints current.node nextLeft)
          (Function.update rightEndpoints current.node nextRight)
          leftHeadResult.2 rightHeadResult.2 hleftTailFresh hrightTailFresh
            hnextCache hleftNextLe hrightNextLe))
      intro leftTailResult rightTailResult htailResult
      obtain ⟨htailRelation, hleftTailSupport, hrightTailSupport⟩ :=
        htailResult
      obtain ⟨htailValues, finalLeft, finalRight, hfinalCache,
        htailReplay⟩ := htailRelation
      have hleftTailLe := treeValues_cache_le parameter left.1 indices
        leftHeadResult.2 leftTailResult hleftTailSupport
      have hrightTailLe := treeValues_cache_le parameter right.1 indices
        rightHeadResult.2 rightTailResult hrightTailSupport
      have hleftCurrentStable :=
        Concrete.CacheReplay.leafAt_oneTimePublicKey_eq_in_largerCache
          parameter left.1 current.node leftCache leftHeadResult.2
            leftTailResult.2 leftHeadResult.1 (by
              simpa [TreeValueIndex.computation, hcurrentZero] using
                hleftHeadSupport) hleftTailLe
      have hrightCurrentStable :=
        Concrete.CacheReplay.leafAt_oneTimePublicKey_eq_in_largerCache
          parameter right.1 current.node rightCache rightHeadResult.2
            rightTailResult.2 rightHeadResult.1 (by
              simpa [TreeValueIndex.computation, hcurrentZero] using
                hrightHeadSupport) hrightTailLe
      obtain ⟨leftOutput, hleftCached⟩ :=
        Concrete.CacheReplay.leafAt_query_cached parameter left.1 current.node
          leftCache leftHeadResult.2 leftHeadResult.1 (by
            simpa [TreeValueIndex.computation, hcurrentZero] using
              hleftHeadSupport)
      have hheadReplay :
          leftHeadResult.2 (Concrete.CacheView.leafInput parameter current.node
            (Concrete.CacheReplay.oneTimePublicKey leftHeadResult.2 parameter
              left.1 current.node)) =
          rightHeadResult.2 (Concrete.CacheView.leafInput parameter current.node
            (Concrete.CacheReplay.oneTimePublicKey rightHeadResult.2 parameter
              right.1 current.node)) := by
        have hleaf := hnextCache.leaves current.node
        rw [Function.update_self, Function.update_self] at hleaf
        calc
          leftHeadResult.2 (Concrete.CacheView.leafInput parameter current.node
              (Concrete.CacheReplay.oneTimePublicKey leftHeadResult.2 parameter
                left.1 current.node)) =
              leftHeadResult.2 (Concrete.CacheView.leafInput parameter
                current.node nextLeft) := by rw [hnextLeft]
          _ = rightHeadResult.2 (Concrete.CacheView.leafInput parameter
                current.node nextRight) := hleaf
          _ = rightHeadResult.2 (Concrete.CacheView.leafInput parameter
              current.node
              (Concrete.CacheReplay.oneTimePublicKey rightHeadResult.2 parameter
                right.1 current.node)) := by rw [hnextRight]
      have hrightCached :
          rightHeadResult.2 (Concrete.CacheView.leafInput parameter current.node
            (Concrete.CacheReplay.oneTimePublicKey rightHeadResult.2 parameter
              right.1 current.node)) = some leftOutput := by
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

end XmssSecurity.CappedChain
