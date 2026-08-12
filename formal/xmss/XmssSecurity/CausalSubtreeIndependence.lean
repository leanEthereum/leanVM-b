import XmssSecurity.CausalKeygenTableIndependence

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

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

theorem programmedFixedSeedChainTrajectories_avoids_leaf
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (result : List FullChainTrajectory × QueryCache HashSpec)
    (hresult : result ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (targetEpoch : Epoch) (input : HashInput)
    (hinput : AtHashAddress parameter (.leaf targetEpoch) input) :
    result.2 input = none := by
  have hdist := evalDist_fixedSeedChainTrajectories_eq_programmed
    parameter secret chain (chainLength - 1) le_rfl allEpochs ∅
      allEpochs_nodup (by simp)
  have hactual : result ∈ support
      (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs) :=
    (mem_support_iff_of_evalDist_eq hdist result).mpr hresult
  exact Concrete.fixedSeedChainTrajectoriesFromCache_avoids_leaf
    parameter secret chain (chainLength - 1) targetEpoch input hinput
      allEpochs ∅ result (by simp) hactual

theorem Concrete.leafAt_probability_from_cache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (initialCache : QueryCache HashSpec)
    (habsent : ∀ input,
      AtHashAddress parameter (.leaf epoch) input →
        initialCache input = none)
    (target : Digest) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      (simulateQ randomOracle
        (Concrete.leafAt parameter secret epoch :
          OracleComp HashSpec Digest)).run initialCache] =
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  rw [Concrete.leafAt, simulateQ_bind, StateT.run_bind,
    probEvent_bind_eq_tsum]
  have hconditional : ∀ endpointsResult ∈ support
      ((simulateQ randomOracle
        (Concrete.oneTimePublicKey parameter secret epoch)).run initialCache),
      Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
        (simulateQ randomOracle
          (Concrete.leafHash parameter epoch endpointsResult.1 :
            OracleComp HashSpec Digest)).run endpointsResult.2] =
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
    intro endpointsResult hendpoints
    apply Concrete.tweakableHash_fresh_probability
    apply Concrete.CacheReplay.cache_none_of_zero_query_bound
      (Concrete.oneTimePublicKey parameter secret epoch)
      (Concrete.CacheView.leafInput parameter epoch endpointsResult.1)
      initialCache endpointsResult.2 endpointsResult.1
    · apply OracleComp.IsQueryBoundP.of_imp
        (p' := AtHashAddress parameter (.leaf epoch))
      · intro input heq
        subst input
        exact (atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl
      · exact Concrete.oneTimePublicKey_queryBound_zero_leafAddress
          parameter secret epoch epoch
    · exact habsent _
        ((atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl)
    · exact hendpoints
  calc
    ∑' endpointsResult,
        Pr[= endpointsResult |
          (simulateQ randomOracle
            (Concrete.oneTimePublicKey parameter secret epoch)).run initialCache] *
          Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
            (simulateQ randomOracle
              (Concrete.leafHash parameter epoch endpointsResult.1 :
                OracleComp HashSpec Digest)).run endpointsResult.2] =
      ∑' endpointsResult,
        Pr[= endpointsResult |
          (simulateQ randomOracle
            (Concrete.oneTimePublicKey parameter secret epoch)).run initialCache] *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      apply tsum_congr
      intro endpointsResult
      by_cases hendpoints : endpointsResult ∈ support
          ((simulateQ randomOracle
            (Concrete.oneTimePublicKey parameter secret epoch)).run initialCache)
      · rw [hconditional endpointsResult hendpoints]
      · rw [probOutput_eq_zero_of_not_mem_support hendpoints, zero_mul, zero_mul]
    _ = (∑' endpointsResult,
        Pr[= endpointsResult |
          (simulateQ randomOracle
            (Concrete.oneTimePublicKey parameter secret epoch)).run initialCache]) *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      ENNReal.tsum_mul_right
    _ = ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      rw [tsum_probOutput_eq_one']
      · exact one_mul _
      · exact probFailure_eq_zero'
          (neverFail_simulateQ_randomOracle_run
            (Concrete.oneTimePublicKey parameter secret epoch) initialCache)

theorem programmedWarmedTrajectory_treeNode_probability
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (htrajectory : trajectoryResult ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (levels : Nat) (node : MerkleNode) (hlevels : levels < treeHeight)
    (hvalid : TreeSubtreeValid levels node) (target : Digest) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      (simulateQ randomOracle
        (Concrete.treeNode parameter secret levels node :
          OracleComp HashSpec Digest)).run trajectoryResult.2] =
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  cases levels with
  | zero =>
      rw [Concrete.treeNode_zero_eq]
      apply Concrete.leafAt_probability_from_cache
      intro input hinput
      exact programmedFixedSeedChainTrajectories_avoids_leaf
        parameter secret chain trajectoryResult htrajectory node input hinput
  | succ levels =>
      have hlevel : levels < treeHeight := by omega
      apply Concrete.treeNode_positive_probability_from_cache
        (parameter := parameter) (secret := secret) (levels := levels)
        (node := node) (hlevel := hlevel) (hvalid := hvalid)
        (initialCache := trajectoryResult.2)
      intro input hinput
      exact programmedFixedSeedChainTrajectories_avoids_merkle
        parameter secret chain trajectoryResult htrajectory
          ⟨levels, hlevel⟩ node input hinput

set_option maxRecDepth 100000 in
theorem evalDist_programmedWarmedTrajectory_treeNode_eq_uniform
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (htrajectory : trajectoryResult ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (levels : Nat) (node : MerkleNode) (hlevels : levels < treeHeight)
    (hvalid : TreeSubtreeValid levels node) :
    𝒟[Prod.fst <$> (simulateQ randomOracle
      (Concrete.treeNode parameter secret levels node :
        OracleComp HashSpec Digest)).run trajectoryResult.2] =
      𝒟[$ᵗ Digest] := by
  apply SPMF.ext
  intro target
  change Pr[= target | Prod.fst <$> (simulateQ randomOracle
      (Concrete.treeNode parameter secret levels node :
        OracleComp HashSpec Digest)).run trajectoryResult.2] =
    Pr[= target | $ᵗ Digest]
  rw [← probEvent_eq_eq_probOutput, probEvent_map]
  calc
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret levels node :
            OracleComp HashSpec Digest)).run trajectoryResult.2] =
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      programmedWarmedTrajectory_treeNode_probability parameter secret chain
        trajectoryResult htrajectory levels node hlevels hvalid target
    _ = Pr[= target | $ᵗ Digest] := by
      rw [probOutput_uniformSample, HiddenValue.card_digest]

theorem programmedWarmedTrajectory_subtree_avoids_root
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (htrajectory : trajectoryResult ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (levels : Nat) (node : MerkleNode) (hlevels : levels < treeHeight)
    (hvalid : TreeSubtreeValid levels node)
    (subtreeResult : Digest × QueryCache HashSpec)
    (hsubtree : subtreeResult ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret levels node :
          OracleComp HashSpec Digest)).run trajectoryResult.2))
    (input : HashInput)
    (hinput : AtHashAddress parameter
      (.merkle ⟨treeHeight - 1, by decide⟩ Concrete.rootNode) input) :
    subtreeResult.2 input = none := by
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest)
    input trajectoryResult.2 subtreeResult.2 subtreeResult.1
  · apply OracleComp.IsQueryBoundP.of_imp
      (p' := AtHashAddress parameter
        (.merkle ⟨treeHeight - 1, by decide⟩ Concrete.rootNode))
    · intro candidate heq
      subst candidate
      exact hinput
    · have hbound := Concrete.treeNode_queryBound_merkleAddress
        parameter secret ⟨treeHeight - 1, by decide⟩ Concrete.rootNode
          levels node (Nat.le_of_lt hlevels) hvalid
      have hnot : ¬ MerkleAddressInSubtree
          ⟨treeHeight - 1, by decide⟩ Concrete.rootNode levels node := by
        intro hcontains
        unfold MerkleAddressInSubtree at hcontains
        change treeHeight - 1 < levels ∧ _ at hcontains
        omega
      simpa [hnot] using hbound
  · exact programmedFixedSeedChainTrajectories_avoids_merkle
      parameter secret chain trajectoryResult htrajectory
        ⟨treeHeight - 1, by decide⟩ Concrete.rootNode input hinput
  · exact hsubtree

theorem programmedWarmedTrajectory_root_after_subtree_probability
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (htrajectory : trajectoryResult ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (levels : Nat) (node : MerkleNode) (hlevels : levels < treeHeight)
    (hvalid : TreeSubtreeValid levels node)
    (subtreeResult : Digest × QueryCache HashSpec)
    (hsubtree : subtreeResult ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret levels node :
          OracleComp HashSpec Digest)).run trajectoryResult.2))
    (target : Digest) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      (simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run subtreeResult.2] =
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  have hheight : treeHeight = (treeHeight - 1) + 1 := by decide
  rw [hheight]
  apply Concrete.treeNode_positive_probability_from_cache
    (parameter := parameter) (secret := secret) (levels := treeHeight - 1)
    (node := Concrete.rootNode) (hlevel := by decide)
    (hvalid := by
      unfold TreeSubtreeValid Concrete.rootNode lifetime
      change (0 + 1) * 2 ^ (treeHeight - 1 + 1) ≤ 2 ^ treeHeight
      rw [← hheight]
      simp)
    (initialCache := subtreeResult.2)
  intro input hinput
  exact programmedWarmedTrajectory_subtree_avoids_root parameter secret chain
    trajectoryResult htrajectory levels node hlevels hvalid subtreeResult
      hsubtree input hinput

set_option maxRecDepth 100000 in
theorem evalDist_programmedWarmedTrajectory_root_after_subtree_eq_uniform
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (htrajectory : trajectoryResult ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (levels : Nat) (node : MerkleNode) (hlevels : levels < treeHeight)
    (hvalid : TreeSubtreeValid levels node)
    (subtreeResult : Digest × QueryCache HashSpec)
    (hsubtree : subtreeResult ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret levels node :
          OracleComp HashSpec Digest)).run trajectoryResult.2)) :
    𝒟[Prod.fst <$> (simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run subtreeResult.2] =
      𝒟[$ᵗ Digest] := by
  apply SPMF.ext
  intro target
  change Pr[= target | Prod.fst <$> (simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run subtreeResult.2] =
    Pr[= target | $ᵗ Digest]
  rw [← probEvent_eq_eq_probOutput, probEvent_map]
  calc
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run subtreeResult.2] =
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      programmedWarmedTrajectory_root_after_subtree_probability parameter secret
        chain trajectoryResult htrajectory levels node hlevels hvalid
          subtreeResult hsubtree target
    _ = Pr[= target | $ᵗ Digest] := by
      rw [probOutput_uniformSample, HiddenValue.card_digest]

noncomputable def programmedWarmedTrajectorySubtreeRootPair
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (levels : Nat) (node : MerkleNode) : ProbComp (Digest × Digest) := do
  let subtreeResult ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest)).run trajectoryResult.2
  let rootResult ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)).run subtreeResult.2
  pure (subtreeResult.1, rootResult.1)

noncomputable def independentDigestPair : ProbComp (Digest × Digest) := do
  let left ← $ᵗ Digest
  let right ← $ᵗ Digest
  pure (left, right)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_programmedWarmedTrajectorySubtreeRootPair_eq_independent
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (htrajectory : trajectoryResult ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (levels : Nat) (node : MerkleNode) (hlevels : levels < treeHeight)
    (hvalid : TreeSubtreeValid levels node) :
    𝒟[programmedWarmedTrajectorySubtreeRootPair parameter secret
      trajectoryResult levels node] =
      𝒟[independentDigestPair] := by
  unfold programmedWarmedTrajectorySubtreeRootPair independentDigestPair
  calc
    𝒟[(simulateQ randomOracle
          (Concrete.treeNode parameter secret levels node :
            OracleComp HashSpec Digest)).run trajectoryResult.2 >>=
        fun subtreeResult =>
      (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run subtreeResult.2 >>=
        fun rootResult => pure (subtreeResult.1, rootResult.1)] =
      𝒟[(simulateQ randomOracle
          (Concrete.treeNode parameter secret levels node :
            OracleComp HashSpec Digest)).run trajectoryResult.2 >>=
        fun subtreeResult =>
      ($ᵗ Digest) >>= fun root => pure (subtreeResult.1, root)] := by
      apply evalDist_bind_congr
      intro subtreeResult hsubtree
      calc
        𝒟[(simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run subtreeResult.2 >>=
            fun rootResult => pure (subtreeResult.1, rootResult.1)] =
          𝒟[(Prod.fst <$> (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run subtreeResult.2) >>=
            fun root => pure (subtreeResult.1, root)] := by
            simp [map_eq_bind_pure_comp, bind_assoc]
        _ = 𝒟[($ᵗ Digest) >>= fun root =>
              pure (subtreeResult.1, root)] := by
            rw [evalDist_bind,
              evalDist_programmedWarmedTrajectory_root_after_subtree_eq_uniform
                parameter secret chain trajectoryResult htrajectory levels node
                  hlevels hvalid subtreeResult hsubtree,
              ← evalDist_bind]
    _ = 𝒟[($ᵗ Digest) >>= fun root =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret levels node :
              OracleComp HashSpec Digest)).run trajectoryResult.2 >>=
            fun subtreeResult => pure (subtreeResult.1, root)] :=
      OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[($ᵗ Digest) >>= fun root =>
          ($ᵗ Digest) >>= fun subtree => pure (subtree, root)] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro root
      calc
        𝒟[(simulateQ randomOracle
              (Concrete.treeNode parameter secret levels node :
                OracleComp HashSpec Digest)).run trajectoryResult.2 >>=
            fun subtreeResult => pure (subtreeResult.1, root)] =
          𝒟[(Prod.fst <$> (simulateQ randomOracle
              (Concrete.treeNode parameter secret levels node :
                OracleComp HashSpec Digest)).run trajectoryResult.2) >>=
            fun subtree => pure (subtree, root)] := by
            simp [map_eq_bind_pure_comp, bind_assoc]
        _ = 𝒟[($ᵗ Digest) >>= fun subtree => pure (subtree, root)] := by
            rw [evalDist_bind,
              evalDist_programmedWarmedTrajectory_treeNode_eq_uniform
                parameter secret chain trajectoryResult htrajectory levels node
                  hlevels hvalid,
              ← evalDist_bind]
    _ = 𝒟[($ᵗ Digest) >>= fun subtree =>
          ($ᵗ Digest) >>= fun root => pure (subtree, root)] :=
      OracleComp.DeferredSampling.evalDist_bind_comm _ _ _

end XmssSecurity
