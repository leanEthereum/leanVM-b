import XmssSecurity.CausalSubtreeIndependence
import XmssSecurity.ConcreteCorrectness

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem treeSubtreeValid_pathNode
    (epoch : Epoch) (levels : Nat) (hlevels : levels ≤ treeHeight) :
    TreeSubtreeValid levels
      (Concrete.CacheReplay.pathNode epoch levels) := by
  have hfactor :
      2 ^ (treeHeight - levels) * 2 ^ levels = lifetime := by
    rw [← pow_add, Nat.sub_add_cancel hlevels]
    rfl
  have hquotient : epoch.val / 2 ^ levels < 2 ^ (treeHeight - levels) := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos (by omega) _)]
    rw [hfactor]
    exact epoch.isLt
  have hpath :
      (Concrete.CacheReplay.pathNode epoch levels).val =
        epoch.val / 2 ^ levels := by
    unfold Concrete.CacheReplay.pathNode Concrete.merkleNodeOfNat
    exact Nat.mod_eq_of_lt
      ((Nat.div_le_self epoch.val _).trans_lt epoch.isLt)
  unfold TreeSubtreeValid
  rw [hpath]
  nlinarith

theorem authenticationPathNode_subtreeValid
    (epoch : Epoch) (level : MerkleLevel) :
    TreeSubtreeValid level.val
      (Concrete.authenticationPathNode epoch level) := by
  have hparent : TreeSubtreeValid (level.val + 1)
      (Concrete.CacheReplay.pathNode epoch (level.val + 1)) :=
    treeSubtreeValid_pathNode epoch (level.val + 1) (by omega)
  have hchildren := Concrete.CacheReplay.pathNode_children
    epoch level.val level.isLt
  by_cases hbit : epoch.val.testBit level.val = true
  · rw [if_pos hbit] at hchildren
    have hvalid := childNode_subtreeValid level.val
      (Concrete.CacheReplay.pathNode epoch (level.val + 1)) false hparent
    rw [hchildren.1] at hvalid
    exact hvalid
  · rw [if_neg hbit] at hchildren
    have hvalid := childNode_subtreeValid level.val
      (Concrete.CacheReplay.pathNode epoch (level.val + 1)) true hparent
    rw [hchildren.2] at hvalid
    exact hvalid

def authenticationPathComponentDomain
    (epoch : Epoch) (level : MerkleLevel) : HashDomain :=
  if hzero : level.val = 0 then
    .leaf (Concrete.authenticationPathNode epoch level)
  else
    .merkle ⟨level.val - 1, by omega⟩
      (Concrete.authenticationPathNode epoch level)

def AuthenticationPathComponentsFresh
    (parameter : PublicParameter) (epoch : Epoch)
    (levels : List MerkleLevel) (cache : QueryCache HashSpec) : Prop :=
  ∀ level ∈ levels, ∀ input,
    AtHashAddress parameter (authenticationPathComponentDomain epoch level) input →
      cache input = none

noncomputable def authenticationPathLevels
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) : List MerkleLevel →
      QueryCache HashSpec → ProbComp (List Digest × QueryCache HashSpec)
  | [], cache => pure ([], cache)
  | level :: levels, cache => do
      let head ← (simulateQ randomOracle
        (Concrete.treeNode parameter secret level.val
          (Concrete.authenticationPathNode epoch level) :
            OracleComp HashSpec Digest)).run cache
      let tail ← authenticationPathLevels parameter secret epoch levels head.2
      pure (head.1 :: tail.1, tail.2)

@[simp]
theorem authenticationPathLevels_nil
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (cache : QueryCache HashSpec) :
    authenticationPathLevels parameter secret epoch [] cache =
      pure ([], cache) := rfl

theorem authenticationPathLevels_cons
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (level : MerkleLevel) (levels : List MerkleLevel)
    (cache : QueryCache HashSpec) :
    authenticationPathLevels parameter secret epoch (level :: levels) cache = (do
      let head ← (simulateQ randomOracle
        (Concrete.treeNode parameter secret level.val
          (Concrete.authenticationPathNode epoch level) :
            OracleComp HashSpec Digest)).run cache
      let tail ← authenticationPathLevels parameter secret epoch levels head.2
      pure (head.1 :: tail.1, tail.2)) := rfl

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem authenticationPathComponent_probability_from_cache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (level : MerkleLevel)
    (cache : QueryCache HashSpec)
    (hfresh : ∀ input,
      AtHashAddress parameter
        (authenticationPathComponentDomain epoch level) input →
      cache input = none)
    (target : Digest) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      (simulateQ randomOracle
        (Concrete.treeNode parameter secret level.val
          (Concrete.authenticationPathNode epoch level) :
            OracleComp HashSpec Digest)).run cache] =
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  by_cases hzero : level.val = 0
  · rw [hzero, Concrete.treeNode_zero_eq]
    apply Concrete.leafAt_probability_from_cache
    intro input hinput
    apply hfresh input
    unfold authenticationPathComponentDomain
    rw [dif_pos hzero]
    exact hinput
  · have hsucc : level.val = (level.val - 1) + 1 := by omega
    rw [hsucc]
    apply Concrete.treeNode_positive_probability_from_cache
      (parameter := parameter) (secret := secret) (levels := level.val - 1)
      (node := Concrete.authenticationPathNode epoch level)
      (hlevel := by omega)
      (hvalid := by simpa [← hsucc] using
        authenticationPathNode_subtreeValid epoch level)
      (initialCache := cache)
    intro input hinput
    apply hfresh input
    unfold authenticationPathComponentDomain
    rw [dif_neg hzero]
    exact hinput

set_option maxRecDepth 100000 in
theorem evalDist_authenticationPathComponent_eq_uniform
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (level : MerkleLevel)
    (cache : QueryCache HashSpec)
    (hfresh : ∀ input,
      AtHashAddress parameter
        (authenticationPathComponentDomain epoch level) input →
      cache input = none) :
    𝒟[Prod.fst <$> (simulateQ randomOracle
      (Concrete.treeNode parameter secret level.val
        (Concrete.authenticationPathNode epoch level) :
          OracleComp HashSpec Digest)).run cache] =
      𝒟[$ᵗ Digest] := by
  apply SPMF.ext
  intro target
  change Pr[= target | Prod.fst <$> (simulateQ randomOracle
      (Concrete.treeNode parameter secret level.val
        (Concrete.authenticationPathNode epoch level) :
          OracleComp HashSpec Digest)).run cache] =
    Pr[= target | $ᵗ Digest]
  rw [← probEvent_eq_eq_probOutput, probEvent_map]
  calc
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret level.val
            (Concrete.authenticationPathNode epoch level) :
              OracleComp HashSpec Digest)).run cache] =
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      authenticationPathComponent_probability_from_cache parameter secret epoch
        level cache hfresh target
    _ = Pr[= target | $ᵗ Digest] := by
      rw [probOutput_uniformSample, HiddenValue.card_digest]

theorem authenticationPathComponent_preserves_fresh_higher
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (current target : MerkleLevel)
    (hlt : current.val < target.val)
    (cache : QueryCache HashSpec)
    (result : Digest × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret current.val
          (Concrete.authenticationPathNode epoch current) :
            OracleComp HashSpec Digest)).run cache))
    (input : HashInput)
    (hinput : AtHashAddress parameter
      (authenticationPathComponentDomain epoch target) input)
    (hcache : cache input = none) :
    result.2 input = none := by
  have htarget : target.val ≠ 0 := by omega
  unfold authenticationPathComponentDomain at hinput
  rw [dif_neg htarget] at hinput
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.treeNode parameter secret current.val
      (Concrete.authenticationPathNode epoch current) :
        OracleComp HashSpec Digest)
    input cache result.2 result.1
  · apply OracleComp.IsQueryBoundP.of_imp
      (p' := AtHashAddress parameter
        (.merkle ⟨target.val - 1, by omega⟩
          (Concrete.authenticationPathNode epoch target)))
    · intro candidate heq
      subst candidate
      exact hinput
    · have hbound := Concrete.treeNode_queryBound_merkleAddress
        parameter secret ⟨target.val - 1, by omega⟩
          (Concrete.authenticationPathNode epoch target)
          current.val (Concrete.authenticationPathNode epoch current)
          (by omega) (authenticationPathNode_subtreeValid epoch current)
      have hnot : ¬ MerkleAddressInSubtree
          ⟨target.val - 1, by omega⟩
          (Concrete.authenticationPathNode epoch target)
          current.val (Concrete.authenticationPathNode epoch current) := by
        intro hcontains
        unfold MerkleAddressInSubtree at hcontains
        change target.val - 1 < current.val ∧ _ at hcontains
        omega
      simpa [hnot] using hbound
  · exact hcache
  · exact hresult

theorem authenticationPathComponent_preserves_tail_fresh
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (current : MerkleLevel) (levels : List MerkleLevel)
    (hordered : ∀ target ∈ levels, current.val < target.val)
    (cache : QueryCache HashSpec)
    (hfresh : AuthenticationPathComponentsFresh parameter epoch
      (current :: levels) cache)
    (result : Digest × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret current.val
          (Concrete.authenticationPathNode epoch current) :
            OracleComp HashSpec Digest)).run cache)) :
    AuthenticationPathComponentsFresh parameter epoch levels result.2 := by
  intro target htarget input hinput
  apply authenticationPathComponent_preserves_fresh_higher
    parameter secret epoch current target (hordered target htarget)
      cache result hresult input hinput
  exact hfresh target (by simp [htarget]) input hinput

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_authenticationPathLevels_values_eq_drawList
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) :
    ∀ (levels : List MerkleLevel) (cache : QueryCache HashSpec),
      levels.Pairwise (fun left right => left.val < right.val) →
      AuthenticationPathComponentsFresh parameter epoch levels cache →
      𝒟[Prod.fst <$>
        authenticationPathLevels parameter secret epoch levels cache] =
      𝒟[OracleComp.drawList ($ᵗ Digest) levels.length] := by
  intro levels
  induction levels with
  | nil =>
      intro cache _hordered _hfresh
      simp [OracleComp.drawList]
  | cons current levels ih =>
      intro cache hordered hfresh
      have hcurrentOrdered : ∀ target ∈ levels,
          current.val < target.val := by
        exact (List.pairwise_cons.mp hordered).1
      have htailOrdered : levels.Pairwise
          (fun left right => left.val < right.val) :=
        (List.pairwise_cons.mp hordered).2
      have hcurrentFresh : ∀ input,
          AtHashAddress parameter
            (authenticationPathComponentDomain epoch current) input →
          cache input = none := by
        intro input hinput
        exact hfresh current (by simp) input hinput
      rw [authenticationPathLevels_cons, map_eq_bind_pure_comp]
      simp only [bind_assoc, pure_bind, Function.comp_apply]
      calc
        𝒟[(simulateQ randomOracle
              (Concrete.treeNode parameter secret current.val
                (Concrete.authenticationPathNode epoch current) :
                  OracleComp HashSpec Digest)).run cache >>= fun headResult =>
            authenticationPathLevels parameter secret epoch levels
                headResult.2 >>= fun tailResult =>
              pure (headResult.1 :: tailResult.1)] =
          𝒟[(simulateQ randomOracle
              (Concrete.treeNode parameter secret current.val
                (Concrete.authenticationPathNode epoch current) :
                  OracleComp HashSpec Digest)).run cache >>= fun headResult =>
            OracleComp.drawList ($ᵗ Digest) levels.length >>= fun tail =>
              pure (headResult.1 :: tail)] := by
            apply evalDist_bind_congr
            intro headResult hheadResult
            have htailFresh :=
              authenticationPathComponent_preserves_tail_fresh
                parameter secret epoch current levels hcurrentOrdered cache
                  hfresh headResult hheadResult
            calc
              𝒟[authenticationPathLevels parameter secret epoch levels
                    headResult.2 >>= fun tailResult =>
                  pure (headResult.1 :: tailResult.1)] =
                𝒟[(Prod.fst <$>
                    authenticationPathLevels parameter secret epoch levels
                      headResult.2) >>= fun tail =>
                  pure (headResult.1 :: tail)] := by
                    simp [map_eq_bind_pure_comp, bind_assoc]
              _ = 𝒟[OracleComp.drawList ($ᵗ Digest) levels.length >>= fun tail =>
                    pure (headResult.1 :: tail)] := by
                    rw [evalDist_bind,
                      ih headResult.2 htailOrdered htailFresh,
                      ← evalDist_bind]
        _ = 𝒟[(Prod.fst <$> (simulateQ randomOracle
              (Concrete.treeNode parameter secret current.val
                (Concrete.authenticationPathNode epoch current) :
                  OracleComp HashSpec Digest)).run cache) >>= fun head =>
            OracleComp.drawList ($ᵗ Digest) levels.length >>= fun tail =>
              pure (head :: tail)] := by
            simp [map_eq_bind_pure_comp, bind_assoc]
        _ = 𝒟[($ᵗ Digest) >>= fun head =>
            OracleComp.drawList ($ᵗ Digest) levels.length >>= fun tail =>
              pure (head :: tail)] := by
            rw [evalDist_bind,
              evalDist_authenticationPathComponent_eq_uniform
                parameter secret epoch current cache hcurrentFresh,
              ← evalDist_bind]
        _ = 𝒟[OracleComp.drawList ($ᵗ Digest)
            (current :: levels).length] := by
            rfl

def allMerkleLevels : List MerkleLevel :=
  List.ofFn id

@[simp]
theorem allMerkleLevels_length : allMerkleLevels.length = treeHeight := by
  simp [allMerkleLevels]

theorem allMerkleLevels_pairwise :
    allMerkleLevels.Pairwise (fun left right => left.val < right.val) := by
  rw [allMerkleLevels, List.pairwise_ofFn]
  intro left right hlt
  exact hlt

theorem programmedWarmedTrajectory_authenticationPath_fresh
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (htrajectory : trajectoryResult ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (epoch : Epoch) :
    AuthenticationPathComponentsFresh parameter epoch allMerkleLevels
      trajectoryResult.2 := by
  intro level _hlevel input hinput
  by_cases hzero : level.val = 0
  · unfold authenticationPathComponentDomain at hinput
    rw [dif_pos hzero] at hinput
    exact programmedFixedSeedChainTrajectories_avoids_leaf
      parameter secret chain trajectoryResult htrajectory
        (Concrete.authenticationPathNode epoch level) input hinput
  · unfold authenticationPathComponentDomain at hinput
    rw [dif_neg hzero] at hinput
    exact programmedFixedSeedChainTrajectories_avoids_merkle
      parameter secret chain trajectoryResult htrajectory
        ⟨level.val - 1, by omega⟩
        (Concrete.authenticationPathNode epoch level) input hinput

set_option maxRecDepth 1000000 in
theorem evalDist_programmedWarmedAuthenticationPathValues_eq_drawList
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (htrajectory : trajectoryResult ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (epoch : Epoch) :
    𝒟[Prod.fst <$> authenticationPathLevels parameter secret epoch
      allMerkleLevels trajectoryResult.2] =
      𝒟[OracleComp.drawList ($ᵗ Digest) treeHeight] := by
  rw [← allMerkleLevels_length]
  exact evalDist_authenticationPathLevels_values_eq_drawList
    parameter secret epoch allMerkleLevels trajectoryResult.2
      allMerkleLevels_pairwise
      (programmedWarmedTrajectory_authenticationPath_fresh
        parameter secret chain trajectoryResult htrajectory epoch)

theorem treeNode_preserves_root_fresh
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) (hlevels : levels < treeHeight)
    (hvalid : TreeSubtreeValid levels node)
    (cache : QueryCache HashSpec)
    (result : Digest × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret levels node :
          OracleComp HashSpec Digest)).run cache))
    (input : HashInput)
    (hinput : AtHashAddress parameter
      (.merkle ⟨treeHeight - 1, by decide⟩ Concrete.rootNode) input)
    (hcache : cache input = none) :
    result.2 input = none := by
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest)
    input cache result.2 result.1
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
  · exact hcache
  · exact hresult

theorem authenticationPathLevels_preserves_root_fresh
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) :
    ∀ (levels : List MerkleLevel) (cache : QueryCache HashSpec)
      (result : List Digest × QueryCache HashSpec)
      (_hresult : result ∈ support
        (authenticationPathLevels parameter secret epoch levels cache))
      (input : HashInput),
      AtHashAddress parameter
        (.merkle ⟨treeHeight - 1, by decide⟩ Concrete.rootNode) input →
      cache input = none → result.2 input = none := by
  intro levels
  induction levels with
  | nil =>
      intro cache result hresult input _hinput hcache
      simp only [authenticationPathLevels_nil, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact hcache
  | cons level levels ih =>
      intro cache result hresult input hinput hcache
      rw [authenticationPathLevels_cons, mem_support_bind_iff] at hresult
      obtain ⟨headResult, hheadResult, htail⟩ := hresult
      rw [mem_support_bind_iff] at htail
      obtain ⟨tailResult, htailResult, hpure⟩ := htail
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      apply ih headResult.2 tailResult htailResult input hinput
      exact treeNode_preserves_root_fresh parameter secret level.val
        (Concrete.authenticationPathNode epoch level) level.isLt
          (authenticationPathNode_subtreeValid epoch level) cache headResult
            hheadResult input hinput hcache

theorem programmedWarmedAuthenticationPath_root_probability
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (htrajectory : trajectoryResult ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (epoch : Epoch)
    (pathResult : List Digest × QueryCache HashSpec)
    (hpath : pathResult ∈ support
      (authenticationPathLevels parameter secret epoch allMerkleLevels
        trajectoryResult.2))
    (target : Digest) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      (simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run pathResult.2] =
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
    (initialCache := pathResult.2)
  intro input hinput
  apply authenticationPathLevels_preserves_root_fresh parameter secret epoch
    allMerkleLevels trajectoryResult.2 pathResult hpath input hinput
  exact programmedFixedSeedChainTrajectories_avoids_merkle
    parameter secret chain trajectoryResult htrajectory
      ⟨treeHeight - 1, by decide⟩ Concrete.rootNode input hinput

set_option maxRecDepth 100000 in
theorem evalDist_programmedWarmedAuthenticationPath_root_eq_uniform
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (htrajectory : trajectoryResult ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (epoch : Epoch)
    (pathResult : List Digest × QueryCache HashSpec)
    (hpath : pathResult ∈ support
      (authenticationPathLevels parameter secret epoch allMerkleLevels
        trajectoryResult.2)) :
    𝒟[Prod.fst <$> (simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run pathResult.2] =
      𝒟[$ᵗ Digest] := by
  apply SPMF.ext
  intro target
  change Pr[= target | Prod.fst <$> (simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run pathResult.2] =
    Pr[= target | $ᵗ Digest]
  rw [← probEvent_eq_eq_probOutput, probEvent_map]
  calc
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run pathResult.2] =
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      programmedWarmedAuthenticationPath_root_probability parameter secret chain
        trajectoryResult htrajectory epoch pathResult hpath target
    _ = Pr[= target | $ᵗ Digest] := by
      rw [probOutput_uniformSample, HiddenValue.card_digest]

noncomputable def programmedWarmedAuthenticationPathRootPair
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (epoch : Epoch) : ProbComp (List Digest × Digest) := do
  let pathResult ← authenticationPathLevels parameter secret epoch
    allMerkleLevels trajectoryResult.2
  let rootResult ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)).run pathResult.2
  pure (pathResult.1, rootResult.1)

noncomputable def independentAuthenticationPathRootPair :
    ProbComp (List Digest × Digest) := do
  let path ← OracleComp.drawList ($ᵗ Digest) treeHeight
  let root ← $ᵗ Digest
  pure (path, root)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_programmedWarmedAuthenticationPathRootPair_eq_independent
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (htrajectory : trajectoryResult ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (epoch : Epoch) :
    𝒟[programmedWarmedAuthenticationPathRootPair parameter secret
      trajectoryResult epoch] =
      𝒟[independentAuthenticationPathRootPair] := by
  unfold programmedWarmedAuthenticationPathRootPair
    independentAuthenticationPathRootPair
  calc
    𝒟[authenticationPathLevels parameter secret epoch allMerkleLevels
          trajectoryResult.2 >>= fun pathResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run pathResult.2 >>= fun rootResult =>
        pure (pathResult.1, rootResult.1)] =
      𝒟[authenticationPathLevels parameter secret epoch allMerkleLevels
          trajectoryResult.2 >>= fun pathResult =>
        ($ᵗ Digest) >>= fun root => pure (pathResult.1, root)] := by
      apply evalDist_bind_congr
      intro pathResult hpath
      calc
        𝒟[(simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run pathResult.2 >>= fun rootResult =>
            pure (pathResult.1, rootResult.1)] =
          𝒟[(Prod.fst <$> (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run pathResult.2) >>= fun root =>
            pure (pathResult.1, root)] := by
            simp [map_eq_bind_pure_comp, bind_assoc]
        _ = 𝒟[($ᵗ Digest) >>= fun root => pure (pathResult.1, root)] := by
            rw [evalDist_bind,
              evalDist_programmedWarmedAuthenticationPath_root_eq_uniform
                parameter secret chain trajectoryResult htrajectory epoch
                  pathResult hpath,
              ← evalDist_bind]
    _ = 𝒟[(Prod.fst <$> authenticationPathLevels parameter secret epoch
          allMerkleLevels trajectoryResult.2) >>= fun path =>
        ($ᵗ Digest) >>= fun root => pure (path, root)] := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = 𝒟[OracleComp.drawList ($ᵗ Digest) treeHeight >>= fun path =>
        ($ᵗ Digest) >>= fun root => pure (path, root)] := by
      rw [evalDist_bind,
        evalDist_programmedWarmedAuthenticationPathValues_eq_drawList
          parameter secret chain trajectoryResult htrajectory epoch,
        ← evalDist_bind]

noncomputable def programmedWarmedAuthenticationPathPublicTableView
    (chain : ChainIndex) (epoch : Epoch) :
    ProbComp (PublicKey × (List Digest × (ChainValueIndex → Digest))) := do
  let parameter ← Concrete.samplePublicParameter
  let material ← programmedWarmedTrajectoryMaterial parameter chain
  let pathRoot ← programmedWarmedAuthenticationPathRootPair parameter
    (unflattenSecret material.1.2) material.2 epoch
  pure (⟨pathRoot.2, parameter⟩,
    (pathRoot.1, chainValueTableOfList material.2.1))

noncomputable def independentAuthenticationPathPublicTableView
    (chain : ChainIndex) :
    ProbComp (PublicKey × (List Digest × (ChainValueIndex → Digest))) := do
  let parameter ← Concrete.samplePublicParameter
  let pathRoot ← independentAuthenticationPathRootPair
  let table ← uniformChainValueTable chain
  pure (⟨pathRoot.2, parameter⟩, (pathRoot.1, table))

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_programmedWarmedAuthenticationPathPublicTableView_eq_independent
    (chain : ChainIndex) (epoch : Epoch) :
    𝒟[programmedWarmedAuthenticationPathPublicTableView chain epoch] =
      𝒟[independentAuthenticationPathPublicTableView chain] := by
  unfold programmedWarmedAuthenticationPathPublicTableView
    independentAuthenticationPathPublicTableView
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  calc
    𝒟[programmedWarmedTrajectoryMaterial parameter chain >>= fun material =>
        programmedWarmedAuthenticationPathRootPair parameter
          (unflattenSecret material.1.2) material.2 epoch >>= fun pathRoot =>
        pure ((⟨pathRoot.2, parameter⟩ : PublicKey),
          (pathRoot.1, chainValueTableOfList material.2.1))] =
      𝒟[programmedWarmedTrajectoryMaterial parameter chain >>= fun material =>
        independentAuthenticationPathRootPair >>= fun pathRoot =>
        pure ((⟨pathRoot.2, parameter⟩ : PublicKey),
          (pathRoot.1, chainValueTableOfList material.2.1))] := by
      apply evalDist_bind_congr
      intro material hmaterial
      have htrajectory :=
        programmedWarmedTrajectoryMaterial_support_trajectory parameter chain
          material hmaterial
      let finish : (List Digest × Digest) →
          ProbComp (PublicKey × (List Digest ×
            (ChainValueIndex → Digest))) := fun pathRoot =>
        pure (⟨pathRoot.2, parameter⟩,
          (pathRoot.1, chainValueTableOfList material.2.1))
      change 𝒟[programmedWarmedAuthenticationPathRootPair parameter
          (unflattenSecret material.1.2) material.2 epoch >>= finish] =
        𝒟[independentAuthenticationPathRootPair >>= finish]
      rw [evalDist_bind,
        evalDist_programmedWarmedAuthenticationPathRootPair_eq_independent
          parameter (unflattenSecret material.1.2) chain material.2
            htrajectory epoch,
        ← evalDist_bind]
    _ = 𝒟[independentAuthenticationPathRootPair >>= fun pathRoot =>
          programmedWarmedTrajectoryMaterial parameter chain >>= fun material =>
          pure ((⟨pathRoot.2, parameter⟩ : PublicKey),
            (pathRoot.1, chainValueTableOfList material.2.1))] :=
      OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[independentAuthenticationPathRootPair >>= fun pathRoot =>
          programmedWarmedTrajectoryTableOnly parameter chain >>= fun table =>
          pure ((⟨pathRoot.2, parameter⟩ : PublicKey),
            (pathRoot.1, table))] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro pathRoot
      simp [programmedWarmedTrajectoryTableOnly,
        map_eq_bind_pure_comp, bind_assoc]
    _ = 𝒟[independentAuthenticationPathRootPair >>= fun pathRoot =>
          uniformChainValueTable chain >>= fun table =>
          pure ((⟨pathRoot.2, parameter⟩ : PublicKey),
            (pathRoot.1, table))] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro pathRoot
      let finish : (ChainValueIndex → Digest) →
          ProbComp (PublicKey × (List Digest ×
            (ChainValueIndex → Digest))) := fun table =>
        pure (⟨pathRoot.2, parameter⟩, (pathRoot.1, table))
      change 𝒟[programmedWarmedTrajectoryTableOnly parameter chain >>= finish] =
        𝒟[uniformChainValueTable chain >>= finish]
      rw [evalDist_bind,
        evalDist_programmedWarmedTrajectoryTableOnly_eq_uniformChainValueTable
          parameter chain,
        ← evalDist_bind]

end XmssSecurity
