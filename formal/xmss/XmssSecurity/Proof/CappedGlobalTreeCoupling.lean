import XmssSecurity.Proof.CappedGlobalChainKeygenCoupling
import XmssSecurity.Proof.CausalTreeTableIndependence

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

abbrev GlobalChainTrajectoryMaterial :=
  (Epoch → ChainIndex → Digest) ×
    (AllChainTrajectories × QueryCache HashSpec)

noncomputable def globalChainTrajectoryMaterialTable
    (material : GlobalChainTrajectoryMaterial) :
    GlobalChainValueIndex → Digest :=
  globalChainValueTableOfTrajectories material.2.1

noncomputable def programmedGlobalChainTrajectoryMaterial
    (parameter : PublicParameter) : ProbComp GlobalChainTrajectoryMaterial := do
  let secret ← Concrete.sampleSecret
  let trajectories ← programmedAllChainTrajectoriesFromCache parameter
    secret ∅ allChains
  pure (secret, trajectories)

noncomputable def programmedGlobalChainTrajectoryMaterialWithBase
    (parameter : PublicParameter) :
    ProbComp (GlobalChainTrajectoryMaterial ×
      (GlobalChainValueIndex → Digest)) := do
  let base ← $ᵗ (GlobalChainValueIndex → Digest)
  let material ← programmedGlobalChainTrajectoryMaterial parameter
  pure (material, base)

theorem programmedGlobalChainTrajectoryMaterial_support_trajectories
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter)) :
    material.2 ∈ support
      (programmedAllChainTrajectoriesFromCache parameter material.1 ∅
        allChains) := by
  unfold programmedGlobalChainTrajectoryMaterial at hmaterial
  rw [mem_support_bind_iff] at hmaterial
  obtain ⟨secret, _hsecret, htrajectories⟩ := hmaterial
  rw [mem_support_bind_iff] at htrajectories
  obtain ⟨trajectories, htrajectories, hpure⟩ := htrajectories
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst material
  exact htrajectories

theorem evalDist_programmedGlobalChainTrajectoryMaterial_table_eq_uniform
    (parameter : PublicParameter) :
    evalDist (globalChainTrajectoryMaterialTable <$>
      programmedGlobalChainTrajectoryMaterial parameter) =
      evalDist ($ᵗ (GlobalChainValueIndex → Digest)) := by
  unfold programmedGlobalChainTrajectoryMaterial
    globalChainTrajectoryMaterialTable
  simp only [map_eq_bind_pure_comp, bind_assoc]
  calc
    _ = evalDist (Concrete.sampleSecret >>= fun secret =>
          globalChainValueTableOfTrajectories <$>
            (Prod.fst <$> programmedAllChainTrajectoriesFromCache parameter
              secret ∅ allChains)) := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro secret
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (Concrete.sampleSecret >>= fun secret =>
          globalChainValueTableOfTrajectories <$>
            uniformAllChainTrajectories secret allChains) := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro secret
      rw [evalDist_map,
        evalDist_programmedAllChainTrajectories_fst_eq_uniform parameter
          secret allChains ∅,
        ← evalDist_map]
    _ = evalDist uniformGlobalChainTableFromTrajectories := rfl
    _ = evalDist ($ᵗ (GlobalChainValueIndex → Digest)) :=
      evalDist_uniformGlobalChainTableFromTrajectories_eq_uniform

def globalChainTrajectoryMaterialBase
    (result : GlobalChainTrajectoryMaterial ×
      (GlobalChainValueIndex → Digest)) :
    GlobalChainValueIndex → Digest := result.2

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
set_option linter.constructorNameAsVariable false in
theorem evalDist_programmedGlobalChainTrajectoryMaterial_table_eq_base
    (parameter : PublicParameter) :
    evalDist (globalChainTrajectoryMaterialTable <$>
        programmedGlobalChainTrajectoryMaterial parameter) =
      evalDist (globalChainTrajectoryMaterialBase <$>
        programmedGlobalChainTrajectoryMaterialWithBase parameter) := by
  calc
    _ = evalDist ($ᵗ (GlobalChainValueIndex → Digest)) :=
      evalDist_programmedGlobalChainTrajectoryMaterial_table_eq_uniform
        parameter
    _ = evalDist (globalChainTrajectoryMaterialBase <$>
        programmedGlobalChainTrajectoryMaterialWithBase parameter) := by
      unfold programmedGlobalChainTrajectoryMaterialWithBase
        globalChainTrajectoryMaterialBase
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
      symm
      calc
        _ = evalDist ($ᵗ (GlobalChainValueIndex → Digest) >>= fun base =>
              pure base) := by
          apply evalDist_bind_congr
          intro base _hbase
          exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
            (programmedGlobalChainTrajectoryMaterial parameter)
            (probFailure_eq_zero' inferInstance) (pure base)
        _ = _ := by simp

structure CoupledGlobalChainKeygenView where
  secret : Epoch → ChainIndex → Digest
  table : GlobalChainValueIndex → Digest
  values : List Digest
  cache : QueryCache HashSpec

def CoupledGlobalChainKeygenView.root
    (parameter : PublicParameter) (view : CoupledGlobalChainKeygenView) :
    Digest :=
  Concrete.CacheReplay.treeNode view.cache parameter view.secret
    treeHeight Concrete.rootNode

def CoupledGlobalChainKeygenView.authenticationPath
    (parameter : PublicParameter) (view : CoupledGlobalChainKeygenView)
    (epoch : Epoch) : MerkleLevel → Digest :=
  Concrete.CacheReplay.authenticationPath view.cache
    (SecretKey.withoutPrecomputation parameter view.secret) epoch

noncomputable def coupledGlobalChainKeygenExperiment
    (parameter : PublicParameter) : ProbComp CoupledGlobalChainKeygenView := do
  let material ← programmedGlobalChainTrajectoryMaterial parameter
  let tree ← treeValues parameter material.1 allTreeValueIndices
    material.2.2
  pure {
    secret := material.1
    table := globalChainTrajectoryMaterialTable material
    values := tree.1
    cache := tree.2
  }

def CoupledGlobalChainKeygenRelation
    (parameter : PublicParameter)
    (left : CoupledGlobalChainKeygenView)
    (right : CoupledGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  left.table = right.2 ∧
    left.root parameter = right.1.root parameter ∧
    (∀ epoch,
      left.authenticationPath parameter epoch =
        right.1.authenticationPath parameter epoch) ∧
    left.values = right.1.values ∧
    TreeValuesReplay parameter left.secret left.cache
      allTreeValueIndices left.values ∧
    TreeValuesReplay parameter right.1.secret right.1.cache
      allTreeValueIndices right.1.values

theorem programmedGlobalChainTrajectoryMaterial_table_eq_keygenTable
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (tree : List Digest × QueryCache HashSpec)
    (htree : tree ∈ support
      (treeValues parameter material.1 allTreeValueIndices material.2.2)) :
    globalChainTrajectoryMaterialTable material =
      globalKeygenChainValueTable tree.2
        (SecretKey.withoutPrecomputation parameter material.1) := by
  have hprogrammed :=
    programmedGlobalChainTrajectoryMaterial_support_trajectories parameter
      material hmaterial
  have hactual : material.2 ∈ support
      (Concrete.allChainTrajectoriesFromCache parameter material.1 ∅
        allChains) := by
    apply (mem_support_iff_of_evalDist_eq
      (evalDist_allChainTrajectories_eq_programmed parameter material.1
        allChains ∅ allChains_nodup
          (by simp [AllChainAddressesAbsent])) material.2).mpr
    exact hprogrammed
  exact Concrete.allChainTrajectoriesFromCache_globalTable_eq parameter
    material.1 material.2 tree.2 hactual
      (treeValues_cache_le parameter material.1 allTreeValueIndices
        material.2.2 tree htree)

def CoupledGlobalChainKeygenView.toProgrammedView
    (parameter : PublicParameter) (view : CoupledGlobalChainKeygenView) :
    ProgrammedGlobalChainKeygenView := {
  publicKey := ⟨view.root parameter, parameter⟩
  secretKey := SecretKey.withoutPrecomputation parameter view.secret
  cache := view.cache
  table := view.table
}

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_coupledGlobalChainKeygen_toProgrammedView_eq
    (parameter : PublicParameter) :
    evalDist (CoupledGlobalChainKeygenView.toProgrammedView parameter <$>
      coupledGlobalChainKeygenExperiment parameter) =
    evalDist (programmedGlobalChainTrajectoryMaterial parameter >>=
      fun material =>
      (simulateQ randomOracle
        (Concrete.treeNode parameter material.1 treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run material.2.2 >>= fun rootResult =>
      pure ({
        publicKey := ⟨rootResult.1, parameter⟩
        secretKey := SecretKey.withoutPrecomputation parameter material.1
        cache := rootResult.2
        table := globalKeygenChainValueTable rootResult.2
          (SecretKey.withoutPrecomputation parameter material.1)
      } : ProgrammedGlobalChainKeygenView)) := by
  unfold coupledGlobalChainKeygenExperiment
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply evalDist_bind_congr
  intro material hmaterial
  let finish : Digest × QueryCache HashSpec →
      ProbComp ProgrammedGlobalChainKeygenView := fun rootResult => pure {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey := SecretKey.withoutPrecomputation parameter material.1
    cache := rootResult.2
    table := globalKeygenChainValueTable rootResult.2
      (SecretKey.withoutPrecomputation parameter material.1)
  }
  symm
  calc
    evalDist ((simulateQ randomOracle
          (Concrete.treeNode parameter material.1 treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run material.2.2 >>= finish) =
      evalDist (((fun tree : List Digest × QueryCache HashSpec =>
          (Concrete.CacheReplay.treeNode tree.2 parameter material.1
            treeHeight Concrete.rootNode, tree.2)) <$>
            treeValues parameter material.1 allTreeValueIndices
              material.2.2) >>= finish) := by
        rw [evalDist_bind,
          evalDist_rootTree_run_eq_treeValues_root_cache,
          ← evalDist_bind]
    _ = evalDist (treeValues parameter material.1 allTreeValueIndices
          material.2.2 >>= fun tree =>
        pure (CoupledGlobalChainKeygenView.toProgrammedView parameter {
          secret := material.1
          table := globalChainTrajectoryMaterialTable material
          values := tree.1
          cache := tree.2
        })) := by
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply evalDist_bind_congr
      intro tree htree
      unfold finish CoupledGlobalChainKeygenView.toProgrammedView
        CoupledGlobalChainKeygenView.root
      rw [programmedGlobalChainTrajectoryMaterial_table_eq_keygenTable
        parameter material hmaterial tree htree]

noncomputable def coupledGlobalChainKeygen :
    ProbComp ProgrammedGlobalChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let view ← coupledGlobalChainKeygenExperiment parameter
  pure (view.toProgrammedView parameter)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_coupledGlobalChainKeygen_eq_programmedTrajectories :
    evalDist coupledGlobalChainKeygen =
      evalDist (eraseAllChainTrajectories <$>
        programmedAllChainTrajectoryKeygen) := by
  unfold coupledGlobalChainKeygen programmedAllChainTrajectoryKeygen
    eraseAllChainTrajectories
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  change evalDist
      (CoupledGlobalChainKeygenView.toProgrammedView parameter <$>
        coupledGlobalChainKeygenExperiment parameter) = _
  rw [evalDist_coupledGlobalChainKeygen_toProgrammedView_eq parameter]
  unfold programmedGlobalChainTrajectoryMaterial
  simp only [bind_assoc, pure_bind]

def ProgrammedGlobalChainKeygenRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  left.table = right.2 ∧
    left.publicKey = right.1.publicKey ∧
    (∀ epoch,
      Concrete.CacheReplay.authenticationPath left.cache left.secretKey epoch =
        Concrete.CacheReplay.authenticationPath right.1.cache
          right.1.secretKey epoch)

def ProgrammedGlobalChainKeygenFullRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  ProgrammedGlobalChainKeygenRelation left right ∧
    ∃ values,
      TreeValuesReplay left.secretKey.parameter left.secretKey.chainStart
        left.cache allTreeValueIndices values ∧
      TreeValuesReplay right.1.secretKey.parameter
        right.1.secretKey.chainStart right.1.cache allTreeValueIndices values

end XmssSecurity.CappedChain
