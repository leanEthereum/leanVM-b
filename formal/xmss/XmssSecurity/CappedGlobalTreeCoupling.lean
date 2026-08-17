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
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply]
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

theorem relTriple_programmedGlobalChainTrajectoryMaterial_withBase_support
    (parameter : PublicParameter) :
    RelTriple
      (programmedGlobalChainTrajectoryMaterial parameter)
      (programmedGlobalChainTrajectoryMaterialWithBase parameter)
      (fun left right =>
        globalChainTrajectoryMaterialTable left = right.2 ∧
          left ∈ support (programmedGlobalChainTrajectoryMaterial parameter) ∧
          right ∈ support
            (programmedGlobalChainTrajectoryMaterialWithBase parameter)) := by
  exact relTriple_of_evalDist_map_eq_with_support_general
    (programmedGlobalChainTrajectoryMaterial parameter)
    (programmedGlobalChainTrajectoryMaterialWithBase parameter)
    globalChainTrajectoryMaterialTable globalChainTrajectoryMaterialBase
    (evalDist_programmedGlobalChainTrajectoryMaterial_table_eq_base parameter)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
set_option linter.constructorNameAsVariable false in
theorem relTriple_programmedGlobalChainTrajectoryMaterial_withBase
    (parameter : PublicParameter) :
    RelTriple
      (programmedGlobalChainTrajectoryMaterial parameter)
      (programmedGlobalChainTrajectoryMaterialWithBase parameter)
      (fun left right =>
        globalChainTrajectoryMaterialTable left = right.2 ∧
          TreeValuesFresh parameter allTreeValueIndices left.2.2 ∧
          TreeValuesFresh parameter allTreeValueIndices right.1.2.2) := by
  apply relTriple_post_mono
    (relTriple_programmedGlobalChainTrajectoryMaterial_withBase_support
      parameter)
  intro left right hrelation
  obtain ⟨htable, hleftSupport, hrightSupport⟩ := hrelation
  refine ⟨htable, ?_, ?_⟩
  · exact programmedAllChainTrajectories_treeValuesFresh parameter left.1
      left.2
        (programmedGlobalChainTrajectoryMaterial_support_trajectories
          parameter left hleftSupport)
  · unfold programmedGlobalChainTrajectoryMaterialWithBase at hrightSupport
    rw [mem_support_bind_iff] at hrightSupport
    obtain ⟨base, _hbase, hmaterialBind⟩ := hrightSupport
    rw [mem_support_bind_iff] at hmaterialBind
    obtain ⟨material, hmaterial, hpure⟩ := hmaterialBind
    simp only [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
    unfold programmedGlobalChainTrajectoryMaterial at hmaterial
    rw [mem_support_bind_iff] at hmaterial
    obtain ⟨secret, _hsecret, htrajectoryBind⟩ := hmaterial
    rw [mem_support_bind_iff] at htrajectoryBind
    obtain ⟨trajectories, htrajectories, hmaterialPure⟩ := htrajectoryBind
    simp only [support_pure, Set.mem_singleton_iff] at hmaterialPure
    rw [hmaterialPure]
    exact programmedAllChainTrajectories_treeValuesFresh parameter secret
      trajectories htrajectories

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
    ⟨parameter, view.secret⟩ epoch

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

noncomputable def coupledGlobalChainKeygenWithBase
    (parameter : PublicParameter) :
    ProbComp (CoupledGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) := do
  let materialBase ←
    programmedGlobalChainTrajectoryMaterialWithBase parameter
  let material := materialBase.1
  let tree ← treeValues parameter material.1 allTreeValueIndices
    material.2.2
  pure ({
    secret := material.1
    table := globalChainTrajectoryMaterialTable material
    values := tree.1
    cache := tree.2
  }, materialBase.2)

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
    TreeValuesReplay parameter left.secret left.cache
      allTreeValueIndices left.values ∧
    TreeValuesReplay parameter right.1.secret right.1.cache
      allTreeValueIndices right.1.values

set_option maxHeartbeats 500000 in
set_option maxRecDepth 1000000 in
set_option linter.constructorNameAsVariable false in
theorem relTriple_coupledGlobalChainKeygen_withBase
    (parameter : PublicParameter) :
    RelTriple
      (coupledGlobalChainKeygenExperiment parameter)
      (coupledGlobalChainKeygenWithBase parameter)
      (CoupledGlobalChainKeygenRelation parameter) := by
  have hmaterials :=
    relTriple_programmedGlobalChainTrajectoryMaterial_withBase parameter
  change RelTriple
    (programmedGlobalChainTrajectoryMaterial parameter >>= fun material =>
      treeValues parameter material.1 allTreeValueIndices material.2.2 >>=
        fun tree =>
      pure ({
        secret := material.1
        table := globalChainTrajectoryMaterialTable material
        values := tree.1
        cache := tree.2
      } : CoupledGlobalChainKeygenView))
    (programmedGlobalChainTrajectoryMaterialWithBase parameter >>=
      fun materialBase =>
      treeValues parameter materialBase.1.1 allTreeValueIndices
          materialBase.1.2.2 >>= fun tree =>
      pure (({
        secret := materialBase.1.1
        table := globalChainTrajectoryMaterialTable materialBase.1
        values := tree.1
        cache := tree.2
      } : CoupledGlobalChainKeygenView), materialBase.2))
    (CoupledGlobalChainKeygenRelation parameter)
  apply relTriple_bind hmaterials
  intro leftMaterial rightMaterialBase hmaterial
  obtain ⟨htable, hleftFresh, hrightFresh⟩ := hmaterial
  let rightMaterial := rightMaterialBase.1
  apply relTriple_bind
    (relTriple_treeValues_same_values parameter parameter leftMaterial.1
      rightMaterial.1 allTreeValueIndices leftMaterial.2.2 rightMaterial.2.2
        allTreeValueIndices_pairwise hleftFresh hrightFresh)
  intro leftTree rightTree htree
  apply relTriple_pure_pure
  unfold CoupledGlobalChainKeygenRelation
  refine ⟨htable, ?_, ?_, htree.2.1, htree.2.2⟩
  · exact globalTreeValuesReplay_eq_root parameter leftMaterial.1
      rightMaterial.1 leftTree.2 rightTree.2 leftTree.1 htree.2.1
        (htree.1 ▸ htree.2.2)
  · intro epoch
    exact globalTreeValuesReplay_eq_authenticationPath parameter
      leftMaterial.1 rightMaterial.1 leftTree.2 rightTree.2 leftTree.1
        htree.2.1 (htree.1 ▸ htree.2.2) epoch

theorem programmedGlobalChainTrajectoryMaterial_table_eq_keygenTable
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (tree : List Digest × QueryCache HashSpec)
    (htree : tree ∈ support
      (treeValues parameter material.1 allTreeValueIndices material.2.2)) :
    globalChainTrajectoryMaterialTable material =
      globalKeygenChainValueTable tree.2 ⟨parameter, material.1⟩ := by
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
  secretKey := ⟨parameter, view.secret⟩
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
        secretKey := ⟨parameter, material.1⟩
        cache := rootResult.2
        table := globalKeygenChainValueTable rootResult.2
          ⟨parameter, material.1⟩
      } : ProgrammedGlobalChainKeygenView)) := by
  unfold coupledGlobalChainKeygenExperiment
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply evalDist_bind_congr
  intro material hmaterial
  let finish : Digest × QueryCache HashSpec →
      ProbComp ProgrammedGlobalChainKeygenView := fun rootResult => pure {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey := ⟨parameter, material.1⟩
    cache := rootResult.2
    table := globalKeygenChainValueTable rootResult.2
      ⟨parameter, material.1⟩
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

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
set_option linter.constructorNameAsVariable false in
theorem evalDist_coupledGlobalChainKeygenWithBase_eq_independentBase
    (parameter : PublicParameter) :
    evalDist (coupledGlobalChainKeygenWithBase parameter) =
      evalDist (coupledGlobalChainKeygenExperiment parameter >>= fun view =>
        ($ᵗ (GlobalChainValueIndex → Digest)) >>= fun base =>
        pure (view, base)) := by
  unfold coupledGlobalChainKeygenWithBase
    coupledGlobalChainKeygenExperiment
    programmedGlobalChainTrajectoryMaterialWithBase
  simp only [bind_assoc]
  let finish : (GlobalChainValueIndex → Digest) →
      GlobalChainTrajectoryMaterial →
      (List Digest × QueryCache HashSpec) →
      ProbComp (CoupledGlobalChainKeygenView ×
        (GlobalChainValueIndex → Digest)) :=
    fun base material tree => pure (({
      secret := material.1
      table := globalChainTrajectoryMaterialTable material
      values := tree.1
      cache := tree.2
    } : CoupledGlobalChainKeygenView), base)
  calc
    _ = evalDist (programmedGlobalChainTrajectoryMaterial parameter >>=
          fun material =>
          ($ᵗ (GlobalChainValueIndex → Digest)) >>= fun base =>
          treeValues parameter material.1 allTreeValueIndices material.2.2 >>=
            fun tree => finish base material tree) := by
      simpa [finish, bind_assoc] using
        (OracleComp.DeferredSampling.evalDist_bind_comm
          ($ᵗ (GlobalChainValueIndex → Digest))
          (programmedGlobalChainTrajectoryMaterial parameter)
          (fun base material =>
            treeValues parameter material.1 allTreeValueIndices material.2.2 >>=
              fun tree => finish base material tree))
    _ = evalDist (programmedGlobalChainTrajectoryMaterial parameter >>=
          fun material =>
          treeValues parameter material.1 allTreeValueIndices material.2.2 >>=
            fun tree =>
          ($ᵗ (GlobalChainValueIndex → Digest)) >>= fun base =>
            finish base material tree) := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro material
      exact OracleComp.DeferredSampling.evalDist_bind_comm
        ($ᵗ (GlobalChainValueIndex → Digest))
        (treeValues parameter material.1 allTreeValueIndices material.2.2)
        (fun base tree => finish base material tree)
    _ = _ := by
      simp [finish, bind_assoc]

noncomputable def coupledGlobalChainKeygenWithBaseFull :
    ProbComp (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) := do
  let parameter ← Concrete.samplePublicParameter
  let result ← coupledGlobalChainKeygenWithBase parameter
  pure (result.1.toProgrammedView parameter, result.2)

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

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_coupledGlobalChainKeygenWithBaseFull :
    RelTriple coupledGlobalChainKeygen coupledGlobalChainKeygenWithBaseFull
      ProgrammedGlobalChainKeygenRelation := by
  unfold coupledGlobalChainKeygen coupledGlobalChainKeygenWithBaseFull
  apply relTriple_bind (relTriple_refl Concrete.samplePublicParameter)
  intro leftParameter rightParameter hparameter
  subst rightParameter
  apply relTriple_bind
    (relTriple_coupledGlobalChainKeygen_withBase leftParameter)
  intro leftView rightView hview
  apply relTriple_pure_pure
  unfold ProgrammedGlobalChainKeygenRelation
    CoupledGlobalChainKeygenView.toProgrammedView
  refine ⟨hview.1, ?_, hview.2.2.1⟩
  exact congrArg (fun root => (PublicKey.mk root leftParameter)) hview.2.1

end XmssSecurity.CappedChain
