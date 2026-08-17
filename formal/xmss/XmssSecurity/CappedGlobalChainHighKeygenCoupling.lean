import XmssSecurity.CappedGlobalChainTrajectoryHighUniformity
import XmssSecurity.CappedGlobalTreeKeygenCacheCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

noncomputable def programmedGlobalChainTrajectoryMaterialWithBaseHigh
    (parameter : PublicParameter) :
    ProbComp ((GlobalChainTrajectoryMaterial ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) := do
  let materialBase ←
    programmedGlobalChainTrajectoryMaterialWithBase parameter
  let high ← independentGlobalChainHigh
  pure (materialBase, high)

def programmedGlobalChainMaterialBaseHighView
    (result : (GlobalChainTrajectoryMaterial ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    (GlobalChainValueIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest) :=
  (result.1.2, result.2)

theorem evalDist_programmedGlobalChainMaterialBaseHighView_eq_independent
    (parameter : PublicParameter) :
    evalDist (programmedGlobalChainMaterialBaseHighView <$>
      programmedGlobalChainTrajectoryMaterialWithBaseHigh parameter) =
    evalDist independentGlobalChainTableHigh := by
  unfold programmedGlobalChainTrajectoryMaterialWithBaseHigh
    programmedGlobalChainMaterialBaseHighView
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  calc
    _ = evalDist ((globalChainTrajectoryMaterialBase <$>
          programmedGlobalChainTrajectoryMaterialWithBase parameter) >>=
        fun table => independentGlobalChainHigh >>= fun high =>
          pure (table, high)) := by
      simp [globalChainTrajectoryMaterialBase, map_eq_bind_pure_comp,
        bind_assoc]
    _ = evalDist ((globalChainTrajectoryMaterialTable <$>
          programmedGlobalChainTrajectoryMaterial parameter) >>=
        fun table => independentGlobalChainHigh >>= fun high =>
          pure (table, high)) := by
      rw [evalDist_bind,
        ← evalDist_programmedGlobalChainTrajectoryMaterial_table_eq_base
          parameter,
        ← evalDist_bind]
    _ = evalDist (independentGlobalChainValueTable >>= fun table =>
        independentGlobalChainHigh >>= fun high => pure (table, high)) := by
      rw [evalDist_bind,
        evalDist_programmedGlobalChainTrajectoryMaterial_table_eq_uniform
          parameter,
        ← evalDist_bind]
      unfold independentGlobalChainValueTable
      rfl
    _ = _ := by rfl

def ProgrammedGlobalChainMaterialBaseHighRelation
    (parameter : PublicParameter)
    (left : GlobalChainTrajectoryMaterial)
    (right : (GlobalChainTrajectoryMaterial ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) : Prop :=
  globalChainTrajectoryMaterialTable left = right.1.2 ∧
    globalChainEdgeHighTableOfCache left.2.2 parameter
      (globalChainTrajectoryMaterialTable left) = right.2

theorem relTriple_programmedGlobalChainTrajectoryMaterial_withBaseHigh
    (parameter : PublicParameter) :
    RelTriple
      (programmedGlobalChainTrajectoryMaterial parameter)
      (programmedGlobalChainTrajectoryMaterialWithBaseHigh parameter)
      (ProgrammedGlobalChainMaterialBaseHighRelation parameter) := by
  classical
  letI : DecidableEq ((GlobalChainValueIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest)) := Classical.decEq _
  have hprojection :
      evalDist (programmedGlobalChainTrajectoryCacheTableHighView parameter) =
      evalDist (programmedGlobalChainMaterialBaseHighView <$>
        programmedGlobalChainTrajectoryMaterialWithBaseHigh parameter) := by
    calc
      _ = evalDist independentGlobalChainTableHigh :=
        evalDist_programmedGlobalChainTrajectoryCacheTableHighView_eq_independent
          parameter
      _ = _ :=
        (evalDist_programmedGlobalChainMaterialBaseHighView_eq_independent
          parameter).symm
  apply relTriple_post_mono
    (relTriple_of_evalDist_map_eq_general
      (programmedGlobalChainTrajectoryMaterial parameter)
      (programmedGlobalChainTrajectoryMaterialWithBaseHigh parameter)
      (fun material =>
        (globalChainTrajectoryMaterialTable material,
          globalChainEdgeHighTableOfCache material.2.2 parameter
            (globalChainTrajectoryMaterialTable material)))
      programmedGlobalChainMaterialBaseHighView hprojection)
  intro left right hrelation
  exact ⟨congrArg Prod.fst hrelation, congrArg Prod.snd hrelation⟩

set_option maxRecDepth 100000 in
theorem Concrete.allChainTrajectoriesFromCache_edgesMatch
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (result : AllChainTrajectories × QueryCache HashSpec)
    (hresult : result ∈ support
      (Concrete.allChainTrajectoriesFromCache parameter secret ∅ allChains)) :
    GlobalChainTableEdgesMatch result.2 parameter
      (globalChainValueTableOfTrajectories result.1) := by
  have htable := Concrete.allChainTrajectoriesFromCache_globalTable_eq
    parameter secret result result.2 hresult le_rfl
  rw [htable]
  rintro ⟨chain, epoch, step⟩
  have hrun :=
    Concrete.allChainTrajectoriesFromCache_chainWalk_run_eq_pure
      parameter secret result hresult result.2 le_rfl epoch chain
  have hwalk :
      (Concrete.CacheReplay.oneTimePublicKey result.2 parameter secret epoch
          chain, result.2) ∈ support
        ((simulateQ randomOracle
          (Concrete.chainWalk parameter epoch chain 0 (chainLength - 1)
            (secret epoch chain) : OracleComp HashSpec Digest)).run result.2) := by
    rw [hrun]
    simp
  obtain ⟨output, hcached⟩ :=
    Concrete.CacheReplay.chainWalk_query_cached_in_largerCache
      parameter epoch chain 0 (chainLength - 1) (secret epoch chain)
        step.val step.isLt (by simp) result.2 result.2 result.2
        (Concrete.CacheReplay.oneTimePublicKey result.2 parameter secret epoch
          chain) hwalk le_rfl
  have hstepIndex :
      (⟨0 + step.val, by omega⟩ : ChainStep) = step := by
    apply Fin.ext
    simp
  rw [hstepIndex] at hcached
  refine ⟨output, ?_, ?_⟩
  · convert hcached using 1
    all_goals
      simp [globalChainTableEdgeInput, globalKeygenChainValueTable,
        keygenChainValueTable, chainStepDigit]
  · let stepFunction :=
      Concrete.CacheView.chainStep result.2 parameter epoch chain
    calc
      truncateHash output = Concrete.CacheView.digestAt result.2
          (Concrete.CacheView.chainInput parameter epoch chain step
            (Wots.walk stepFunction 0 step.val (secret epoch chain))) :=
        (Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached).symm
      _ = stepFunction step.val
          (Wots.walk stepFunction 0 step.val (secret epoch chain)) := by
        symm
        exact Concrete.CacheView.chainStep_eq result.2 parameter epoch chain
          step.val _ step.isLt
      _ = globalChainTableEdgeTarget
          (globalKeygenChainValueTable result.2 ⟨parameter, secret⟩)
          (chain, epoch, step) := by
        change stepFunction step.val
            (Wots.walk stepFunction 0 step.val (secret epoch chain)) =
          Wots.signChain stepFunction (chainStepNextDigit step)
            (secret epoch chain)
        unfold Wots.signChain
        rw [show (chainStepNextDigit step).val = step.val + 1 by
          simp [chainStepNextDigit]]
        simp only [Wots.walk, zero_add]

theorem programmedGlobalChainTrajectoryMaterial_edgesMatch
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter)) :
    GlobalChainTableEdgesMatch material.2.2 parameter
      (globalChainTrajectoryMaterialTable material) := by
  exact Concrete.allChainTrajectoriesFromCache_edgesMatch parameter material.1
    material.2
      (programmedGlobalChainTrajectoryMaterial_support_as_actual parameter
        material hmaterial)

noncomputable def coupledGlobalChainKeygenWithBaseHigh
    (parameter : PublicParameter) :
    ProbComp ((CoupledGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) := do
  let materialBaseHigh ←
    programmedGlobalChainTrajectoryMaterialWithBaseHigh parameter
  let material := materialBaseHigh.1.1
  let tree ← treeValues parameter material.1 allTreeValueIndices material.2.2
  pure ((({
    secret := material.1
    table := globalChainTrajectoryMaterialTable material
    values := tree.1
    cache := tree.2
  } : CoupledGlobalChainKeygenView), materialBaseHigh.1.2),
    materialBaseHigh.2)

def CoupledGlobalChainKeygenBaseHighRelation
    (parameter : PublicParameter)
    (left : CoupledGlobalChainKeygenView)
    (right : (CoupledGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) : Prop :=
  CoupledGlobalChainKeygenFullCacheRelation parameter left right.1 ∧
    globalChainEdgeHighTableOfCache left.cache parameter left.table = right.2 ∧
    GlobalChainTableEdgesMatch left.cache parameter left.table

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_coupledGlobalChainKeygen_withBaseHigh
    (parameter : PublicParameter) :
    RelTriple
      (coupledGlobalChainKeygenExperiment parameter)
      (coupledGlobalChainKeygenWithBaseHigh parameter)
      (CoupledGlobalChainKeygenBaseHighRelation parameter) := by
  unfold coupledGlobalChainKeygenExperiment
    coupledGlobalChainKeygenWithBaseHigh
  apply relTriple_bind (relTriple_with_support
    (relTriple_programmedGlobalChainTrajectoryMaterial_withBaseHigh parameter))
  intro leftMaterial rightMaterialBaseHigh hmaterial
  rcases hmaterial with ⟨⟨htable, hhigh⟩, hleftSupport,
    hrightSupport⟩
  have hrightMaterialSupport : rightMaterialBaseHigh.1.1 ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter) := by
    unfold programmedGlobalChainTrajectoryMaterialWithBaseHigh at hrightSupport
    rw [mem_support_bind_iff] at hrightSupport
    obtain ⟨materialBase, hmaterialBase, hhighBind⟩ := hrightSupport
    rw [mem_support_bind_iff] at hhighBind
    obtain ⟨sampledHigh, _hsampledHigh, hpure⟩ := hhighBind
    simp only [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
    unfold programmedGlobalChainTrajectoryMaterialWithBase at hmaterialBase
    rw [mem_support_bind_iff] at hmaterialBase
    obtain ⟨base, _hbase, hmaterialBind⟩ := hmaterialBase
    rw [mem_support_bind_iff] at hmaterialBind
    obtain ⟨material, hmaterial, hpureMaterial⟩ := hmaterialBind
    simp only [support_pure, Set.mem_singleton_iff] at hpureMaterial
    rw [hpureMaterial]
    exact hmaterial
  apply relTriple_bind
    (relTriple_with_support
      (relTriple_globalMaterial_allTreeValues_run parameter leftMaterial
        rightMaterialBaseHigh.1.1 hleftSupport hrightMaterialSupport))
  intro leftTree rightTree htree
  obtain ⟨htreeRelation, hleftTreeSupport, hrightTreeSupport⟩ := htree
  obtain ⟨hvalues, leftEndpoints, rightEndpoints, hcache,
    hleftEndpoints, hrightEndpoints⟩ := htreeRelation
  have hleftReplay := treeValues_support_replay parameter leftMaterial.1
    allTreeValueIndices leftMaterial.2.2 leftTree hleftTreeSupport
  have hrightReplay := treeValues_support_replay parameter
    rightMaterialBaseHigh.1.1.1 allTreeValueIndices
      rightMaterialBaseHigh.1.1.2.2 rightTree hrightTreeSupport
  have hmatches := programmedGlobalChainTrajectoryMaterial_edgesMatch
    parameter leftMaterial hleftSupport
  have hcacheLe := treeValues_cache_le parameter leftMaterial.1
    allTreeValueIndices leftMaterial.2.2 leftTree hleftTreeSupport
  have hhighFinal :=
    (globalChainEdgeHighTableOfCache_mono leftMaterial.2.2 leftTree.2
      parameter (globalChainTrajectoryMaterialTable leftMaterial)
      hmatches hcacheLe).symm.trans hhigh
  apply relTriple_pure_pure
  refine ⟨?_, ?_, ?_⟩
  · unfold CoupledGlobalChainKeygenFullCacheRelation
      CoupledGlobalChainKeygenRelation
    refine ⟨⟨htable, ?_, ?_, hvalues, hleftReplay, hrightReplay⟩,
      leftEndpoints, rightEndpoints, hcache, hleftEndpoints,
        hrightEndpoints⟩
    · exact globalTreeValuesReplay_eq_root parameter leftMaterial.1
        rightMaterialBaseHigh.1.1.1 leftTree.2 rightTree.2 leftTree.1
          hleftReplay (hvalues ▸ hrightReplay)
    · intro epoch
      exact globalTreeValuesReplay_eq_authenticationPath parameter
        leftMaterial.1 rightMaterialBaseHigh.1.1.1 leftTree.2 rightTree.2
          leftTree.1 hleftReplay (hvalues ▸ hrightReplay) epoch
  · exact hhighFinal
  · exact hmatches.mono hcacheLe

end XmssSecurity.CappedChain
