import XmssSecurity.Proof.CappedGlobalTreeCacheCorrespondence
import XmssSecurity.Proof.CappedGlobalChainKeygenGameCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

theorem programmedGlobalChainTrajectoryMaterialWithBase_support_material
    (parameter : PublicParameter)
    (result : GlobalChainTrajectoryMaterial ×
      (GlobalChainValueIndex → Digest))
    (hresult : result ∈ support
      (programmedGlobalChainTrajectoryMaterialWithBase parameter)) :
    result.1 ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter) := by
  unfold programmedGlobalChainTrajectoryMaterialWithBase at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨base, _hbase, hmaterialBind⟩ := hresult
  rw [mem_support_bind_iff] at hmaterialBind
  obtain ⟨material, hmaterial, hpure⟩ := hmaterialBind
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  have hfirst : result.1 = material := congrArg Prod.fst hpure
  rw [hfirst]
  exact hmaterial

def CoupledGlobalChainKeygenFullCacheRelation
    (parameter : PublicParameter)
    (left : CoupledGlobalChainKeygenView)
    (right : CoupledGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  CoupledGlobalChainKeygenRelation parameter left right ∧
    ∃ leftEndpoints rightEndpoints,
      GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
        left.cache right.1.cache ∧
      ReplayEndpointsMatch parameter left.secret leftEndpoints left.cache ∧
      ReplayEndpointsMatch parameter right.1.secret rightEndpoints
        right.1.cache

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_coupledGlobalChainKeygen_withBase_fullCache
    (parameter : PublicParameter) :
    RelTriple
      (coupledGlobalChainKeygenExperiment parameter)
      (coupledGlobalChainKeygenWithBase parameter)
      (CoupledGlobalChainKeygenFullCacheRelation parameter) := by
  have hmaterials :=
    relTriple_programmedGlobalChainTrajectoryMaterial_withBase_support
      parameter
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
    (CoupledGlobalChainKeygenFullCacheRelation parameter)
  apply relTriple_bind hmaterials
  intro leftMaterial rightMaterialBase hmaterial
  obtain ⟨htable, hleftSupport, hrightBaseSupport⟩ := hmaterial
  unfold programmedGlobalChainTrajectoryMaterialWithBase at hrightBaseSupport
  rw [mem_support_bind_iff] at hrightBaseSupport
  obtain ⟨base, _hbase, hrightMaterialBind⟩ := hrightBaseSupport
  rw [mem_support_bind_iff] at hrightMaterialBind
  obtain ⟨rightMaterial, hrightSupport, hpure⟩ := hrightMaterialBind
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure] at htable ⊢
  apply relTriple_bind
    (relTriple_with_support
      (relTriple_globalMaterial_allTreeValues_run parameter leftMaterial
        rightMaterial hleftSupport hrightSupport))
  intro leftTree rightTree htree
  obtain ⟨htreeRelation, hleftTreeSupport, hrightTreeSupport⟩ := htree
  obtain ⟨hvalues, leftEndpoints, rightEndpoints, hcache,
    hleftEndpoints, hrightEndpoints⟩ := htreeRelation
  have hleftReplay := treeValues_support_replay parameter leftMaterial.1
    allTreeValueIndices leftMaterial.2.2 leftTree hleftTreeSupport
  have hrightReplay := treeValues_support_replay parameter
    rightMaterial.1 allTreeValueIndices rightMaterial.2.2
      rightTree hrightTreeSupport
  apply relTriple_pure_pure
  unfold CoupledGlobalChainKeygenFullCacheRelation
    CoupledGlobalChainKeygenRelation
  refine ⟨⟨htable, ?_, ?_, hvalues, hleftReplay, hrightReplay⟩,
    leftEndpoints, rightEndpoints, hcache, hleftEndpoints,
      hrightEndpoints⟩
  · exact globalTreeValuesReplay_eq_root parameter leftMaterial.1
      rightMaterial.1 leftTree.2 rightTree.2 leftTree.1 hleftReplay
        (hvalues ▸ hrightReplay)
  · intro epoch
    exact globalTreeValuesReplay_eq_authenticationPath parameter
      leftMaterial.1 rightMaterial.1 leftTree.2 rightTree.2 leftTree.1
        hleftReplay (hvalues ▸ hrightReplay) epoch

def ProgrammedGlobalChainKeygenFullCacheRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  ProgrammedGlobalChainKeygenFullRelation left right ∧
    ∃ leftEndpoints rightEndpoints,
      GlobalTreeCacheCorrespondence left.secretKey.parameter leftEndpoints
        rightEndpoints left.cache right.1.cache ∧
      ReplayEndpointsMatch left.secretKey.parameter left.secretKey.chainStart
        leftEndpoints left.cache ∧
      ReplayEndpointsMatch right.1.secretKey.parameter
        right.1.secretKey.chainStart rightEndpoints right.1.cache

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_coupledGlobalChainKeygenWithBaseFull_fullCache :
    RelTriple coupledGlobalChainKeygen coupledGlobalChainKeygenWithBaseFull
      ProgrammedGlobalChainKeygenFullCacheRelation := by
  unfold coupledGlobalChainKeygen coupledGlobalChainKeygenWithBaseFull
  apply relTriple_bind (relTriple_refl Concrete.samplePublicParameter)
  intro leftParameter rightParameter hparameter
  subst rightParameter
  apply relTriple_bind
    (relTriple_coupledGlobalChainKeygen_withBase_fullCache leftParameter)
  intro leftView rightView hview
  apply relTriple_pure_pure
  unfold ProgrammedGlobalChainKeygenFullCacheRelation
    ProgrammedGlobalChainKeygenFullRelation ProgrammedGlobalChainKeygenRelation
    CoupledGlobalChainKeygenView.toProgrammedView
  refine ⟨⟨⟨hview.1.1, ?_, hview.1.2.2.1⟩, leftView.values,
    hview.1.2.2.2.2.1, ?_⟩, hview.2⟩
  · exact congrArg (fun root => PublicKey.mk root leftParameter)
      hview.1.2.1
  · rw [hview.1.2.2.2.1]
    exact hview.1.2.2.2.2.2

theorem relTriple_trajectoryProgrammedGlobalChainKeygen_withBase_fullCache :
    RelTriple trajectoryProgrammedGlobalChainKeygen
      (trajectoryProgrammedGlobalChainKeygen >>= fun keyView =>
        ($ᵗ (GlobalChainValueIndex → Digest)) >>= fun base =>
        pure (keyView, base))
      ProgrammedGlobalChainKeygenFullCacheRelation := by
  apply relTriple_of_evalDist_eq_left
    evalDist_coupledGlobalChainKeygen_eq_trajectoryProgrammed.symm
  exact relTriple_of_evalDist_eq_right
    evalDist_coupledGlobalChainKeygenWithBaseFull_eq_trajectoryProgrammed
    relTriple_coupledGlobalChainKeygenWithBaseFull_fullCache

end XmssSecurity.CappedChain
