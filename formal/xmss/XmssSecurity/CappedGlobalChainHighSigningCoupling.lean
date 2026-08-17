import XmssSecurity.CappedGlobalChainHighKeygenCoupling
import XmssSecurity.CappedGlobalSigningTreeCacheCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 2000000
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

noncomputable def coupledGlobalChainKeygenWithBaseHighFull :
    ProbComp ((ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) := do
  let parameter ← Concrete.samplePublicParameter
  let result ← coupledGlobalChainKeygenWithBaseHigh parameter
  pure ((result.1.1.toProgrammedView parameter, result.1.2), result.2)

def ProgrammedGlobalChainKeygenBaseHighFullRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) : Prop :=
  ProgrammedGlobalChainKeygenFullCacheRelation left right.1 ∧
    globalChainEdgeHighTableOfCache left.cache left.secretKey.parameter
      left.table = right.2 ∧
    GlobalChainTableEdgesMatch left.cache left.secretKey.parameter left.table

theorem relTriple_coupledGlobalChainKeygenWithBaseHighFull :
    RelTriple coupledGlobalChainKeygen
      coupledGlobalChainKeygenWithBaseHighFull
      ProgrammedGlobalChainKeygenBaseHighFullRelation := by
  unfold coupledGlobalChainKeygen coupledGlobalChainKeygenWithBaseHighFull
  apply relTriple_bind (relTriple_refl Concrete.samplePublicParameter)
  intro leftParameter rightParameter hparameter
  subst rightParameter
  apply relTriple_bind
    (relTriple_coupledGlobalChainKeygen_withBaseHigh leftParameter)
  intro leftView rightView hview
  apply relTriple_pure_pure
  refine ⟨?_, ?_, ?_⟩
  · unfold ProgrammedGlobalChainKeygenFullCacheRelation
      ProgrammedGlobalChainKeygenFullRelation
      ProgrammedGlobalChainKeygenRelation
      CoupledGlobalChainKeygenView.toProgrammedView
    refine ⟨⟨⟨hview.1.1.1, ?_, hview.1.1.2.2.1⟩, leftView.values,
      hview.1.1.2.2.2.2.1, ?_⟩, hview.1.2⟩
    · exact congrArg (fun root => PublicKey.mk root leftParameter)
        hview.1.1.2.1
    · rw [hview.1.1.2.2.2.1]
      exact hview.1.1.2.2.2.2.2
  · exact hview.2.1
  · exact hview.2.2

theorem coupledGlobalChainKeygenWithBaseHighFull_support_keyView
    (result : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hresult : result ∈ support
      coupledGlobalChainKeygenWithBaseHighFull) :
    result.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen := by
  unfold coupledGlobalChainKeygenWithBaseHighFull at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨parameter, hparameter, hparameterBind⟩ := hresult
  rw [mem_support_bind_iff] at hparameterBind
  obtain ⟨viewBaseHigh, hviewBaseHigh, hpureView⟩ := hparameterBind
  simp only [support_pure, Set.mem_singleton_iff] at hpureView
  unfold coupledGlobalChainKeygenWithBaseHigh at hviewBaseHigh
  rw [mem_support_bind_iff] at hviewBaseHigh
  obtain ⟨materialBaseHigh, hmaterialBaseHigh, htreeBind⟩ := hviewBaseHigh
  rw [mem_support_bind_iff] at htreeBind
  obtain ⟨tree, htree, hpureTree⟩ := htreeBind
  simp only [support_pure, Set.mem_singleton_iff] at hpureTree
  unfold programmedGlobalChainTrajectoryMaterialWithBaseHigh at hmaterialBaseHigh
  rw [mem_support_bind_iff] at hmaterialBaseHigh
  obtain ⟨materialBase, hmaterialBase, hhighBind⟩ := hmaterialBaseHigh
  rw [mem_support_bind_iff] at hhighBind
  obtain ⟨high, _hhigh, hpureHigh⟩ := hhighBind
  simp only [support_pure, Set.mem_singleton_iff] at hpureHigh
  unfold programmedGlobalChainTrajectoryMaterialWithBase at hmaterialBase
  rw [mem_support_bind_iff] at hmaterialBase
  obtain ⟨base, _hbase, hmaterialBind⟩ := hmaterialBase
  rw [mem_support_bind_iff] at hmaterialBind
  obtain ⟨material, hmaterial, hpureMaterial⟩ := hmaterialBind
  simp only [support_pure, Set.mem_singleton_iff] at hpureMaterial
  have htreeMaterial : tree ∈ support
      (treeValues parameter material.1 allTreeValueIndices material.2.2) := by
    simpa [hpureHigh, hpureMaterial] using htree
  let expected : ProgrammedGlobalChainKeygenView :=
    (({
      secret := material.1
      table := globalChainTrajectoryMaterialTable material
      values := tree.1
      cache := tree.2
    } : CoupledGlobalChainKeygenView).toProgrammedView parameter)
  let expectedCoupled : CoupledGlobalChainKeygenView := {
    secret := material.1
    table := globalChainTrajectoryMaterialTable material
    values := tree.1
    cache := tree.2
  }
  have hparameterView : expectedCoupled ∈ support
      (coupledGlobalChainKeygenExperiment parameter) := by
    unfold coupledGlobalChainKeygenExperiment
    rw [mem_support_bind_iff]
    refine ⟨material, hmaterial, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨tree, htreeMaterial, by simp [expectedCoupled]⟩
  have hcoupled : expected ∈ support coupledGlobalChainKeygen := by
    unfold coupledGlobalChainKeygen
    rw [mem_support_bind_iff]
    refine ⟨parameter, hparameter, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨expectedCoupled, hparameterView,
      by simp [expected, expectedCoupled]⟩
  have hexpected : expected ∈ support
      trajectoryProgrammedGlobalChainKeygen :=
    (mem_support_iff_of_evalDist_eq
      evalDist_coupledGlobalChainKeygen_eq_trajectoryProgrammed expected).mp
        hcoupled
  have hkeyView : result.1.1 = expected := by
    rw [hpureView, hpureTree, hpureHigh, hpureMaterial]
  rw [hkeyView]
  exact hexpected

def ProgrammedGlobalChainKeygenBaseHighStableRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) : Prop :=
  ProgrammedGlobalChainKeygenFullCacheStableRelation left right.1 ∧
    globalChainEdgeHighTableOfCache left.cache left.secretKey.parameter
      left.table = right.2 ∧
    GlobalChainTableEdgesMatch left.cache left.secretKey.parameter left.table

theorem relTriple_coupledGlobalChainKeygen_withBaseHigh_fullCacheStable :
    RelTriple coupledGlobalChainKeygen
      coupledGlobalChainKeygenWithBaseHighFull
      ProgrammedGlobalChainKeygenBaseHighStableRelation := by
  apply relTriple_post_mono
    (relTriple_with_support
      relTriple_coupledGlobalChainKeygenWithBaseHighFull)
  intro left right hrel
  obtain ⟨hbaseHigh, hleftCoupledSupport, hrightSupport⟩ := hrel
  have hleftSupport : left ∈ support
      trajectoryProgrammedGlobalChainKeygen :=
    (mem_support_iff_of_evalDist_eq
      evalDist_coupledGlobalChainKeygen_eq_trajectoryProgrammed left).mp
        hleftCoupledSupport
  have hrightViewSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen :=
    coupledGlobalChainKeygenWithBaseHighFull_support_keyView right
      hrightSupport
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1.1 hrightViewSupport
  have hparameter : left.secretKey.parameter =
      right.1.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (keygen_parameter_eq left.keyResult hleftKey).symm
      _ = right.1.1.publicKey.parameter :=
        congrArg PublicKey.parameter hbaseHigh.1.1.1.2.1
      _ = right.1.1.secretKey.parameter :=
        keygen_parameter_eq right.1.1.keyResult hrightKey
  obtain ⟨leftEndpoints, rightEndpoints, hcache, hleftReplay,
    hrightReplay⟩ := hbaseHigh.1.2
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨hbaseHigh.1,
      trajectoryProgrammedGlobalChainKeygen_support_treeCacheStable left
        hleftSupport,
      trajectoryProgrammedGlobalChainKeygen_support_treeCacheStable right.1.1
        hrightViewSupport,
      leftEndpoints, rightEndpoints, hcache, hleftReplay, ?_⟩
    rw [hparameter]
    exact hrightReplay
  · exact hbaseHigh.2.1
  · exact hbaseHigh.2.2

theorem relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable :
    RelTriple trajectoryProgrammedGlobalChainKeygen
      coupledGlobalChainKeygenWithBaseHighFull
      ProgrammedGlobalChainKeygenBaseHighStableRelation := by
  exact relTriple_of_evalDist_eq_left
    evalDist_coupledGlobalChainKeygen_eq_trajectoryProgrammed.symm
    relTriple_coupledGlobalChainKeygen_withBaseHigh_fullCacheStable

def GlobalSignFullBaseHighResultRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (request : SignRequest)
    (leftResult rightResult : Option Signature × QueryCache HashSpec) : Prop :=
  GlobalSignFullResultRelation right.1.2 left.secretKey.parameter
      left.secretKey.chainStart right.1.1.secretKey.chainStart request
        left.cache right.1.1.cache leftResult rightResult ∧
    globalChainEdgeHighTableOfCache leftResult.2 left.secretKey.parameter
      left.table = right.2

theorem relTriple_keygenViews_globalSign_run_full_baseHigh
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache rightCache : QueryCache HashSpec)
    (hcacheAgreement : HashCachesAgreeOn
      (GlobalSigningComparableHashInput left.secretKey.parameter)
      leftCache rightCache)
    (htree : GlobalTreeSigningCacheRelation left.secretKey.parameter
      left.secretKey.chainStart right.1.1.secretKey.chainStart
      leftCache rightCache)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.1.cache ≤ rightCache)
    (request : SignRequest) :
    RelTriple
      ((simulateQ xmssRomImpl
        (Concrete.cappedScheme.sign left.publicKey left.secretKey
          request.epoch request.message)).run leftCache)
      ((simulateQ xmssRomImpl
        (Concrete.cappedScheme.sign right.1.1.publicKey right.1.1.secretKey
          request.epoch request.message)).run rightCache)
      (GlobalSignFullBaseHighResultRelation left right request) := by
  apply relTriple_post_mono
    (relTriple_keygenViews_globalSign_run_full left right.1
      hrel.1.toStable hleftSupport hrightSupport leftCache rightCache
        hcacheAgreement htree hleftLe hrightLe request)
  intro leftResult rightResult hsigned
  obtain ⟨randomness, decoded, hdecode, hoptions, hcaches,
    hleftFinal, hrightFinal⟩ := hsigned.1
  have hhighFinal :=
    (globalChainEdgeHighTableOfCache_mono left.cache leftResult.2
      left.secretKey.parameter left.table hrel.2.2 hleftFinal).symm.trans
        hrel.2.1
  exact ⟨⟨⟨randomness, decoded, hdecode, hoptions, hcaches,
    hleftFinal, hrightFinal⟩, hsigned.2⟩, hhighFinal⟩

end XmssSecurity.CappedChain
