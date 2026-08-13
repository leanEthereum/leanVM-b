import XmssSecurity.CausalTreeTableIndependence
import XmssSecurity.CausalKeygenOutsideIndependence

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

def secretOutsideChain
    (chain : ChainIndex) (secret : Epoch → ChainIndex → Digest) :
    Epoch → ChainIndex → Digest := fun epoch candidate =>
  if candidate = chain then 0 else secret epoch candidate

theorem secret_eq_of_outsideChain_eq
    (chain : ChainIndex)
    (left right : Epoch → ChainIndex → Digest)
    (heq : secretOutsideChain chain left = secretOutsideChain chain right)
    (epoch : Epoch) (candidate : ChainIndex) (hne : candidate ≠ chain) :
    left epoch candidate = right epoch candidate := by
  have hpoint := congrFun (congrFun heq epoch) candidate
  simpa [secretOutsideChain, hne] using hpoint

theorem secretOutsideChain_eq_of_outsideChainSecret_eq
    (chain : ChainIndex) (left right : FlatSecret)
    (heq : outsideChainSecret chain left = outsideChainSecret chain right) :
    secretOutsideChain chain (unflattenSecret left) =
      secretOutsideChain chain (unflattenSecret right) := by
  funext epoch candidate
  by_cases hcandidate : candidate = chain
  · simp [secretOutsideChain, hcandidate]
  · have hpoint := congrFun (congrFun heq epoch) ⟨candidate, hcandidate⟩
    simpa [secretOutsideChain, outsideChainSecret, unflattenSecret,
      hcandidate] using hpoint

structure CoupledWarmedKeygenView where
  secret : Epoch → ChainIndex → Digest
  table : ChainValueIndex → Digest
  values : List Digest
  cache : QueryCache HashSpec

abbrev WarmedTrajectoryMaterial :=
  (List Digest × FlatSecret) ×
    (List FullChainTrajectory × QueryCache HashSpec)

noncomputable def warmedMaterialOutsideTable (chain : ChainIndex)
    (material : WarmedTrajectoryMaterial) :
    OutsideChainSecret chain × (ChainValueIndex → Digest) :=
  (outsideChainSecret chain material.1.2,
    chainValueTableOfList material.2.1)

def warmedMaterialBaseView (chain : ChainIndex)
    (result : WarmedTrajectoryMaterial × (ChainValueIndex → Digest)) :
    OutsideChainSecret chain × (ChainValueIndex → Digest) :=
  (outsideChainSecret chain result.1.1.2, result.2)

noncomputable def warmedTrajectoryMaterialWithBase
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (WarmedTrajectoryMaterial × (ChainValueIndex → Digest)) := do
  let material ← programmedWarmedTrajectoryMaterial parameter chain
  let base ← uniformChainValueTable chain
  pure (material, base)

theorem evalDist_warmedMaterialOutsideTable_eq_baseView
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[warmedMaterialOutsideTable chain <$>
        programmedWarmedTrajectoryMaterial parameter chain] =
      𝒟[warmedMaterialBaseView chain <$>
        warmedTrajectoryMaterialWithBase parameter chain] := by
  calc
    𝒟[warmedMaterialOutsideTable chain <$>
        programmedWarmedTrajectoryMaterial parameter chain] =
      𝒟[programmedWarmedOutsideTableView parameter chain] := rfl
    _ = 𝒟[independentOutsideTableView chain] :=
      evalDist_programmedWarmedOutsideTableView_eq_independent parameter chain
    _ = 𝒟[programmedWarmedOutsideOnly parameter chain >>= fun outside =>
          uniformChainValueTable chain >>= fun base =>
            pure (outside, base)] := by
      unfold independentOutsideTableView
      rw [evalDist_bind,
        ← evalDist_programmedWarmedOutsideOnly_eq_uniform parameter chain,
        ← evalDist_bind]
    _ = 𝒟[warmedMaterialBaseView chain <$>
          warmedTrajectoryMaterialWithBase parameter chain] := by
      simp [programmedWarmedOutsideOnly, warmedTrajectoryMaterialWithBase,
        warmedMaterialBaseView, map_eq_bind_pure_comp, bind_assoc]

def CoupledWarmedKeygenView.root
    (parameter : PublicParameter) (view : CoupledWarmedKeygenView) : Digest :=
  Concrete.CacheReplay.treeNode view.cache parameter view.secret
    treeHeight Concrete.rootNode

def CoupledWarmedKeygenView.authenticationPath
    (parameter : PublicParameter) (view : CoupledWarmedKeygenView)
    (epoch : Epoch) : MerkleLevel → Digest :=
  Concrete.CacheReplay.authenticationPath view.cache
    ⟨parameter, view.secret⟩ epoch

noncomputable def coupledWarmedKeygenExperiment
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp CoupledWarmedKeygenView := do
  let material ← programmedWarmedTrajectoryMaterial parameter chain
  let secret := unflattenSecret material.1.2
  let tree ← treeValues parameter secret allTreeValueIndices material.2.2
  pure {
    secret
    table := chainValueTableOfList material.2.1
    values := tree.1
    cache := tree.2
  }

noncomputable def coupledWarmedKeygenWithBase
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (CoupledWarmedKeygenView × (ChainValueIndex → Digest)) := do
  let materialBase ← warmedTrajectoryMaterialWithBase parameter chain
  let material := materialBase.1
  let secret := unflattenSecret material.1.2
  let tree ← treeValues parameter secret allTreeValueIndices material.2.2
  pure ({
    secret
    table := chainValueTableOfList material.2.1
    values := tree.1
    cache := tree.2
  }, materialBase.2)

theorem evalDist_coupledWarmedKeygenWithBase_eq_independentBase
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[coupledWarmedKeygenWithBase parameter chain] =
      𝒟[coupledWarmedKeygenExperiment parameter chain >>= fun view =>
        uniformChainValueTable chain >>= fun base => pure (view, base)] := by
  unfold coupledWarmedKeygenWithBase coupledWarmedKeygenExperiment
    warmedTrajectoryMaterialWithBase
  simp only [bind_assoc]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro material
  let finish : (ChainValueIndex → Digest) →
      (List Digest × QueryCache HashSpec) →
      ProbComp (CoupledWarmedKeygenView × (ChainValueIndex → Digest)) :=
    fun base tree =>
    pure (({
      secret := unflattenSecret material.1.2
      table := chainValueTableOfList material.2.1
      values := tree.1
      cache := tree.2
    } : CoupledWarmedKeygenView), base)
  simpa [finish, bind_assoc] using
    (OracleComp.DeferredSampling.evalDist_bind_comm
      (uniformChainValueTable chain)
      (treeValues parameter (unflattenSecret material.1.2)
        allTreeValueIndices material.2.2) finish)

def CoupledWarmedKeygenView.toProgrammedView
    (parameter : PublicParameter) (view : CoupledWarmedKeygenView) :
    ProgrammedFixedChainKeygenView := {
  publicKey := ⟨view.root parameter, parameter⟩
  secretKey := ⟨parameter, view.secret⟩
  cache := view.cache
  table := view.table
}

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_coupledWarmedKeygen_toProgrammedView_eq
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[CoupledWarmedKeygenView.toProgrammedView parameter <$>
      coupledWarmedKeygenExperiment parameter chain] =
    𝒟[programmedWarmedTrajectoryMaterial parameter chain >>= fun material =>
      (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret material.1.2)
          treeHeight Concrete.rootNode : OracleComp HashSpec Digest)).run
            material.2.2 >>= fun rootResult =>
      pure ({
        publicKey := ⟨rootResult.1, parameter⟩
        secretKey := ⟨parameter, unflattenSecret material.1.2⟩
        cache := rootResult.2
        table := chainValueTableOfList material.2.1
      } : ProgrammedFixedChainKeygenView)] := by
  unfold coupledWarmedKeygenExperiment
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply evalDist_bind_congr
  intro material _hmaterial
  let secret := unflattenSecret material.1.2
  let finish : Digest × QueryCache HashSpec →
      ProbComp ProgrammedFixedChainKeygenView := fun rootResult => pure {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey := ⟨parameter, secret⟩
    cache := rootResult.2
    table := chainValueTableOfList material.2.1
  }
  symm
  calc
    𝒟[(simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run material.2.2 >>= finish] =
      𝒟[((fun tree : List Digest × QueryCache HashSpec =>
          (Concrete.CacheReplay.treeNode tree.2 parameter secret
            treeHeight Concrete.rootNode, tree.2)) <$>
            treeValues parameter secret allTreeValueIndices material.2.2) >>=
              finish] := by
        rw [evalDist_bind,
          evalDist_rootTree_run_eq_treeValues_root_cache,
          ← evalDist_bind]
    _ = 𝒟[treeValues parameter secret allTreeValueIndices material.2.2 >>=
          fun tree => pure (CoupledWarmedKeygenView.toProgrammedView parameter {
            secret
            table := chainValueTableOfList material.2.1
            values := tree.1
            cache := tree.2
          })] := by
      simp [finish, CoupledWarmedKeygenView.toProgrammedView,
        CoupledWarmedKeygenView.root, map_eq_bind_pure_comp, bind_assoc]

noncomputable def coupledWarmedFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let view ← coupledWarmedKeygenExperiment parameter chain
  pure (view.toProgrammedView parameter)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_coupledWarmedFixedChainKeygen_eq_programmed
    (chain : ChainIndex) :
    𝒟[coupledWarmedFixedChainKeygen chain] =
      𝒟[programmedWarmedFixedChainKeygen chain] := by
  unfold coupledWarmedFixedChainKeygen programmedWarmedFixedChainKeygen
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  simpa [programmedWarmedTrajectoryMaterial, map_eq_bind_pure_comp,
    bind_assoc] using
      (evalDist_coupledWarmedKeygen_toProgrammedView_eq parameter chain)

def CoupledWarmedKeygenRelation
    (parameter : PublicParameter) (chain : ChainIndex)
    (left right : CoupledWarmedKeygenView) : Prop :=
  secretOutsideChain chain left.secret = secretOutsideChain chain right.secret ∧
    left.values = right.values ∧
    TreeValuesReplay parameter left.secret left.cache
      allTreeValueIndices left.values ∧
    TreeValuesReplay parameter right.secret right.cache
      allTreeValueIndices right.values ∧
    left.root parameter = right.root parameter ∧
    ∀ epoch, left.authenticationPath parameter epoch =
      right.authenticationPath parameter epoch

def CoupledWarmedKeygenBaseRelation
    (parameter : PublicParameter) (chain : ChainIndex)
    (left : CoupledWarmedKeygenView)
    (right : CoupledWarmedKeygenView × (ChainValueIndex → Digest)) : Prop :=
  left.table = right.2 ∧
    CoupledWarmedKeygenRelation parameter chain left right.1

theorem warmedTrajectoryMaterialWithBase_support_material
    (parameter : PublicParameter) (chain : ChainIndex)
    (result : WarmedTrajectoryMaterial × (ChainValueIndex → Digest))
    (hresult : result ∈ support
      (warmedTrajectoryMaterialWithBase parameter chain)) :
    result.1 ∈ support
      (programmedWarmedTrajectoryMaterial parameter chain) := by
  unfold warmedTrajectoryMaterialWithBase at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨material, hmaterial, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨base, _hbase, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact hmaterial

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem relTriple_coupledWarmedKeygenExperiment_withBase
    (parameter : PublicParameter) (chain : ChainIndex) :
    RelTriple
      (coupledWarmedKeygenExperiment parameter chain)
      (coupledWarmedKeygenWithBase parameter chain)
      (CoupledWarmedKeygenBaseRelation parameter chain) := by
  classical
  let materialExperiment := programmedWarmedTrajectoryMaterial parameter chain
  let rightMaterialExperiment := warmedTrajectoryMaterialWithBase parameter chain
  have hmaterials : RelTriple materialExperiment rightMaterialExperiment
      (fun left right =>
        warmedMaterialOutsideTable chain left =
            warmedMaterialBaseView chain right ∧
          left ∈ support materialExperiment ∧
          right ∈ support rightMaterialExperiment) := by
    apply relTriple_of_evalDist_map_eq_with_support_general
    exact evalDist_warmedMaterialOutsideTable_eq_baseView parameter chain
  unfold coupledWarmedKeygenExperiment coupledWarmedKeygenWithBase
  change RelTriple
    (materialExperiment >>= fun material =>
      let secret := unflattenSecret material.1.2
      treeValues parameter secret allTreeValueIndices material.2.2 >>= fun tree =>
      pure ({
        secret
        table := chainValueTableOfList material.2.1
        values := tree.1
        cache := tree.2
      } : CoupledWarmedKeygenView))
    (rightMaterialExperiment >>= fun materialBase =>
      let material := materialBase.1
      let secret := unflattenSecret material.1.2
      treeValues parameter secret allTreeValueIndices material.2.2 >>= fun tree =>
      pure (({
        secret
        table := chainValueTableOfList material.2.1
        values := tree.1
        cache := tree.2
      } : CoupledWarmedKeygenView), materialBase.2))
    (CoupledWarmedKeygenBaseRelation parameter chain)
  apply relTriple_bind hmaterials
  intro leftMaterial rightMaterialBase hmaterial
  let rightMaterial := rightMaterialBase.1
  let leftSecret := unflattenSecret leftMaterial.1.2
  let rightSecret := unflattenSecret rightMaterial.1.2
  have hleftMaterial : leftMaterial ∈ support
      (programmedWarmedTrajectoryMaterial parameter chain) := by
    simpa [materialExperiment] using hmaterial.2.1
  have hrightMaterialBase : rightMaterialBase ∈ support
      (warmedTrajectoryMaterialWithBase parameter chain) := by
    simpa [rightMaterialExperiment] using hmaterial.2.2
  have hrightMaterial : rightMaterial ∈ support
      (programmedWarmedTrajectoryMaterial parameter chain) := by
    exact warmedTrajectoryMaterialWithBase_support_material parameter chain
      rightMaterialBase hrightMaterialBase
  have htrees := relTriple_programmedWarmedTreeValues_same_root_and_paths
    parameter leftSecret rightSecret chain leftMaterial.2 rightMaterial.2
      (programmedWarmedTrajectoryMaterial_support_trajectory
        parameter chain leftMaterial hleftMaterial)
      (programmedWarmedTrajectoryMaterial_support_trajectory
        parameter chain rightMaterial hrightMaterial)
  apply relTriple_bind htrees
  intro leftTree rightTree htree
  apply relTriple_pure_pure
  have houtside : outsideChainSecret chain leftMaterial.1.2 =
      outsideChainSecret chain rightMaterial.1.2 :=
    congrArg Prod.fst hmaterial.1
  have htable : chainValueTableOfList leftMaterial.2.1 =
      rightMaterialBase.2 := congrArg Prod.snd hmaterial.1
  refine ⟨htable,
    secretOutsideChain_eq_of_outsideChainSecret_eq chain
      leftMaterial.1.2 rightMaterial.1.2 houtside,
    htree.1, htree.2.1, htree.2.2.1, ?_, ?_⟩
  · exact htree.2.2.2.1
  · exact htree.2.2.2.2

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem relTriple_coupledWarmedKeygenExperiment
    (parameter : PublicParameter) (chain : ChainIndex) :
    RelTriple
      (coupledWarmedKeygenExperiment parameter chain)
      (coupledWarmedKeygenExperiment parameter chain)
      (CoupledWarmedKeygenRelation parameter chain) := by
  classical
  let materialExperiment := programmedWarmedTrajectoryMaterial parameter chain
  let project := fun material :
      (List Digest × FlatSecret) ×
        (List FullChainTrajectory × QueryCache HashSpec) =>
    secretOutsideChain chain (unflattenSecret material.1.2)
  have hmaterials : RelTriple materialExperiment materialExperiment
      (fun left right =>
        project left = project right ∧
          left ∈ support materialExperiment ∧
          right ∈ support materialExperiment) := by
    apply relTriple_of_evalDist_map_eq_with_support_general
    rfl
  unfold coupledWarmedKeygenExperiment
  apply relTriple_bind hmaterials
  intro leftMaterial rightMaterial hmaterial
  let leftSecret := unflattenSecret leftMaterial.1.2
  let rightSecret := unflattenSecret rightMaterial.1.2
  have hleftMaterial : leftMaterial ∈ support
      (programmedWarmedTrajectoryMaterial parameter chain) := by
    simpa [materialExperiment] using hmaterial.2.1
  have hrightMaterial : rightMaterial ∈ support
      (programmedWarmedTrajectoryMaterial parameter chain) := by
    simpa [materialExperiment] using hmaterial.2.2
  have htrees := relTriple_programmedWarmedTreeValues_same_root_and_paths
    parameter leftSecret rightSecret chain leftMaterial.2 rightMaterial.2
      (programmedWarmedTrajectoryMaterial_support_trajectory
        parameter chain leftMaterial hleftMaterial)
      (programmedWarmedTrajectoryMaterial_support_trajectory
        parameter chain rightMaterial hrightMaterial)
  apply relTriple_bind htrees
  intro leftTree rightTree htree
  apply relTriple_pure_pure
  refine ⟨hmaterial.1, htree.1, htree.2.1, htree.2.2.1, ?_, ?_⟩
  · exact htree.2.2.2.1
  · exact htree.2.2.2.2

noncomputable def coupledWarmedFixedChainKeygenWithBase
    (chain : ChainIndex) :
    ProbComp (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) := do
  let parameter ← Concrete.samplePublicParameter
  let result ← coupledWarmedKeygenWithBase parameter chain
  pure (result.1.toProgrammedView parameter, result.2)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_coupledWarmedFixedChainKeygenWithBase_eq_actual
    (chain : ChainIndex) :
    𝒟[coupledWarmedFixedChainKeygenWithBase chain] =
      𝒟[actualFixedChainKeygen chain >>= fun keyView =>
        uniformChainValueTable chain >>= fun base =>
          pure (keyView, base)] := by
  calc
    𝒟[coupledWarmedFixedChainKeygenWithBase chain] =
        𝒟[coupledWarmedFixedChainKeygen chain >>= fun keyView =>
          uniformChainValueTable chain >>= fun base =>
            pure (keyView, base)] := by
      unfold coupledWarmedFixedChainKeygenWithBase
        coupledWarmedFixedChainKeygen
      simp only [bind_assoc, pure_bind]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro parameter
      calc
        𝒟[coupledWarmedKeygenWithBase parameter chain >>= fun result =>
            pure (result.1.toProgrammedView parameter, result.2)] =
          𝒟[(coupledWarmedKeygenExperiment parameter chain >>= fun view =>
              uniformChainValueTable chain >>= fun base => pure (view, base)) >>=
                fun result =>
                  pure (result.1.toProgrammedView parameter, result.2)] := by
            rw [evalDist_bind,
              evalDist_coupledWarmedKeygenWithBase_eq_independentBase
                parameter chain,
              ← evalDist_bind]
        _ = 𝒟[coupledWarmedKeygenExperiment parameter chain >>= fun view =>
              pure (view.toProgrammedView parameter) >>= fun keyView =>
                uniformChainValueTable chain >>= fun base =>
                  pure (keyView, base)] := by
            simp
    _ = 𝒟[programmedWarmedFixedChainKeygen chain >>= fun keyView =>
          uniformChainValueTable chain >>= fun base =>
            pure (keyView, base)] := by
      rw [evalDist_bind,
        evalDist_coupledWarmedFixedChainKeygen_eq_programmed chain,
        ← evalDist_bind]
    _ = 𝒟[actualFixedChainKeygen chain >>= fun keyView =>
          uniformChainValueTable chain >>= fun base =>
            pure (keyView, base)] := by
      rw [evalDist_bind,
        ← evalDist_actualFixedChainKeygen_eq_programmedWarmed chain,
        ← evalDist_bind]

noncomputable def coupledWarmedRichKeygen
    (chain : ChainIndex) :
    ProbComp (PublicParameter × CoupledWarmedKeygenView) := do
  let parameter ← Concrete.samplePublicParameter
  let view ← coupledWarmedKeygenExperiment parameter chain
  pure (parameter, view)

noncomputable def coupledWarmedRichKeygenWithBase
    (chain : ChainIndex) :
    ProbComp (PublicParameter ×
      (CoupledWarmedKeygenView × (ChainValueIndex → Digest))) := do
  let parameter ← Concrete.samplePublicParameter
  let result ← coupledWarmedKeygenWithBase parameter chain
  pure (parameter, result)

def CoupledWarmedRichKeygenBaseRelation
    (chain : ChainIndex)
    (left : PublicParameter × CoupledWarmedKeygenView)
    (right : PublicParameter ×
      (CoupledWarmedKeygenView × (ChainValueIndex → Digest))) : Prop :=
  left.1 = right.1 ∧
    CoupledWarmedKeygenBaseRelation left.1 chain left.2 right.2

theorem relTriple_coupledWarmedRichKeygen_withBase
    (chain : ChainIndex) :
    RelTriple (coupledWarmedRichKeygen chain)
      (coupledWarmedRichKeygenWithBase chain)
      (CoupledWarmedRichKeygenBaseRelation chain) := by
  unfold coupledWarmedRichKeygen coupledWarmedRichKeygenWithBase
  apply relTriple_bind (relTriple_refl Concrete.samplePublicParameter)
  intro leftParameter rightParameter hparameter
  subst rightParameter
  apply relTriple_bind
    (relTriple_coupledWarmedKeygenExperiment_withBase leftParameter chain)
  intro leftView rightView hview
  exact relTriple_pure_pure ⟨rfl, hview⟩

theorem CoupledWarmedKeygenRelation.secret_eq_of_ne
    (parameter : PublicParameter) (chain : ChainIndex)
    (left right : CoupledWarmedKeygenView)
    (hrel : CoupledWarmedKeygenRelation parameter chain left right)
    (epoch : Epoch) (candidate : ChainIndex) (hne : candidate ≠ chain) :
    left.secret epoch candidate = right.secret epoch candidate := by
  exact secret_eq_of_outsideChain_eq chain left.secret right.secret hrel.1
    epoch candidate hne

end XmssSecurity
