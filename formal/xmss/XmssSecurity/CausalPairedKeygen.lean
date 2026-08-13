import XmssSecurity.CausalTreeTableIndependence

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

structure CoupledWarmedKeygenView where
  secret : Epoch → ChainIndex → Digest
  table : ChainValueIndex → Digest
  values : List Digest
  cache : QueryCache HashSpec

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

theorem CoupledWarmedKeygenRelation.secret_eq_of_ne
    (parameter : PublicParameter) (chain : ChainIndex)
    (left right : CoupledWarmedKeygenView)
    (hrel : CoupledWarmedKeygenRelation parameter chain left right)
    (epoch : Epoch) (candidate : ChainIndex) (hne : candidate ≠ chain) :
    left.secret epoch candidate = right.secret epoch candidate := by
  exact secret_eq_of_outsideChain_eq chain left.secret right.secret hrel.1
    epoch candidate hne

end XmssSecurity
