import XmssSecurity.Proof.CausalTreeTableIndependence
import XmssSecurity.Proof.CausalKeygenTableIndependence

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

structure CoupledWarmedKeygenView where
  secret : Epoch → ChainIndex → Digest
  table : ChainValueIndex → Digest
  values : List Digest
  cache : QueryCache HashSpec

def CoupledWarmedKeygenView.root
    (parameter : PublicParameter) (view : CoupledWarmedKeygenView) : Digest :=
  Concrete.CacheReplay.treeNode view.cache parameter view.secret
    treeHeight Concrete.rootNode

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
  secretKey := SecretKey.withoutPrecomputation parameter view.secret
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
        secretKey := SecretKey.withoutPrecomputation parameter
          (unflattenSecret material.1.2)
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
    secretKey := (SecretKey.withoutPrecomputation parameter secret)
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

end XmssSecurity
