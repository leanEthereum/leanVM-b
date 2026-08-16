import XmssSecurity.CappedGlobalChainPresampling
import XmssSecurity.CappedChain.CausalKeygenCoupling

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

abbrev AllChainTrajectories := ChainIndex → List FullChainTrajectory

noncomputable def Concrete.allChainTrajectoriesFromCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    QueryCache HashSpec → List ChainIndex →
      ProbComp (AllChainTrajectories × QueryCache HashSpec)
  | cache, [] => pure (fun _ => [], cache)
  | cache, chain :: chains => do
      let first ← Concrete.fixedSeedChainTrajectoriesFromCache parameter secret
        chain (chainLength - 1) cache allEpochs
      let rest ← Concrete.allChainTrajectoriesFromCache parameter secret
        first.2 chains
      pure (Function.update rest.1 chain first.1, rest.2)

@[simp]
theorem Concrete.allChainTrajectoriesFromCache_nil
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (cache : QueryCache HashSpec) :
    Concrete.allChainTrajectoriesFromCache parameter secret cache [] =
      pure (fun _ => [], cache) := rfl

theorem Concrete.allChainTrajectoriesFromCache_cons
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (cache : QueryCache HashSpec) (chain : ChainIndex)
    (chains : List ChainIndex) :
    Concrete.allChainTrajectoriesFromCache parameter secret cache
      (chain :: chains) = (do
        let first ← Concrete.fixedSeedChainTrajectoriesFromCache parameter secret
          chain (chainLength - 1) cache allEpochs
        let rest ← Concrete.allChainTrajectoriesFromCache parameter secret
          first.2 chains
        pure (Function.update rest.1 chain first.1, rest.2)) := rfl

theorem evalDist_rootTree_run_eq_allChainTrajectories_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chains : List ChainIndex) (initialCache : QueryCache HashSpec) :
    evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache) =
      evalDist (Concrete.allChainTrajectoriesFromCache parameter secret
        initialCache chains >>= fun trajectoryResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run trajectoryResult.2) := by
  induction chains generalizing initialCache with
  | nil => simp
  | cons chain chains ih =>
      calc
        evalDist ((simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run initialCache) =
          evalDist (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret
            chain (chainLength - 1) initialCache allEpochs >>=
              fun first =>
            (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run first.2) :=
          evalDist_rootTree_run_eq_fixedSeedTrajectories_then_rootTree
            parameter secret chain (chainLength - 1) le_rfl allEpochs
              initialCache
        _ = evalDist (Concrete.fixedSeedChainTrajectoriesFromCache parameter
              secret chain (chainLength - 1) initialCache allEpochs >>=
            fun first =>
            Concrete.allChainTrajectoriesFromCache parameter secret first.2
              chains >>= fun rest =>
            (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run rest.2) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          exact ih first.2
        _ = evalDist (Concrete.allChainTrajectoriesFromCache parameter secret
              initialCache (chain :: chains) >>= fun trajectoryResult =>
            (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run trajectoryResult.2) := by
          rw [Concrete.allChainTrajectoriesFromCache_cons]
          simp only [bind_assoc, pure_bind]

noncomputable def allChainTrajectoryKeygen :
    ProbComp (ProgrammedGlobalChainKeygenView × AllChainTrajectories) := do
  let parameter ← Concrete.samplePublicParameter
  let secret ← Concrete.sampleSecret
  let trajectoryResult ← Concrete.allChainTrajectoriesFromCache parameter
    secret ∅ allChains
  let rootResult ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)).run trajectoryResult.2
  let secretKey : SecretKey := ⟨parameter, secret⟩
  pure ({
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey
    cache := rootResult.2
    table := globalKeygenChainValueTable rootResult.2 secretKey
  }, trajectoryResult.1)

def eraseAllChainTrajectories
    (result : ProgrammedGlobalChainKeygenView × AllChainTrajectories) :
    ProgrammedGlobalChainKeygenView := result.1

theorem evalDist_explicitGlobalChainKeygen_eq_allChainTrajectoryKeygen :
    evalDist explicitGlobalChainKeygen =
      evalDist (eraseAllChainTrajectories <$> allChainTrajectoryKeygen) := by
  unfold explicitGlobalChainKeygen allChainTrajectoryKeygen
    eraseAllChainTrajectories
  simp only [map_bind, bind_pure_comp, Functor.map_map]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secret
  let finish : Digest × QueryCache HashSpec →
      ProbComp ProgrammedGlobalChainKeygenView := fun rootResult =>
    let secretKey : SecretKey := ⟨parameter, secret⟩
    pure {
      publicKey := ⟨rootResult.1, parameter⟩
      secretKey
      cache := rootResult.2
      table := globalKeygenChainValueTable rootResult.2 secretKey
    }
  change evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run ∅ >>= finish) =
    evalDist (Concrete.allChainTrajectoriesFromCache parameter secret ∅
      allChains >>= fun trajectoryResult =>
      (simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run trajectoryResult.2 >>= finish)
  conv_lhs => rw [evalDist_bind]
  conv_rhs => rw [evalDist_bind]
  rw [evalDist_rootTree_run_eq_allChainTrajectories_then_rootTree parameter
    secret allChains ∅]
  simp only [evalDist_bind, bind_assoc]

theorem evalDist_actualGlobalChainKeygen_eq_allChainTrajectoryKeygen :
    evalDist actualGlobalChainKeygen =
      evalDist (eraseAllChainTrajectories <$> allChainTrajectoryKeygen) :=
  evalDist_actualGlobalChainKeygen_eq_explicit.trans
    evalDist_explicitGlobalChainKeygen_eq_allChainTrajectoryKeygen

end XmssSecurity.CappedChain
