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

def AllChainAddressesAbsent
    (parameter : PublicParameter) (chains : List ChainIndex)
    (cache : QueryCache HashSpec) : Prop :=
  ∀ chain ∈ chains, ∀ epoch step input,
    AtHashAddress parameter (.chain epoch chain step) input →
      cache input = none

set_option maxRecDepth 100000 in
theorem Concrete.fixedSeedChainTrajectories_preserves_otherChain_none
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (selected other : ChainIndex) (hne : selected ≠ other)
    (steps : Nat) (epochs : List Epoch) (cache : QueryCache HashSpec)
    (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec)
    (hresult : result ∈ support
      (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret selected
        steps cache epochs))
    (epoch : Epoch) (step : ChainStep) (input : HashInput)
    (haddress : AtHashAddress parameter (.chain epoch other step) input)
    (habsent : cache input = none) :
    result.2 input = none := by
  induction epochs generalizing cache result with
  | nil =>
      simp only [Concrete.fixedSeedChainTrajectoriesFromCache_nil,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact habsent
  | cons firstEpoch epochs ih =>
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      apply ih first.2 rest hrest
      apply Concrete.CacheReplay.cache_none_of_zero_query_bound
        (Concrete.chainTrajectory parameter firstEpoch selected 0 steps
          (secret firstEpoch selected)) input cache first.2 first.1
      · apply OracleComp.IsQueryBoundP.of_imp
          (p' := AtHashAddress parameter (.chain epoch other step))
        · intro candidate heq
          subst candidate
          exact haddress
        · apply Concrete.chainTrajectory_queryBound_zero_of_avoids
          intro offset hoffset hvalid heq
          simp only [HashDomain.chain.injEq] at heq
          exact hne heq.2.1
      · exact habsent
      · exact hfirst

noncomputable def programmedAllChainTrajectoriesFromCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    QueryCache HashSpec → List ChainIndex →
      ProbComp (AllChainTrajectories × QueryCache HashSpec)
  | cache, [] => pure (fun _ => [], cache)
  | cache, chain :: chains => do
      let first ← programmedFixedSeedChainTrajectoriesFromCache parameter secret
        chain (chainLength - 1) cache allEpochs
      let rest ← programmedAllChainTrajectoriesFromCache parameter secret
        first.2 chains
      pure (Function.update rest.1 chain first.1, rest.2)

@[simp]
theorem programmedAllChainTrajectoriesFromCache_nil
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (cache : QueryCache HashSpec) :
    programmedAllChainTrajectoriesFromCache parameter secret cache [] =
      pure (fun _ => [], cache) := rfl

theorem programmedAllChainTrajectoriesFromCache_cons
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (cache : QueryCache HashSpec) (chain : ChainIndex)
    (chains : List ChainIndex) :
    programmedAllChainTrajectoriesFromCache parameter secret cache
      (chain :: chains) = (do
        let first ← programmedFixedSeedChainTrajectoriesFromCache parameter
          secret chain (chainLength - 1) cache allEpochs
        let rest ← programmedAllChainTrajectoriesFromCache parameter secret
          first.2 chains
        pure (Function.update rest.1 chain first.1, rest.2)) := rfl

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 100000 in
theorem evalDist_allChainTrajectories_eq_programmed
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec),
      chains.Nodup → AllChainAddressesAbsent parameter chains cache →
      evalDist (Concrete.allChainTrajectoriesFromCache parameter secret cache
        chains) =
      evalDist (programmedAllChainTrajectoriesFromCache parameter secret cache
        chains) := by
  intro chains
  induction chains with
  | nil =>
      intro cache _hnodup _habsent
      simp
  | cons chain chains ih =>
      intro cache hnodup habsent
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [Concrete.allChainTrajectoriesFromCache_cons,
        programmedAllChainTrajectoriesFromCache_cons]
      let actualFirst := Concrete.fixedSeedChainTrajectoriesFromCache parameter
        secret chain (chainLength - 1) cache allEpochs
      let programmedFirst := programmedFixedSeedChainTrajectoriesFromCache
        parameter secret chain (chainLength - 1) cache allEpochs
      have hfirst : evalDist actualFirst = evalDist programmedFirst := by
        apply evalDist_fixedSeedChainTrajectories_eq_programmed parameter secret
          chain (chainLength - 1) le_rfl allEpochs cache allEpochs_nodup
        intro epoch _hepoch step input haddress
        exact habsent chain (by simp) epoch step input haddress
      calc
        _ = evalDist (programmedFirst >>= fun first =>
              Concrete.allChainTrajectoriesFromCache parameter secret first.2
                chains >>= fun rest =>
              pure (Function.update rest.1 chain first.1, rest.2)) := by
          rw [evalDist_bind, hfirst, ← evalDist_bind]
        _ = evalDist (programmedFirst >>= fun first =>
              programmedAllChainTrajectoriesFromCache parameter secret first.2
                chains >>= fun rest =>
              pure (Function.update rest.1 chain first.1, rest.2)) := by
          apply evalDist_bind_congr
          intro first hfirstProgrammed
          have hfirstActual : first ∈ support actualFirst :=
            (mem_support_iff_of_evalDist_eq hfirst first).mpr hfirstProgrammed
          have htailAbsent : AllChainAddressesAbsent parameter chains first.2 := by
            intro later hlater epoch step input haddress
            apply Concrete.fixedSeedChainTrajectories_preserves_otherChain_none
              parameter secret chain later
            · intro heq
              subst later
              exact hnotMem hlater
            · exact hfirstActual
            · exact haddress
            · exact habsent later (by simp [hlater]) epoch step input haddress
          have hrest := ih first.2 htailNodup htailAbsent
          rw [evalDist_bind, hrest, ← evalDist_bind]

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

noncomputable def programmedAllChainTrajectoryKeygen :
    ProbComp (ProgrammedGlobalChainKeygenView × AllChainTrajectories) := do
  let parameter ← Concrete.samplePublicParameter
  let secret ← Concrete.sampleSecret
  let trajectoryResult ← programmedAllChainTrajectoriesFromCache parameter
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

theorem evalDist_allChainTrajectoryKeygen_eq_programmed :
    evalDist allChainTrajectoryKeygen =
      evalDist programmedAllChainTrajectoryKeygen := by
  unfold allChainTrajectoryKeygen programmedAllChainTrajectoryKeygen
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secret
  conv_lhs => rw [evalDist_bind]
  conv_rhs => rw [evalDist_bind]
  rw [evalDist_allChainTrajectories_eq_programmed parameter secret allChains ∅
    allChains_nodup (by simp [AllChainAddressesAbsent])]

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

theorem evalDist_actualGlobalChainKeygen_eq_programmedAllChainTrajectories :
    evalDist actualGlobalChainKeygen =
      evalDist (eraseAllChainTrajectories <$>
        programmedAllChainTrajectoryKeygen) := by
  calc
    _ = evalDist (eraseAllChainTrajectories <$>
        allChainTrajectoryKeygen) :=
      evalDist_actualGlobalChainKeygen_eq_allChainTrajectoryKeygen
    _ = evalDist (eraseAllChainTrajectories <$>
        programmedAllChainTrajectoryKeygen) := by
      rw [evalDist_map, evalDist_allChainTrajectoryKeygen_eq_programmed,
        ← evalDist_map]

end XmssSecurity.CappedChain
