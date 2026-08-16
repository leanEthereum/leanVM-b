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

noncomputable def uniformTrajectoryFromSeed :
    (steps : Nat) → Digest → ProbComp (Vector Digest (steps + 1))
  | 0, seed => pure (Vector.ofFn fun _ => seed)
  | steps + 1, seed => do
      let prior ← uniformTrajectoryFromSeed steps seed
      let next ← $ᵗ Digest
      pure (prior.push next)

@[simp]
theorem uniformTrajectoryFromSeed_zero (seed : Digest) :
    uniformTrajectoryFromSeed 0 seed =
      pure (Vector.ofFn fun _ => seed) := rfl

theorem uniformTrajectoryFromSeed_succ (steps : Nat) (seed : Digest) :
    uniformTrajectoryFromSeed (steps + 1) seed = (do
      let prior ← uniformTrajectoryFromSeed steps seed
      let next ← $ᵗ Digest
      pure (prior.push next)) := rfl

theorem evalDist_sampledHashOutputWithDigest_fst_eq_uniform :
    evalDist (Prod.fst <$> Rom.sampledHashOutputWithDigest) =
      evalDist ($ᵗ Digest) := by
  calc
    _ = evalDist (truncateHash <$> ($ᵗ HashOutput)) := by
      rw [evalDist_map, Rom.evalDist_sampledHashOutputWithDigest_eq_uniform,
        ← evalDist_map]
      simp [Functor.map_map]
    _ = evalDist ($ᵗ Digest) := Rom.evalDist_truncate_uniformHashOutput

theorem evalDist_programmedChainExtension_fst
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (values : Vector Digest (n + 1))
    (cache : QueryCache HashSpec) :
    evalDist (Prod.fst <$>
      programmedChainExtension parameter epoch chain step values cache) =
      evalDist ((fun next : Digest => values.push next) <$> ($ᵗ Digest)) := by
  unfold programmedChainExtension
  simp only [bind_pure_comp]
  calc
    _ = evalDist ((fun next : Digest => values.push next) <$>
          (Prod.fst <$> Rom.sampledHashOutputWithDigest)) := by
      simp [Functor.map_map]
    _ = evalDist ((fun next : Digest => values.push next) <$>
          ($ᵗ Digest)) := by
      rw [evalDist_map,
        evalDist_sampledHashOutputWithDigest_fst_eq_uniform, ← evalDist_map]

set_option maxRecDepth 100000 in
theorem evalDist_programmedChainTrajectory_fst_eq_uniform
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position : Nat) : ∀ (steps : Nat) (seed : Digest)
      (cache : QueryCache HashSpec),
      position + steps ≤ chainLength - 1 →
      evalDist (Prod.fst <$>
        programmedChainTrajectory parameter epoch chain position steps seed
          cache) =
      evalDist (uniformTrajectoryFromSeed steps seed) := by
  intro steps
  induction steps with
  | zero =>
      intro seed cache _hsteps
      simp [programmedChainTrajectory]
  | succ steps ih =>
      intro seed cache hsteps
      have hvalid : position + steps < chainLength - 1 := by omega
      simp only [programmedChainTrajectory, hvalid, ↓reduceDIte, map_bind]
      let prior := programmedChainTrajectory parameter epoch chain position
        steps seed cache
      calc
        _ = evalDist (prior >>= fun priorResult =>
              (fun next : Digest => priorResult.1.push next) <$>
                ($ᵗ Digest)) := by
          apply evalDist_bind_congr
          intro priorResult _hpriorResult
          exact evalDist_programmedChainExtension_fst parameter epoch chain
            ⟨position + steps, hvalid⟩ priorResult.1 priorResult.2
        _ = evalDist ((Prod.fst <$> prior) >>= fun priorValues =>
              (fun next : Digest => priorValues.push next) <$>
                ($ᵗ Digest)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = evalDist (uniformTrajectoryFromSeed steps seed >>=
              fun priorValues =>
              (fun next : Digest => priorValues.push next) <$>
                ($ᵗ Digest)) := by
          rw [evalDist_bind, ih seed cache (by omega), ← evalDist_bind]
        _ = evalDist (uniformTrajectoryFromSeed (steps + 1) seed) := by
          simp [uniformTrajectoryFromSeed_succ, map_eq_bind_pure_comp]

noncomputable def uniformFixedChainTrajectories
    (secret : Epoch → ChainIndex → Digest) (chain : ChainIndex)
    (steps : Nat) : List Epoch →
      ProbComp (List (Vector Digest (steps + 1)))
  | [] => pure []
  | epoch :: epochs => do
      let first ← uniformTrajectoryFromSeed steps (secret epoch chain)
      let rest ← uniformFixedChainTrajectories secret chain steps epochs
      pure (first :: rest)

@[simp]
theorem uniformFixedChainTrajectories_nil
    (secret : Epoch → ChainIndex → Digest) (chain : ChainIndex)
    (steps : Nat) :
    uniformFixedChainTrajectories secret chain steps [] = pure [] := rfl

theorem uniformFixedChainTrajectories_cons
    (secret : Epoch → ChainIndex → Digest) (chain : ChainIndex)
    (steps : Nat) (epoch : Epoch) (epochs : List Epoch) :
    uniformFixedChainTrajectories secret chain steps (epoch :: epochs) = (do
      let first ← uniformTrajectoryFromSeed steps (secret epoch chain)
      let rest ← uniformFixedChainTrajectories secret chain steps epochs
      pure (first :: rest)) := rfl

set_option maxRecDepth 100000 in
theorem evalDist_programmedFixedChainTrajectories_fst_eq_uniform
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec),
      evalDist (Prod.fst <$>
        programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
          steps cache epochs) =
      evalDist (uniformFixedChainTrajectories secret chain steps epochs) := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache
      simp
  | cons epoch epochs ih =>
      intro cache
      rw [programmedFixedSeedChainTrajectoriesFromCache_cons,
        uniformFixedChainTrajectories_cons]
      simp only [map_bind, bind_pure_comp]
      let firstProgram := programmedChainTrajectory parameter epoch chain 0
        steps (secret epoch chain) cache
      calc
        _ = evalDist (firstProgram >>= fun first =>
              uniformFixedChainTrajectories secret chain steps epochs >>=
                fun rest =>
              pure (first.1 :: rest)) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          calc
            _ = evalDist ((fun rest => first.1 :: rest) <$>
                  (Prod.fst <$>
                    programmedFixedSeedChainTrajectoriesFromCache parameter
                      secret chain steps first.2 epochs)) := by
              simp [map_eq_bind_pure_comp, bind_assoc]
            _ = evalDist ((fun rest => first.1 :: rest) <$>
                  uniformFixedChainTrajectories secret chain steps epochs) := by
              rw [evalDist_map, ih first.2, ← evalDist_map]
            _ = _ := by
              simp [map_eq_bind_pure_comp]
        _ = evalDist ((Prod.fst <$> firstProgram) >>= fun first =>
              uniformFixedChainTrajectories secret chain steps epochs >>=
                fun rest =>
              pure (first :: rest)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = evalDist (uniformTrajectoryFromSeed steps (secret epoch chain) >>=
              fun first =>
              uniformFixedChainTrajectories secret chain steps epochs >>=
                fun rest =>
              pure (first :: rest)) := by
          rw [evalDist_bind,
            evalDist_programmedChainTrajectory_fst_eq_uniform parameter epoch
              chain 0 steps (secret epoch chain) cache (by simpa using hsteps),
            ← evalDist_bind]

noncomputable def uniformAllChainTrajectories
    (secret : Epoch → ChainIndex → Digest) :
    List ChainIndex → ProbComp AllChainTrajectories
  | [] => pure (fun _ => [])
  | chain :: chains => do
      let first ← uniformFixedChainTrajectories secret chain
        (chainLength - 1) allEpochs
      let rest ← uniformAllChainTrajectories secret chains
      pure (Function.update rest chain first)

@[simp]
theorem uniformAllChainTrajectories_nil
    (secret : Epoch → ChainIndex → Digest) :
    uniformAllChainTrajectories secret [] = pure (fun _ => []) := rfl

theorem uniformAllChainTrajectories_cons
    (secret : Epoch → ChainIndex → Digest) (chain : ChainIndex)
    (chains : List ChainIndex) :
    uniformAllChainTrajectories secret (chain :: chains) = (do
      let first ← uniformFixedChainTrajectories secret chain
        (chainLength - 1) allEpochs
      let rest ← uniformAllChainTrajectories secret chains
      pure (Function.update rest chain first)) := rfl

set_option maxRecDepth 100000 in
theorem evalDist_programmedAllChainTrajectories_fst_eq_uniform
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec),
      evalDist (Prod.fst <$>
        programmedAllChainTrajectoriesFromCache parameter secret cache chains) =
      evalDist (uniformAllChainTrajectories secret chains) := by
  intro chains
  induction chains with
  | nil =>
      intro cache
      simp
  | cons chain chains ih =>
      intro cache
      rw [programmedAllChainTrajectoriesFromCache_cons,
        uniformAllChainTrajectories_cons]
      simp only [map_bind, bind_pure_comp]
      let firstProgram := programmedFixedSeedChainTrajectoriesFromCache
        parameter secret chain (chainLength - 1) cache allEpochs
      calc
        _ = evalDist (firstProgram >>= fun first =>
              uniformAllChainTrajectories secret chains >>= fun rest =>
              pure (Function.update rest chain first.1)) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          calc
            _ = evalDist ((fun rest => Function.update rest chain first.1) <$>
                  (Prod.fst <$>
                    programmedAllChainTrajectoriesFromCache parameter secret
                      first.2 chains)) := by
              simp [map_eq_bind_pure_comp, bind_assoc]
            _ = evalDist ((fun rest => Function.update rest chain first.1) <$>
                  uniformAllChainTrajectories secret chains) := by
              rw [evalDist_map, ih first.2, ← evalDist_map]
            _ = _ := by
              simp [map_eq_bind_pure_comp]
        _ = evalDist ((Prod.fst <$> firstProgram) >>= fun first =>
              uniformAllChainTrajectories secret chains >>= fun rest =>
              pure (Function.update rest chain first)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = evalDist (uniformFixedChainTrajectories secret chain
              (chainLength - 1) allEpochs >>= fun first =>
              uniformAllChainTrajectories secret chains >>= fun rest =>
              pure (Function.update rest chain first)) := by
          rw [evalDist_bind,
            evalDist_programmedFixedChainTrajectories_fst_eq_uniform parameter
              secret chain (chainLength - 1) le_rfl allEpochs cache,
            ← evalDist_bind]

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
