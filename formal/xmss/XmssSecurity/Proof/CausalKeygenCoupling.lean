import XmssSecurity.Proof.ChainOraclePresampling
import XmssSecurity.Proof.EncodingOracleSimulation

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem simulate_chainHash_run_of_fresh
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) (cache : QueryCache HashSpec)
    (habsent : cache
      (Concrete.CacheView.chainInput parameter epoch chain step value) = none) :
    (simulateQ randomOracle
      (Concrete.chainHash parameter epoch chain step value :
        OracleComp HashSpec Digest)).run cache =
      (fun output => (truncateHash output,
        cache.cacheQuery
          (Concrete.CacheView.chainInput parameter epoch chain step value)
          output)) <$> uniformHashOutput := by
  let input := Concrete.CacheView.chainInput parameter epoch chain step value
  change (fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$> (randomOracle input).run cache = _
  rw [randomOracle_run_none_eq_uniformHashOutput _ _ habsent]
  simp [Functor.map_map]

noncomputable def programmedChainExtension
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (values : Vector Digest (n + 1))
    (cache : QueryCache HashSpec) :
    ProbComp (Vector Digest ((n + 1) + 1) × QueryCache HashSpec) := do
  let sampled ← Rom.sampledHashOutputWithDigest
  pure (values.push sampled.1,
    cache.cacheQuery
      (Concrete.CacheView.chainInput parameter epoch chain step values.back)
      sampled.2)

set_option maxRecDepth 100000 in
theorem evalDist_chainExtension_eq_programmed
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (values : Vector Digest (n + 1))
    (cache : QueryCache HashSpec)
    (habsent : cache
      (Concrete.CacheView.chainInput parameter epoch chain step values.back) = none) :
    evalDist ((simulateQ randomOracle ((do
      let next ← Concrete.chainHash parameter epoch chain step values.back
      pure (values.push next)) :
        OracleComp HashSpec (Vector Digest ((n + 1) + 1)))).run
        cache) =
    evalDist (programmedChainExtension parameter epoch chain step values cache) := by
  rw [simulateQ_bind, StateT.run_bind,
    simulate_chainHash_run_of_fresh parameter epoch chain step values.back
      cache habsent]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, simulateQ_pure, StateT.run_pure]
  unfold programmedChainExtension
  symm
  exact Rom.evalDist_sampledHashOutputWithDigest_bind_eq_uniform_bind
    (fun sampled => pure
      (values.push sampled.1,
        cache.cacheQuery
          (Concrete.CacheView.chainInput parameter epoch chain step values.back)
          sampled.2))

noncomputable def programmedChainTrajectory
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position : Nat) : (steps : Nat) → Digest → QueryCache HashSpec →
      ProbComp (Vector Digest (steps + 1) × QueryCache HashSpec)
  | 0, value, cache => pure (Vector.ofFn (fun _ => value), cache)
  | steps + 1, value, cache => do
      let prior ← programmedChainTrajectory parameter epoch chain position
        steps value cache
      if hvalid : position + steps < chainLength - 1 then
        programmedChainExtension parameter epoch chain ⟨position + steps, hvalid⟩
          prior.1 prior.2
      else
        pure (prior.1.push 0, prior.2)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem evalDist_chainTrajectory_eq_programmed
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position : Nat) : ∀ (steps : Nat) (value : Digest)
      (cache : QueryCache HashSpec),
      position + steps ≤ chainLength - 1 →
      (∀ step : ChainStep, ∀ input,
        AtHashAddress parameter (.chain epoch chain step) input →
          cache input = none) →
      evalDist ((simulateQ randomOracle
        (Concrete.chainTrajectory parameter epoch chain position steps value)).run
          cache) =
      evalDist (programmedChainTrajectory parameter epoch chain position steps
        value cache) := by
  intro steps
  induction steps with
  | zero =>
      intro value cache _hsteps _habsent
      simp [Concrete.chainTrajectory_zero, programmedChainTrajectory]
  | succ steps ih =>
      intro value cache hsteps habsent
      have hvalid : position + steps < chainLength - 1 := by
        omega
      rw [Concrete.chainTrajectory_succ, programmedChainTrajectory]
      simp only [hvalid, ↓reduceDIte, simulateQ_bind, StateT.run_bind,
        simulateQ_pure, StateT.run_pure]
      let actualPrior := (simulateQ randomOracle
        (Concrete.chainTrajectory parameter epoch chain position steps value)).run
          cache
      let programmedPrior := programmedChainTrajectory parameter epoch chain
        position steps value cache
      let actualExtension := fun prior :
          Vector Digest (steps + 1) × QueryCache HashSpec =>
        (simulateQ randomOracle
          (Concrete.chainHash parameter epoch chain
            ⟨position + steps, hvalid⟩ prior.1.back :
            OracleComp HashSpec Digest)).run prior.2 >>= fun hashed =>
          pure (prior.1.push hashed.1, hashed.2)
      let programmedExtension := fun prior :
          Vector Digest (steps + 1) × QueryCache HashSpec =>
        programmedChainExtension parameter epoch chain
          ⟨position + steps, hvalid⟩ prior.1 prior.2
      change evalDist (actualPrior >>= actualExtension) =
        evalDist (programmedPrior >>= programmedExtension)
      calc
        evalDist (actualPrior >>= actualExtension) =
            evalDist (programmedPrior >>= actualExtension) := by
          rw [evalDist_bind, ih value cache (by omega) habsent,
            ← evalDist_bind]
        _ = evalDist (programmedPrior >>= programmedExtension) := by
          apply evalDist_bind_congr
          intro prior hprior
          have hpriorActual : prior ∈ support actualPrior :=
            (mem_support_iff_of_evalDist_eq
              (ih value cache (by omega) habsent) prior).mpr hprior
          have hfresh : prior.2
              (Concrete.CacheView.chainInput parameter epoch chain
                ⟨position + steps, hvalid⟩ prior.1.back) = none := by
            apply Concrete.CacheReplay.cache_none_of_zero_query_bound
              (Concrete.chainTrajectory parameter epoch chain position steps value)
              (Concrete.CacheView.chainInput parameter epoch chain
                ⟨position + steps, hvalid⟩ prior.1.back)
              cache prior.2 prior.1
            · apply OracleComp.IsQueryBoundP.of_imp
                (p' := AtHashAddress parameter
                  (.chain epoch chain ⟨position + steps, hvalid⟩))
              · intro input heq
                subst input
                exact (atHashAddress_tweakableHashInput_iff
                  parameter _ _ _).2 rfl
              · apply Concrete.chainTrajectory_queryBound_zero_of_avoids
                intro offset hoffset hoffsetValid heq
                simp only [HashDomain.chain.injEq, Fin.mk.injEq] at heq
                omega
            · apply habsent ⟨position + steps, hvalid⟩
              exact (atHashAddress_tweakableHashInput_iff
                parameter _ _ _).2 rfl
            · exact hpriorActual
          simpa [actualExtension, programmedExtension, simulateQ_bind,
            StateT.run_bind, simulateQ_pure, StateT.run_pure] using
            (evalDist_chainExtension_eq_programmed parameter epoch chain
              ⟨position + steps, hvalid⟩ prior.1 prior.2 hfresh)

noncomputable def programmedFixedSeedChainTrajectoriesFromCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    QueryCache HashSpec → List Epoch →
      ProbComp (List (Vector Digest (steps + 1)) × QueryCache HashSpec)
  | cache, [] => pure ([], cache)
  | cache, epoch :: epochs => do
      let first ← programmedChainTrajectory parameter epoch chain 0 steps
        (secret epoch chain) cache
      let rest ← programmedFixedSeedChainTrajectoriesFromCache parameter secret
        chain steps first.2 epochs
      pure (first.1 :: rest.1, rest.2)

theorem programmedFixedSeedChainTrajectoriesFromCache_cons
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (cache : QueryCache HashSpec)
    (epoch : Epoch) (epochs : List Epoch) :
    programmedFixedSeedChainTrajectoriesFromCache parameter secret chain steps
      cache (epoch :: epochs) = (do
        let first ← programmedChainTrajectory parameter epoch chain 0 steps
          (secret epoch chain) cache
        let rest ← programmedFixedSeedChainTrajectoriesFromCache parameter secret
          chain steps first.2 epochs
        pure (first.1 :: rest.1, rest.2)) := rfl

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem evalDist_fixedSeedChainTrajectories_eq_programmed
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec),
      epochs.Nodup →
      (∀ epoch ∈ epochs, ∀ step : ChainStep, ∀ input,
        AtHashAddress parameter (.chain epoch chain step) input →
          cache input = none) →
      evalDist (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret
        chain steps cache epochs) =
      evalDist (programmedFixedSeedChainTrajectoriesFromCache parameter secret
        chain steps cache epochs) := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache _hnodup _habsent
      rfl
  | cons epoch epochs ih =>
      intro cache hnodup habsent
      have hnotMem : epoch ∉ epochs := (List.nodup_cons.mp hnodup).1
      have htailNodup : epochs.Nodup := (List.nodup_cons.mp hnodup).2
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        programmedFixedSeedChainTrajectoriesFromCache_cons]
      let actualFirst := (simulateQ randomOracle
        (Concrete.chainTrajectory parameter epoch chain 0 steps
          (secret epoch chain))).run cache
      let programmedFirst := programmedChainTrajectory parameter epoch chain 0
        steps (secret epoch chain) cache
      let actualRest := fun first :
          Vector Digest (steps + 1) × QueryCache HashSpec =>
        Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
          steps first.2 epochs >>= fun rest =>
        pure (first.1 :: rest.1, rest.2)
      let programmedRest := fun first :
          Vector Digest (steps + 1) × QueryCache HashSpec =>
        programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
          steps first.2 epochs >>= fun rest =>
        pure (first.1 :: rest.1, rest.2)
      change evalDist (actualFirst >>= actualRest) =
        evalDist (programmedFirst >>= programmedRest)
      have hfirst : evalDist actualFirst = evalDist programmedFirst := by
        apply evalDist_chainTrajectory_eq_programmed parameter epoch chain 0
          steps (secret epoch chain) cache
        · simpa using hsteps
        · intro step input haddress
          exact habsent epoch (by simp) step input haddress
      calc
        evalDist (actualFirst >>= actualRest) =
            evalDist (programmedFirst >>= actualRest) := by
          rw [evalDist_bind, hfirst, ← evalDist_bind]
        _ = evalDist (programmedFirst >>= programmedRest) := by
          apply evalDist_bind_congr
          intro first hfirstProgrammed
          have hfirstActual : first ∈ support actualFirst :=
            (mem_support_iff_of_evalDist_eq hfirst first).mpr hfirstProgrammed
          have htailAbsent : ∀ later ∈ epochs, ∀ step : ChainStep, ∀ input,
              AtHashAddress parameter (.chain later chain step) input →
                first.2 input = none := by
            intro later hlater step input haddress
            apply Concrete.CacheReplay.cache_none_of_zero_query_bound
              (Concrete.chainTrajectory parameter epoch chain 0 steps
                (secret epoch chain)) input cache first.2 first.1
            · apply OracleComp.IsQueryBoundP.of_imp
                (p' := AtHashAddress parameter (.chain later chain step))
              · intro candidate heq
                subst candidate
                exact haddress
              · apply Concrete.chainTrajectory_queryBound_zero_of_avoids
                intro offset hoffset hoffsetValid heq
                simp only [HashDomain.chain.injEq] at heq
                exact hnotMem (heq.1 ▸ hlater)
            · exact habsent later (by simp [hlater]) step input haddress
            · exact hfirstActual
          have hrest := ih first.2 htailNodup htailAbsent
          simp only [actualRest, programmedRest]
          rw [evalDist_bind, hrest, ← evalDist_bind]

noncomputable def programmedWarmedFixedChainKeygenReplayTable
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let secretView ← extractFixedChainSeeds chain allEpochs
  let secret := unflattenSecret secretView.2
  let trajectoryResult ← programmedFixedSeedChainTrajectoriesFromCache
    parameter secret chain (chainLength - 1) ∅ allEpochs
  let rootResult ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)).run trajectoryResult.2
  pure {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey := (SecretKey.withoutPrecomputation parameter secret)
    cache := rootResult.2
    table := keygenChainValueTable rootResult.2 (SecretKey.withoutPrecomputation parameter secret) chain
  }

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 100000 in
theorem evalDist_chronologicallyWarmedFixedChainKeygen_eq_programmedReplay
    (chain : ChainIndex) :
    evalDist (chronologicallyWarmedExtractedFixedChainKeygen chain) =
      evalDist (programmedWarmedFixedChainKeygenReplayTable chain) := by
  unfold chronologicallyWarmedExtractedFixedChainKeygen
    programmedWarmedFixedChainKeygenReplayTable
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secretView
  let secret := unflattenSecret secretView.2
  let finish := fun trajectoryResult :
      List FullChainTrajectory × QueryCache HashSpec => do
    let rootResult ← (simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run trajectoryResult.2
    pure ({
      publicKey := ⟨rootResult.1, parameter⟩
      secretKey := (SecretKey.withoutPrecomputation parameter secret)
      cache := rootResult.2
      table := keygenChainValueTable rootResult.2
        (SecretKey.withoutPrecomputation parameter secret) chain
    } : ProgrammedFixedChainKeygenView)
  dsimp only
  simp only [bind_assoc]
  change evalDist
      (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs >>= finish) =
    evalDist
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs >>= finish)
  rw [evalDist_bind,
    evalDist_fixedSeedChainTrajectories_eq_programmed parameter secret chain
      (chainLength - 1) le_rfl allEpochs ∅ allEpochs_nodup (by simp),
    ← evalDist_bind]

noncomputable def programmedWarmedFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let secretView ← extractFixedChainSeeds chain allEpochs
  let secret := unflattenSecret secretView.2
  let trajectoryResult ← programmedFixedSeedChainTrajectoriesFromCache
    parameter secret chain (chainLength - 1) ∅ allEpochs
  let rootResult ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)).run trajectoryResult.2
  pure {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey := (SecretKey.withoutPrecomputation parameter secret)
    cache := rootResult.2
    table := chainValueTableOfList trajectoryResult.1
  }

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 100000 in
theorem evalDist_programmedWarmedFixedChainKeygenReplayTable_eq_explicit
    (chain : ChainIndex) :
    evalDist (programmedWarmedFixedChainKeygenReplayTable chain) =
      evalDist (programmedWarmedFixedChainKeygen chain) := by
  unfold programmedWarmedFixedChainKeygenReplayTable
    programmedWarmedFixedChainKeygen
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secretView
  let secret := unflattenSecret secretView.2
  apply evalDist_bind_congr
  intro trajectoryResult hprogrammed
  have htrajectories : evalDist
      (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs) =
      evalDist
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs) :=
    evalDist_fixedSeedChainTrajectories_eq_programmed parameter secret chain
      (chainLength - 1) le_rfl allEpochs ∅ allEpochs_nodup (by simp)
  have hactual : trajectoryResult ∈ support
      (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs) :=
    (mem_support_iff_of_evalDist_eq htrajectories trajectoryResult).mpr
      hprogrammed
  apply evalDist_bind_congr
  intro rootResult hroot
  have hcacheLe : trajectoryResult.2 ≤ rootResult.2 :=
    Concrete.CacheReplay.randomOracle_cache_le
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest) trajectoryResult.2 rootResult hroot
  have htable : chainValueTableOfList trajectoryResult.1 =
      keygenChainValueTable rootResult.2 (SecretKey.withoutPrecomputation parameter secret) chain :=
    Concrete.fixedSeedChainTrajectoriesFromCache_table_eq_in_largerCache
      parameter secret chain trajectoryResult rootResult.2 hactual hcacheLe
  rw [htable]

theorem evalDist_chronologicallyWarmedFixedChainKeygen_eq_programmed
    (chain : ChainIndex) :
    evalDist (chronologicallyWarmedExtractedFixedChainKeygen chain) =
      evalDist (programmedWarmedFixedChainKeygen chain) :=
  (evalDist_chronologicallyWarmedFixedChainKeygen_eq_programmedReplay chain).trans
    (evalDist_programmedWarmedFixedChainKeygenReplayTable_eq_explicit chain)

theorem evalDist_actualFixedChainKeygen_eq_programmedWarmed
    (chain : ChainIndex) :
    evalDist (actualFixedChainKeygen chain) =
      evalDist (programmedWarmedFixedChainKeygen chain) :=
  (evalDist_actualFixedChainKeygen_eq_chronologicallyWarmed chain).trans
    (evalDist_chronologicallyWarmedFixedChainKeygen_eq_programmed chain)

end XmssSecurity
