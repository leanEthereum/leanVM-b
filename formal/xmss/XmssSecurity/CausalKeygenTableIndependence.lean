import XmssSecurity.CausalKeygenCoupling
import XmssSecurity.PublicRootUniformity

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem installChainTableEdgeOutputs_apply_of_avoids
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) (input : HashInput) :
    ∀ (edges : List ChainEdgeIndex) (outputs : List HashOutput)
      (cache : QueryCache HashSpec),
      (∀ edge ∈ edges,
        input ≠ chainTableEdgeInput parameter chain table edge) →
      installChainTableEdgeOutputs cache parameter chain table edges outputs input =
        cache input := by
  intro edges
  induction edges with
  | nil =>
      intro outputs cache _havoids
      rfl
  | cons edge edges ih =>
      intro outputs cache havoids
      cases outputs with
      | nil => rfl
      | cons output outputs =>
          rw [installChainTableEdgeOutputs_cons,
            ih outputs (cache.cacheQuery
              (chainTableEdgeInput parameter chain table edge) output)]
          · exact QueryCache.cacheQuery_of_ne cache output
              (havoids edge (by simp))
          · intro target htarget
            exact havoids target (by simp [htarget])

theorem fixedChainMaterialRepresentation_cache_avoids_merkle
    (parameter : PublicParameter) (chain : ChainIndex)
    (material : (List Digest × FlatSecret) ×
      (List Digest × (List HashOutput × QueryCache HashSpec)))
    (hmaterial : material ∈ support
      (fixedChainMaterialRepresentation parameter chain))
    (domain : HashDomain) (hmerkle : ∃ level node, domain = .merkle level node)
    (input : HashInput) (hinput : AtHashAddress parameter domain input) :
    material.2.2.2 input = none := by
  unfold fixedChainMaterialRepresentation at hmaterial
  rw [mem_support_bind_iff] at hmaterial
  obtain ⟨secretView, _hsecretView, hedgeView⟩ := hmaterial
  rw [mem_support_bind_iff] at hedgeView
  obtain ⟨edgeView, hedgeView, hpure⟩ := hedgeView
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst material
  unfold uniformInstalledChainEdgeCache at hedgeView
  rw [support_map] at hedgeView
  obtain ⟨tape, _htape, heq⟩ := hedgeView
  subst edgeView
  unfold installedChainEdgeTapeResult
  dsimp only
  rw [installChainTableEdgeOutputs_apply_of_avoids]
  · rfl
  · intro edge _hedge heq
    have hchain : AtHashAddress parameter
        (.chain edge.1 chain edge.2)
        (chainTableEdgeInput parameter chain
          (chainTableMaterialEquiv.symm
            ((fun epoch => secretView.2 (epoch, chain)),
              chainEdgeTableOfTape tape.1)) edge) := by
      simp [chainTableEdgeInput, Concrete.CacheView.chainInput]
    have hboth : AtHashAddress parameter domain
        (chainTableEdgeInput parameter chain
          (chainTableMaterialEquiv.symm
            ((fun epoch => secretView.2 (epoch, chain)),
              chainEdgeTableOfTape tape.1)) edge) := by
      rw [← heq]
      exact hinput
    obtain ⟨level, node, rfl⟩ := hmerkle
    simp [chainTableEdgeInput, Concrete.CacheView.chainInput] at hboth

theorem fixedChainMaterial_rootTree_probability
    (parameter : PublicParameter) (chain : ChainIndex)
    (material : (List Digest × FlatSecret) ×
      (List Digest × (List HashOutput × QueryCache HashSpec)))
    (hmaterial : material ∈ support
      (fixedChainMaterialRepresentation parameter chain))
    (target : Digest) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      (simulateQ randomOracle
        (Concrete.treeNode parameter (unflattenSecret material.1.2)
          treeHeight Concrete.rootNode : OracleComp HashSpec Digest)).run
            material.2.2.2] =
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  have hheight : treeHeight = (treeHeight - 1) + 1 := by decide
  rw [hheight]
  apply Concrete.treeNode_positive_probability_from_cache
    (parameter := parameter) (secret := unflattenSecret material.1.2)
    (levels := treeHeight - 1) (node := Concrete.rootNode)
    (hlevel := by decide)
    (hvalid := by
      unfold TreeSubtreeValid Concrete.rootNode lifetime
      change (0 + 1) * 2 ^ (treeHeight - 1 + 1) ≤ 2 ^ treeHeight
      rw [← hheight]
      simp)
    (initialCache := material.2.2.2)
  intro input hinput
  exact fixedChainMaterialRepresentation_cache_avoids_merkle
    parameter chain material hmaterial
      (.merkle ⟨treeHeight - 1, by decide⟩ Concrete.rootNode)
      ⟨_, _, rfl⟩ input hinput

set_option maxRecDepth 100000 in
theorem evalDist_fixedChainMaterial_root_eq_uniform
    (parameter : PublicParameter) (chain : ChainIndex)
    (material : (List Digest × FlatSecret) ×
      (List Digest × (List HashOutput × QueryCache HashSpec)))
    (hmaterial : material ∈ support
      (fixedChainMaterialRepresentation parameter chain)) :
    𝒟[Prod.fst <$> (simulateQ randomOracle
      (Concrete.treeNode parameter (unflattenSecret material.1.2)
        treeHeight Concrete.rootNode : OracleComp HashSpec Digest)).run
          material.2.2.2] =
      𝒟[$ᵗ Digest] := by
  apply SPMF.ext
  intro target
  change Pr[= target | Prod.fst <$> (simulateQ randomOracle
      (Concrete.treeNode parameter (unflattenSecret material.1.2)
        treeHeight Concrete.rootNode : OracleComp HashSpec Digest)).run
          material.2.2.2] = Pr[= target | $ᵗ Digest]
  rw [← probEvent_eq_eq_probOutput, probEvent_map]
  calc
    Pr[fun result : Digest × QueryCache HashSpec =>
          result.1 = target |
        (simulateQ randomOracle
          (Concrete.treeNode parameter (unflattenSecret material.1.2)
            treeHeight Concrete.rootNode : OracleComp HashSpec Digest)).run
              material.2.2.2] =
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      fixedChainMaterial_rootTree_probability
        parameter chain material hmaterial target
    _ = Pr[= target | $ᵗ Digest] := by
      rw [probOutput_uniformSample, HiddenValue.card_digest]

noncomputable def programmedFixedChainPublicTableView
    (chain : ChainIndex) : ProbComp (PublicKey × (ChainValueIndex → Digest)) :=
  (fun result : ProgrammedFixedChainKeygenView =>
    (result.publicKey, result.table)) <$> programmedFixedChainKeygen chain

noncomputable def uniformChainValueTable
    (chain : ChainIndex) : ProbComp (ChainValueIndex → Digest) :=
  Concrete.sampledAllEpochChainValueTableOnly 0 chain

set_option maxRecDepth 1000000 in
theorem evalDist_fixedChainMaterialTableOnly_eq_uniformChainValueTable
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[fixedChainMaterialTableOnly parameter chain] =
      𝒟[uniformChainValueTable chain] := by
  unfold uniformChainValueTable
  exact (evalDist_fixedChainMaterialTableOnly_eq_uniform parameter chain).trans
    (Concrete.evalDist_sampledAllEpochChainValueTableOnly_eq_uniform
      0 chain).symm

noncomputable def independentFixedChainPublicTableView
    (chain : ChainIndex) : ProbComp (PublicKey × (ChainValueIndex → Digest)) := do
  let parameter ← Concrete.samplePublicParameter
  let root ← $ᵗ Digest
  let table ← uniformChainValueTable chain
  pure (⟨root, parameter⟩, table)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_programmedFixedChainPublicTableView_eq_independent
    (chain : ChainIndex) :
    𝒟[programmedFixedChainPublicTableView chain] =
      𝒟[independentFixedChainPublicTableView chain] := by
  unfold programmedFixedChainPublicTableView programmedFixedChainKeygen
    independentFixedChainPublicTableView
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  calc
    𝒟[fixedChainMaterialRepresentation parameter chain >>= fun material =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter (unflattenSecret material.1.2)
            treeHeight Concrete.rootNode : OracleComp HashSpec Digest)).run
              material.2.2.2 >>= fun rootResult =>
        pure ((⟨rootResult.1, parameter⟩ : PublicKey),
          fixedChainMaterialTable chain material)] =
      𝒟[fixedChainMaterialRepresentation parameter chain >>= fun material =>
        ($ᵗ Digest) >>= fun root =>
        pure ((⟨root, parameter⟩ : PublicKey),
          fixedChainMaterialTable chain material)] := by
      apply evalDist_bind_congr
      intro material hmaterial
      calc
        𝒟[(simulateQ randomOracle
              (Concrete.treeNode parameter (unflattenSecret material.1.2)
                treeHeight Concrete.rootNode : OracleComp HashSpec Digest)).run
                  material.2.2.2 >>= fun rootResult =>
            pure ((⟨rootResult.1, parameter⟩ : PublicKey),
              fixedChainMaterialTable chain material)] =
          𝒟[(Prod.fst <$> (simulateQ randomOracle
              (Concrete.treeNode parameter (unflattenSecret material.1.2)
                treeHeight Concrete.rootNode : OracleComp HashSpec Digest)).run
                  material.2.2.2) >>= fun root =>
            pure ((⟨root, parameter⟩ : PublicKey),
              fixedChainMaterialTable chain material)] := by
            simp [map_eq_bind_pure_comp, bind_assoc]
        _ = 𝒟[($ᵗ Digest) >>= fun root =>
              pure ((⟨root, parameter⟩ : PublicKey),
                fixedChainMaterialTable chain material)] := by
            rw [evalDist_bind,
              evalDist_fixedChainMaterial_root_eq_uniform
                parameter chain material hmaterial,
              ← evalDist_bind]
    _ = 𝒟[($ᵗ Digest) >>= fun root =>
          fixedChainMaterialRepresentation parameter chain >>= fun material =>
          pure ((⟨root, parameter⟩ : PublicKey),
            fixedChainMaterialTable chain material)] :=
      OracleComp.DeferredSampling.evalDist_bind_comm
        (fixedChainMaterialRepresentation parameter chain) ($ᵗ Digest)
        (fun material root => pure ((⟨root, parameter⟩ : PublicKey),
          fixedChainMaterialTable chain material))
    _ = 𝒟[($ᵗ Digest) >>= fun root =>
          fixedChainMaterialTableOnly parameter chain >>= fun table =>
          pure ((⟨root, parameter⟩ : PublicKey), table)] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro root
      simp [fixedChainMaterialTableOnly, map_eq_bind_pure_comp, bind_assoc]
    _ = 𝒟[($ᵗ Digest) >>= fun root =>
          uniformChainValueTable chain >>= fun table =>
          pure ((⟨root, parameter⟩ : PublicKey), table)] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro root
      let finish : (ChainValueIndex → Digest) →
          ProbComp (PublicKey × (ChainValueIndex → Digest)) :=
        fun table => pure ((⟨root, parameter⟩ : PublicKey), table)
      change 𝒟[fixedChainMaterialTableOnly parameter chain >>= finish] =
        𝒟[uniformChainValueTable chain >>= finish]
      rw [evalDist_bind,
        evalDist_fixedChainMaterialTableOnly_eq_uniformChainValueTable
          parameter chain,
        ← evalDist_bind]

theorem Concrete.fixedSeedChainTrajectoriesFromCache_avoids_merkle
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (level : MerkleLevel)
    (node : MerkleNode) (input : HashInput)
    (hinput : AtHashAddress parameter (.merkle level node) input) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec)
      (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec),
      cache input = none →
      result ∈ support
        (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
          steps cache epochs) →
      result.2 input = none := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache result hcache hresult
      simp only [Concrete.fixedSeedChainTrajectoriesFromCache_nil,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hcache
  | cons epoch epochs ih =>
      intro cache result hcache hresult
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      apply ih first.2 rest
      · apply Concrete.CacheReplay.cache_none_of_zero_query_bound
          (Concrete.chainTrajectory parameter epoch chain 0 steps
            (secret epoch chain)) input cache first.2 first.1
        · apply OracleComp.IsQueryBoundP.of_imp
            (p' := AtHashAddress parameter (.merkle level node))
          · intro candidate heq
            subst candidate
            exact hinput
          · apply Concrete.chainTrajectory_queryBound_zero_of_avoids
            intro offset hoffset hvalid heq
            simp at heq
        · exact hcache
        · exact hfirst
      · exact hrest

theorem programmedFixedSeedChainTrajectories_avoids_merkle
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (result : List FullChainTrajectory × QueryCache HashSpec)
    (hresult : result ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (level : MerkleLevel) (node : MerkleNode) (input : HashInput)
    (hinput : AtHashAddress parameter (.merkle level node) input) :
    result.2 input = none := by
  have hdist := evalDist_fixedSeedChainTrajectories_eq_programmed
    parameter secret chain (chainLength - 1) le_rfl allEpochs ∅
      allEpochs_nodup (by simp)
  have hactual : result ∈ support
      (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs) :=
    (mem_support_iff_of_evalDist_eq hdist result).mpr hresult
  exact Concrete.fixedSeedChainTrajectoriesFromCache_avoids_merkle
    parameter secret chain (chainLength - 1) level node input hinput
      allEpochs ∅ result (by simp) hactual

theorem programmedWarmedTrajectory_rootTree_probability
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (htrajectory : trajectoryResult ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (target : Digest) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      (simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run trajectoryResult.2] =
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  have hheight : treeHeight = (treeHeight - 1) + 1 := by decide
  rw [hheight]
  apply Concrete.treeNode_positive_probability_from_cache
    (parameter := parameter) (secret := secret)
    (levels := treeHeight - 1) (node := Concrete.rootNode)
    (hlevel := by decide)
    (hvalid := by
      unfold TreeSubtreeValid Concrete.rootNode lifetime
      change (0 + 1) * 2 ^ (treeHeight - 1 + 1) ≤ 2 ^ treeHeight
      rw [← hheight]
      simp)
    (initialCache := trajectoryResult.2)
  intro input hinput
  exact programmedFixedSeedChainTrajectories_avoids_merkle
    parameter secret chain trajectoryResult htrajectory
      ⟨treeHeight - 1, by decide⟩ Concrete.rootNode input hinput

set_option maxRecDepth 100000 in
theorem evalDist_programmedWarmedTrajectory_root_eq_uniform
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (trajectoryResult : List FullChainTrajectory × QueryCache HashSpec)
    (htrajectory : trajectoryResult ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs)) :
    𝒟[Prod.fst <$> (simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run trajectoryResult.2] =
      𝒟[$ᵗ Digest] := by
  apply SPMF.ext
  intro target
  change Pr[= target | Prod.fst <$> (simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run trajectoryResult.2] =
    Pr[= target | $ᵗ Digest]
  rw [← probEvent_eq_eq_probOutput, probEvent_map]
  calc
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run trajectoryResult.2] =
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      programmedWarmedTrajectory_rootTree_probability parameter secret chain
        trajectoryResult htrajectory target
    _ = Pr[= target | $ᵗ Digest] := by
      rw [probOutput_uniformSample, HiddenValue.card_digest]

noncomputable def programmedWarmedTrajectoryMaterial
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp ((List Digest × FlatSecret) ×
      (List FullChainTrajectory × QueryCache HashSpec)) := do
  let secretView ← extractFixedChainSeeds chain allEpochs
  let trajectoryResult ← programmedFixedSeedChainTrajectoriesFromCache parameter
    (unflattenSecret secretView.2) chain (chainLength - 1) ∅ allEpochs
  pure (secretView, trajectoryResult)

noncomputable def programmedWarmedTrajectoryTableOnly
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (ChainValueIndex → Digest) :=
  (fun material => chainValueTableOfList material.2.1) <$>
    programmedWarmedTrajectoryMaterial parameter chain

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_programmedWarmedTrajectoryTableOnly_eq_uniformChainValueTable
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[programmedWarmedTrajectoryTableOnly parameter chain] =
      𝒟[uniformChainValueTable chain] := by
  calc
    𝒟[programmedWarmedTrajectoryTableOnly parameter chain] =
        𝒟[Concrete.extractedAllEpochChainValueTableOnly parameter chain] := by
      unfold programmedWarmedTrajectoryTableOnly
        programmedWarmedTrajectoryMaterial
        Concrete.extractedAllEpochChainValueTableOnly
        Concrete.extractedFixedChainTrajectoriesFromCache
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro secretView
      let finish : (List FullChainTrajectory × QueryCache HashSpec) →
          ProbComp (ChainValueIndex → Digest) := fun result =>
        pure (chainValueTableOfList result.1)
      change 𝒟[programmedFixedSeedChainTrajectoriesFromCache parameter
          (unflattenSecret secretView.2) chain (chainLength - 1) ∅ allEpochs >>=
            finish] =
        𝒟[Concrete.fixedSeedChainTrajectoriesFromCache parameter
          (unflattenSecret secretView.2) chain (chainLength - 1) ∅ allEpochs >>=
            finish]
      rw [evalDist_bind,
        ← evalDist_fixedSeedChainTrajectories_eq_programmed parameter
          (unflattenSecret secretView.2) chain (chainLength - 1) le_rfl
          allEpochs ∅ allEpochs_nodup (by simp),
        ← evalDist_bind]
    _ = 𝒟[Concrete.sampledAllEpochChainValueTableOnly parameter chain] := by
      unfold Concrete.extractedAllEpochChainValueTableOnly
      rw [evalDist_map,
        Concrete.evalDist_extractedFixedChainTrajectories_eq_sampled parameter
          chain (chainLength - 1) ∅ allEpochs allEpochs_nodup,
        ← evalDist_map]
      simp [Concrete.sampledAllEpochChainValueTableOnly,
        Concrete.sampledAllEpochChainValueTable,
        Concrete.sampledAllEpochChainTrajectories, Functor.map_map]
    _ = 𝒟[uniformChainValueTable chain] := by
      unfold uniformChainValueTable
      apply SPMF.ext
      intro target
      change Pr[= target |
          Concrete.sampledAllEpochChainValueTableOnly parameter chain] =
        Pr[= target | Concrete.sampledAllEpochChainValueTableOnly 0 chain]
      rw [Concrete.sampledAllEpochChainValueTableOnly_probability,
        Concrete.sampledAllEpochChainValueTableOnly_probability]

theorem programmedWarmedTrajectoryMaterial_support_trajectory
    (parameter : PublicParameter) (chain : ChainIndex)
    (material : (List Digest × FlatSecret) ×
      (List FullChainTrajectory × QueryCache HashSpec))
    (hmaterial : material ∈ support
      (programmedWarmedTrajectoryMaterial parameter chain)) :
    material.2 ∈ support
      (programmedFixedSeedChainTrajectoriesFromCache parameter
        (unflattenSecret material.1.2) chain (chainLength - 1) ∅
        allEpochs) := by
  unfold programmedWarmedTrajectoryMaterial at hmaterial
  rw [mem_support_bind_iff] at hmaterial
  obtain ⟨secretView, _hsecretView, htrajectory⟩ := hmaterial
  rw [mem_support_bind_iff] at htrajectory
  obtain ⟨trajectoryResult, htrajectoryResult, hpure⟩ := htrajectory
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst material
  exact htrajectoryResult

set_option maxRecDepth 100000 in
theorem evalDist_programmedWarmedTrajectoryMaterial_root_eq_uniform
    (parameter : PublicParameter) (chain : ChainIndex)
    (material : (List Digest × FlatSecret) ×
      (List FullChainTrajectory × QueryCache HashSpec))
    (hmaterial : material ∈ support
      (programmedWarmedTrajectoryMaterial parameter chain)) :
    𝒟[Prod.fst <$> (simulateQ randomOracle
      (Concrete.treeNode parameter (unflattenSecret material.1.2)
        treeHeight Concrete.rootNode : OracleComp HashSpec Digest)).run
          material.2.2] =
      𝒟[$ᵗ Digest] :=
  evalDist_programmedWarmedTrajectory_root_eq_uniform parameter
    (unflattenSecret material.1.2) chain material.2
      (programmedWarmedTrajectoryMaterial_support_trajectory parameter chain
        material hmaterial)

noncomputable def programmedWarmedFixedChainPublicTableView
    (chain : ChainIndex) : ProbComp (PublicKey × (ChainValueIndex → Digest)) :=
  (fun result : ProgrammedFixedChainKeygenView =>
    (result.publicKey, result.table)) <$> programmedWarmedFixedChainKeygen chain

noncomputable def programmedWarmedFixedChainPublicTableExperiment
    (chain : ChainIndex) : ProbComp (PublicKey × (ChainValueIndex → Digest)) := do
  let parameter ← Concrete.samplePublicParameter
  let material ← programmedWarmedTrajectoryMaterial parameter chain
  let rootResult ← (simulateQ randomOracle
    (Concrete.treeNode parameter (unflattenSecret material.1.2)
      treeHeight Concrete.rootNode : OracleComp HashSpec Digest)).run
        material.2.2
  pure (⟨rootResult.1, parameter⟩,
    chainValueTableOfList material.2.1)

theorem programmedWarmedFixedChainPublicTableView_eq_experiment
    (chain : ChainIndex) :
    programmedWarmedFixedChainPublicTableView chain =
      programmedWarmedFixedChainPublicTableExperiment chain := by
  simp [programmedWarmedFixedChainPublicTableView,
    programmedWarmedFixedChainPublicTableExperiment,
    programmedWarmedFixedChainKeygen, programmedWarmedTrajectoryMaterial,
    map_eq_bind_pure_comp, bind_assoc]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_programmedWarmedFixedChainPublicTableView_eq_independent
    (chain : ChainIndex) :
    𝒟[programmedWarmedFixedChainPublicTableView chain] =
      𝒟[independentFixedChainPublicTableView chain] := by
  rw [programmedWarmedFixedChainPublicTableView_eq_experiment]
  unfold programmedWarmedFixedChainPublicTableExperiment
    independentFixedChainPublicTableView
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  calc
    𝒟[programmedWarmedTrajectoryMaterial parameter chain >>= fun material =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter (unflattenSecret material.1.2)
            treeHeight Concrete.rootNode : OracleComp HashSpec Digest)).run
              material.2.2 >>= fun rootResult =>
        pure ((⟨rootResult.1, parameter⟩ : PublicKey),
          chainValueTableOfList material.2.1)] =
      𝒟[programmedWarmedTrajectoryMaterial parameter chain >>= fun material =>
        ($ᵗ Digest) >>= fun root =>
        pure ((⟨root, parameter⟩ : PublicKey),
          chainValueTableOfList material.2.1)] := by
      apply evalDist_bind_congr
      intro material hmaterial
      calc
        𝒟[(simulateQ randomOracle
              (Concrete.treeNode parameter (unflattenSecret material.1.2)
                treeHeight Concrete.rootNode : OracleComp HashSpec Digest)).run
                  material.2.2 >>= fun rootResult =>
            pure ((⟨rootResult.1, parameter⟩ : PublicKey),
              chainValueTableOfList material.2.1)] =
          𝒟[(Prod.fst <$> (simulateQ randomOracle
              (Concrete.treeNode parameter (unflattenSecret material.1.2)
                treeHeight Concrete.rootNode : OracleComp HashSpec Digest)).run
                  material.2.2) >>= fun root =>
            pure ((⟨root, parameter⟩ : PublicKey),
              chainValueTableOfList material.2.1)] := by
            simp [map_eq_bind_pure_comp, bind_assoc]
        _ = 𝒟[($ᵗ Digest) >>= fun root =>
              pure ((⟨root, parameter⟩ : PublicKey),
                chainValueTableOfList material.2.1)] := by
            rw [evalDist_bind,
              evalDist_programmedWarmedTrajectoryMaterial_root_eq_uniform
                parameter chain material hmaterial,
              ← evalDist_bind]
    _ = 𝒟[($ᵗ Digest) >>= fun root =>
          programmedWarmedTrajectoryMaterial parameter chain >>= fun material =>
          pure ((⟨root, parameter⟩ : PublicKey),
            chainValueTableOfList material.2.1)] :=
      OracleComp.DeferredSampling.evalDist_bind_comm
        (programmedWarmedTrajectoryMaterial parameter chain) ($ᵗ Digest)
        (fun material root => pure ((⟨root, parameter⟩ : PublicKey),
          chainValueTableOfList material.2.1))
    _ = 𝒟[($ᵗ Digest) >>= fun root =>
          programmedWarmedTrajectoryTableOnly parameter chain >>= fun table =>
          pure ((⟨root, parameter⟩ : PublicKey), table)] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro root
      simp [programmedWarmedTrajectoryTableOnly, map_eq_bind_pure_comp,
        bind_assoc]
    _ = 𝒟[($ᵗ Digest) >>= fun root =>
          uniformChainValueTable chain >>= fun table =>
          pure ((⟨root, parameter⟩ : PublicKey), table)] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro root
      let finish : (ChainValueIndex → Digest) →
          ProbComp (PublicKey × (ChainValueIndex → Digest)) := fun table =>
        pure ((⟨root, parameter⟩ : PublicKey), table)
      change 𝒟[programmedWarmedTrajectoryTableOnly parameter chain >>= finish] =
        𝒟[uniformChainValueTable chain >>= finish]
      rw [evalDist_bind,
        evalDist_programmedWarmedTrajectoryTableOnly_eq_uniformChainValueTable
          parameter chain,
        ← evalDist_bind]

noncomputable def actualFixedChainPublicTableView
    (chain : ChainIndex) : ProbComp (PublicKey × (ChainValueIndex → Digest)) :=
  (fun result : ProgrammedFixedChainKeygenView =>
    (result.publicKey, result.table)) <$> actualFixedChainKeygen chain

theorem evalDist_actualFixedChainPublicTableView_eq_independent
  (chain : ChainIndex) :
    𝒟[actualFixedChainPublicTableView chain] =
      𝒟[independentFixedChainPublicTableView chain] := by
  unfold actualFixedChainPublicTableView
  calc
    𝒟[(fun result : ProgrammedFixedChainKeygenView =>
          (result.publicKey, result.table)) <$>
        actualFixedChainKeygen chain] =
      𝒟[(fun result : ProgrammedFixedChainKeygenView =>
          (result.publicKey, result.table)) <$>
        programmedWarmedFixedChainKeygen chain] := by
      rw [evalDist_map,
        evalDist_actualFixedChainKeygen_eq_programmedWarmed chain,
        ← evalDist_map]
    _ = 𝒟[independentFixedChainPublicTableView chain] :=
      evalDist_programmedWarmedFixedChainPublicTableView_eq_independent chain

end XmssSecurity
