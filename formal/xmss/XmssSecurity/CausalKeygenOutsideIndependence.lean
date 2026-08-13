import XmssSecurity.CausalKeygenTableIndependence

open OracleComp OracleSpec

namespace XmssSecurity

abbrev OtherChainIndex (chain : ChainIndex) :=
  {candidate : ChainIndex // candidate ≠ chain}

abbrev OutsideChainSecret (chain : ChainIndex) :=
  Epoch → OtherChainIndex chain → Digest

def outsideChainSecret (chain : ChainIndex) (secret : FlatSecret) :
    OutsideChainSecret chain := fun epoch candidate =>
  secret (epoch, candidate.1)

def flatSecretOfOutsideAndSeeds
    (chain : ChainIndex) (outside : OutsideChainSecret chain)
    (seeds : Epoch → Digest) : FlatSecret := fun index =>
  if heq : index.2 = chain then seeds index.1
  else outside index.1 ⟨index.2, heq⟩

def outsideChainSecretSeedEquiv (chain : ChainIndex) :
    FlatSecret ≃ (OutsideChainSecret chain × (Epoch → Digest)) where
  toFun secret :=
    (outsideChainSecret chain secret, fun epoch => secret (epoch, chain))
  invFun material :=
    flatSecretOfOutsideAndSeeds chain material.1 material.2
  left_inv secret := by
    funext index
    rcases index with ⟨epoch, candidate⟩
    by_cases heq : candidate = chain
    · subst candidate
      simp [flatSecretOfOutsideAndSeeds]
    · simp [flatSecretOfOutsideAndSeeds, outsideChainSecret, heq]
  right_inv material := by
    apply Prod.ext
    · funext epoch candidate
      simp [outsideChainSecret, flatSecretOfOutsideAndSeeds,
        candidate.property]
    · funext epoch
      simp [flatSecretOfOutsideAndSeeds]

def outsideChainTableMaterialEquiv (chain : ChainIndex) :
    (FlatSecret × (ChainEdgeIndex → Digest)) ≃
      (OutsideChainSecret chain × (ChainValueIndex → Digest)) where
  toFun material :=
    (outsideChainSecret chain material.1,
      chainTableMaterialEquiv.symm
        ((fun epoch => material.1 (epoch, chain)), material.2))
  invFun material :=
    let chainMaterial := chainTableMaterialEquiv material.2
    (flatSecretOfOutsideAndSeeds chain material.1 chainMaterial.1,
      chainMaterial.2)
  left_inv material := by
    apply Prod.ext
    · funext index
      rcases index with ⟨epoch, candidate⟩
      by_cases heq : candidate = chain
      · subst candidate
        simp [flatSecretOfOutsideAndSeeds]
      · simp [flatSecretOfOutsideAndSeeds, outsideChainSecret, heq]
    · simp
  right_inv material := by
    apply Prod.ext
    · funext epoch candidate
      simp [outsideChainSecret, flatSecretOfOutsideAndSeeds,
        candidate.property]
    · let chainMaterial := chainTableMaterialEquiv material.2
      have hseeds :
          (fun epoch => flatSecretOfOutsideAndSeeds chain material.1
            chainMaterial.1 (epoch, chain)) = chainMaterial.1 := by
        funext epoch
        simp [flatSecretOfOutsideAndSeeds]
      change chainTableMaterialEquiv.symm
          ((fun epoch => flatSecretOfOutsideAndSeeds chain material.1
            chainMaterial.1 (epoch, chain)), chainMaterial.2) = material.2
      rw [hseeds]
      exact chainTableMaterialEquiv.symm_apply_apply material.2

noncomputable local instance outsideIndependenceSampleableFlatSecret :
    SampleableType FlatSecret :=
  SampleableType.ofFintype FlatSecret

noncomputable local instance outsideIndependenceSampleableEdges :
    SampleableType (ChainEdgeIndex → Digest) :=
  SampleableType.ofFintype (ChainEdgeIndex → Digest)

noncomputable local instance outsideIndependenceSampleableSeeds :
    SampleableType (Epoch → Digest) :=
  SampleableType.ofFintype (Epoch → Digest)

noncomputable local instance outsideIndependenceSampleableOutside
    (chain : ChainIndex) : SampleableType (OutsideChainSecret chain) :=
  SampleableType.ofFintype (OutsideChainSecret chain)

noncomputable local instance outsideIndependenceSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

noncomputable def independentOutsideSource :
    ProbComp (FlatSecret × (ChainEdgeIndex → Digest)) :=
  Prod.mk <$> ($ᵗ FlatSecret) <*> ($ᵗ (ChainEdgeIndex → Digest))

theorem evalDist_independentOutsideSource_eq_uniform :
    𝒟[independentOutsideSource] =
      𝒟[$ᵗ (FlatSecret × (ChainEdgeIndex → Digest))] := by
  apply SPMF.ext
  intro target
  change Pr[= target | independentOutsideSource] =
    Pr[= target | $ᵗ (FlatSecret × (ChainEdgeIndex → Digest))]
  unfold independentOutsideSource
  rw [probOutput_seq_map_prod_mk_eq_mul, probOutput_uniformSample,
    probOutput_uniformSample, probOutput_uniformSample, Fintype.card_prod,
    Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]

noncomputable def independentOutsideTarget (chain : ChainIndex) :
    ProbComp (OutsideChainSecret chain × (ChainValueIndex → Digest)) :=
  Prod.mk <$> ($ᵗ (OutsideChainSecret chain)) <*>
    ($ᵗ (ChainValueIndex → Digest))

theorem evalDist_independentOutsideTarget_eq_uniform (chain : ChainIndex) :
    𝒟[independentOutsideTarget chain] =
      𝒟[$ᵗ (OutsideChainSecret chain ×
        (ChainValueIndex → Digest))] := by
  apply SPMF.ext
  intro target
  change Pr[= target | independentOutsideTarget chain] =
    Pr[= target | $ᵗ (OutsideChainSecret chain ×
      (ChainValueIndex → Digest))]
  unfold independentOutsideTarget
  rw [probOutput_seq_map_prod_mk_eq_mul, probOutput_uniformSample,
    probOutput_uniformSample, probOutput_uniformSample, Fintype.card_prod,
    Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]

noncomputable def splitOutsideSeeds (chain : ChainIndex) :
    ProbComp (OutsideChainSecret chain × (Epoch → Digest)) :=
  outsideChainSecretSeedEquiv chain <$> ($ᵗ FlatSecret)

noncomputable def independentOutsideSeeds (chain : ChainIndex) :
    ProbComp (OutsideChainSecret chain × (Epoch → Digest)) :=
  Prod.mk <$> ($ᵗ (OutsideChainSecret chain)) <*> ($ᵗ (Epoch → Digest))

theorem evalDist_splitOutsideSeeds_eq_independent (chain : ChainIndex) :
    𝒟[splitOutsideSeeds chain] = 𝒟[independentOutsideSeeds chain] := by
  calc
    𝒟[splitOutsideSeeds chain] =
        𝒟[$ᵗ (OutsideChainSecret chain × (Epoch → Digest))] := by
      unfold splitOutsideSeeds
      exact evalDist_map_bijective_uniform_cross
        (α := FlatSecret)
        (β := OutsideChainSecret chain × (Epoch → Digest))
        (outsideChainSecretSeedEquiv chain)
        (outsideChainSecretSeedEquiv chain).bijective
    _ = 𝒟[independentOutsideSeeds chain] := by
      symm
      apply SPMF.ext
      intro target
      change Pr[= target | independentOutsideSeeds chain] =
        Pr[= target | $ᵗ (OutsideChainSecret chain × (Epoch → Digest))]
      unfold independentOutsideSeeds
      rw [probOutput_seq_map_prod_mk_eq_mul, probOutput_uniformSample,
        probOutput_uniformSample, probOutput_uniformSample, Fintype.card_prod,
        Nat.cast_mul,
        ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
          (Or.inl (ENNReal.natCast_ne_top _))]

def secretFromOutsideSeeds (chain : ChainIndex)
    (outside : OutsideChainSecret chain) (seeds : Epoch → Digest) :
    Epoch → ChainIndex → Digest :=
  unflattenSecret (flatSecretOfOutsideAndSeeds chain outside seeds)

@[simp]
theorem secretFromOutsideSeeds_fixed (chain : ChainIndex)
    (outside : OutsideChainSecret chain) (seeds : Epoch → Digest)
    (epoch : Epoch) :
    secretFromOutsideSeeds chain outside seeds epoch chain = seeds epoch := by
  simp [secretFromOutsideSeeds, unflattenSecret,
    flatSecretOfOutsideAndSeeds]

def zeroOutsideChainSecret (chain : ChainIndex) : OutsideChainSecret chain :=
  fun _epoch _candidate => 0

noncomputable def programmedTableFromSeeds
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (ChainValueIndex → Digest) := do
  let seeds ← $ᵗ (Epoch → Digest)
  let secret := secretFromOutsideSeeds chain
    (zeroOutsideChainSecret chain) seeds
  let trajectories ← programmedFixedSeedChainTrajectoriesFromCache
    parameter secret chain (chainLength - 1) ∅ allEpochs
  pure (chainValueTableOfList trajectories.1)

theorem programmedTableFromSeeds_eq
    (parameter : PublicParameter) (chain : ChainIndex) :
    programmedTableFromSeeds parameter chain = (do
      let seeds ← $ᵗ (Epoch → Digest)
      let trajectories ← programmedFixedSeedChainTrajectoriesFromCache
        parameter (secretFromOutsideSeeds chain
          (zeroOutsideChainSecret chain) seeds) chain
            (chainLength - 1) ∅ allEpochs
      pure (chainValueTableOfList trajectories.1)) := rfl

noncomputable def programmedWarmedOutsideTableView
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (OutsideChainSecret chain × (ChainValueIndex → Digest)) :=
  (fun material =>
    (outsideChainSecret chain material.1.2,
      chainValueTableOfList material.2.1)) <$>
        programmedWarmedTrajectoryMaterial parameter chain

noncomputable def normalizedProgrammedOutsideTableView
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (OutsideChainSecret chain × (ChainValueIndex → Digest)) := do
  let table ← programmedTableFromSeeds parameter chain
  let outside ← $ᵗ (OutsideChainSecret chain)
  pure (outside, table)

noncomputable def independentOutsideTableView (chain : ChainIndex) :
    ProbComp (OutsideChainSecret chain × (ChainValueIndex → Digest)) := do
  let outside ← $ᵗ (OutsideChainSecret chain)
  let table ← uniformChainValueTable chain
  pure (outside, table)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_programmedWarmedOutsideTableView_eq_normalized
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[programmedWarmedOutsideTableView parameter chain] =
      𝒟[normalizedProgrammedOutsideTableView parameter chain] := by
  unfold programmedWarmedOutsideTableView programmedWarmedTrajectoryMaterial
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  calc
    𝒟[extractFixedChainSeeds chain allEpochs >>= fun secretView =>
        programmedFixedSeedChainTrajectoriesFromCache parameter
            (unflattenSecret secretView.2) chain (chainLength - 1) ∅
              allEpochs >>= fun trajectories =>
          pure (outsideChainSecret chain secretView.2,
            chainValueTableOfList trajectories.1)] =
      𝒟[(fixedChainSeedView chain allEpochs <$>
          ($ᵗ FlatSecret)) >>= fun secretView =>
        programmedFixedSeedChainTrajectoriesFromCache parameter
            (unflattenSecret secretView.2) chain (chainLength - 1) ∅
              allEpochs >>= fun trajectories =>
          pure (outsideChainSecret chain secretView.2,
            chainValueTableOfList trajectories.1)] := by
        rw [evalDist_bind,
          evalDist_extractFixedChainSeeds_eq_uniform chain allEpochs
            allEpochs_nodup,
          ← evalDist_bind]
    _ = 𝒟[($ᵗ FlatSecret) >>= fun flatSecret =>
        programmedFixedSeedChainTrajectoriesFromCache parameter
            (unflattenSecret flatSecret) chain (chainLength - 1) ∅
              allEpochs >>= fun trajectories =>
          pure (outsideChainSecret chain flatSecret,
            chainValueTableOfList trajectories.1)] := by
      simp [fixedChainSeedView, map_eq_bind_pure_comp, bind_assoc]
    _ = 𝒟[splitOutsideSeeds chain >>= fun split =>
        programmedFixedSeedChainTrajectoriesFromCache parameter
            (secretFromOutsideSeeds chain split.1 split.2) chain
              (chainLength - 1) ∅ allEpochs >>= fun trajectories =>
          pure (split.1, chainValueTableOfList trajectories.1)] := by
      unfold splitOutsideSeeds secretFromOutsideSeeds
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro flatSecret
      have hflat := (outsideChainSecretSeedEquiv chain).symm_apply_apply flatSecret
      change flatSecretOfOutsideAndSeeds chain
          ((outsideChainSecretSeedEquiv chain flatSecret).1)
          ((outsideChainSecretSeedEquiv chain flatSecret).2) =
        flatSecret at hflat
      have houtside : (outsideChainSecretSeedEquiv chain flatSecret).1 =
          outsideChainSecret chain flatSecret := rfl
      rw [hflat]
      rw [houtside]
    _ = 𝒟[independentOutsideSeeds chain >>= fun split =>
        programmedFixedSeedChainTrajectoriesFromCache parameter
            (secretFromOutsideSeeds chain split.1 split.2) chain
              (chainLength - 1) ∅ allEpochs >>= fun trajectories =>
          pure (split.1, chainValueTableOfList trajectories.1)] := by
      rw [evalDist_bind, evalDist_splitOutsideSeeds_eq_independent chain,
        ← evalDist_bind]
    _ = 𝒟[($ᵗ (OutsideChainSecret chain)) >>= fun outside =>
        ($ᵗ (Epoch → Digest)) >>= fun seeds =>
          programmedFixedSeedChainTrajectoriesFromCache parameter
              (secretFromOutsideSeeds chain outside seeds) chain
                (chainLength - 1) ∅ allEpochs >>= fun trajectories =>
            pure (outside, chainValueTableOfList trajectories.1)] := by
      simp [independentOutsideSeeds, monad_norm]
    _ = 𝒟[($ᵗ (OutsideChainSecret chain)) >>= fun outside =>
        ($ᵗ (Epoch → Digest)) >>= fun seeds =>
          programmedFixedSeedChainTrajectoriesFromCache parameter
              (secretFromOutsideSeeds chain (zeroOutsideChainSecret chain)
                seeds) chain (chainLength - 1) ∅ allEpochs >>=
            fun trajectories =>
              pure (outside, chainValueTableOfList trajectories.1)] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro outside
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro seeds
      have hagrees : ∀ epoch ∈ allEpochs,
          secretFromOutsideSeeds chain outside seeds epoch chain =
            secretFromOutsideSeeds chain (zeroOutsideChainSecret chain)
              seeds epoch chain := by
        intro epoch _hepoch
        rw [secretFromOutsideSeeds_fixed,
          secretFromOutsideSeeds_fixed]
      rw [programmedFixedSeedChainTrajectoriesFromCache_congr_secret
        parameter (secretFromOutsideSeeds chain outside seeds)
          (secretFromOutsideSeeds chain (zeroOutsideChainSecret chain) seeds)
            chain (chainLength - 1) allEpochs ∅ hagrees]
    _ = 𝒟[($ᵗ (OutsideChainSecret chain)) >>= fun outside =>
        programmedTableFromSeeds parameter chain >>= fun table =>
          pure (outside, table)] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro outside
      rw [programmedTableFromSeeds_eq]
      simp
    _ = 𝒟[normalizedProgrammedOutsideTableView parameter chain] := by
      unfold normalizedProgrammedOutsideTableView
      exact OracleComp.DeferredSampling.evalDist_bind_comm
        ($ᵗ (OutsideChainSecret chain))
        (programmedTableFromSeeds parameter chain)
        (fun outside table => pure (outside, table))

set_option linter.constructorNameAsVariable false in
theorem evalDist_normalizedProgrammedOutsideTableView_snd
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[Prod.snd <$>
        normalizedProgrammedOutsideTableView parameter chain] =
      𝒟[programmedTableFromSeeds parameter chain] := by
  unfold normalizedProgrammedOutsideTableView
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  calc
    𝒟[programmedTableFromSeeds parameter chain >>= fun table =>
        ($ᵗ (OutsideChainSecret chain)) >>= fun _outside => pure table] =
      𝒟[programmedTableFromSeeds parameter chain >>= fun table =>
        pure table] := by
          apply evalDist_bind_congr
          intro table _htable
          exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
            ($ᵗ (OutsideChainSecret chain))
            (probFailure_eq_zero' inferInstance) (pure table)
    _ = 𝒟[programmedTableFromSeeds parameter chain] := by simp

theorem evalDist_programmedWarmedOutsideTableView_snd
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[Prod.snd <$>
        programmedWarmedOutsideTableView parameter chain] =
      𝒟[programmedWarmedTrajectoryTableOnly parameter chain] := by
  unfold programmedWarmedOutsideTableView
    programmedWarmedTrajectoryTableOnly
  simp [Functor.map_map]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_programmedTableFromSeeds_eq_uniformChainValueTable
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[programmedTableFromSeeds parameter chain] =
      𝒟[uniformChainValueTable chain] := by
  calc
    𝒟[programmedTableFromSeeds parameter chain] =
        𝒟[Prod.snd <$>
          normalizedProgrammedOutsideTableView parameter chain] :=
      (evalDist_normalizedProgrammedOutsideTableView_snd
        parameter chain).symm
    _ = 𝒟[Prod.snd <$>
          programmedWarmedOutsideTableView parameter chain] := by
      rw [evalDist_map,
        ← evalDist_programmedWarmedOutsideTableView_eq_normalized
          parameter chain,
        ← evalDist_map]
    _ = 𝒟[programmedWarmedTrajectoryTableOnly parameter chain] :=
      evalDist_programmedWarmedOutsideTableView_snd parameter chain
    _ = 𝒟[uniformChainValueTable chain] :=
      evalDist_programmedWarmedTrajectoryTableOnly_eq_uniformChainValueTable
        parameter chain

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_programmedWarmedOutsideTableView_eq_independent
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[programmedWarmedOutsideTableView parameter chain] =
      𝒟[independentOutsideTableView chain] := by
  calc
    𝒟[programmedWarmedOutsideTableView parameter chain] =
        𝒟[normalizedProgrammedOutsideTableView parameter chain] :=
      evalDist_programmedWarmedOutsideTableView_eq_normalized parameter chain
    _ = 𝒟[uniformChainValueTable chain >>= fun table =>
          ($ᵗ (OutsideChainSecret chain)) >>= fun outside =>
            pure (outside, table)] := by
      unfold normalizedProgrammedOutsideTableView
      rw [evalDist_bind,
        evalDist_programmedTableFromSeeds_eq_uniformChainValueTable
          parameter chain,
        ← evalDist_bind]
    _ = 𝒟[($ᵗ (OutsideChainSecret chain)) >>= fun outside =>
          uniformChainValueTable chain >>= fun table =>
            pure (outside, table)] :=
      OracleComp.DeferredSampling.evalDist_bind_comm
        (uniformChainValueTable chain) ($ᵗ (OutsideChainSecret chain))
          (fun table outside => pure (outside, table))
    _ = 𝒟[independentOutsideTableView chain] := rfl

noncomputable def programmedWarmedOutsideOnly
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (OutsideChainSecret chain) :=
  (fun material => outsideChainSecret chain material.1.2) <$>
    programmedWarmedTrajectoryMaterial parameter chain

set_option linter.constructorNameAsVariable false in
theorem evalDist_programmedWarmedOutsideOnly_eq_uniform
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[programmedWarmedOutsideOnly parameter chain] =
      𝒟[$ᵗ (OutsideChainSecret chain)] := by
  calc
    𝒟[programmedWarmedOutsideOnly parameter chain] =
        𝒟[Prod.fst <$>
          programmedWarmedOutsideTableView parameter chain] := by
      unfold programmedWarmedOutsideOnly programmedWarmedOutsideTableView
      simp [Functor.map_map]
    _ = 𝒟[Prod.fst <$> independentOutsideTableView chain] := by
      rw [evalDist_map,
        evalDist_programmedWarmedOutsideTableView_eq_independent
          parameter chain,
        ← evalDist_map]
    _ = 𝒟[$ᵗ (OutsideChainSecret chain)] := by
      unfold independentOutsideTableView
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      calc
        𝒟[($ᵗ (OutsideChainSecret chain)) >>= fun outside =>
            uniformChainValueTable chain >>= fun _table => pure outside] =
          𝒟[($ᵗ (OutsideChainSecret chain)) >>= fun outside =>
            pure outside] := by
              apply evalDist_bind_congr
              intro outside _houtside
              exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                (uniformChainValueTable chain)
                (probFailure_eq_zero' inferInstance) (pure outside)
        _ = 𝒟[$ᵗ (OutsideChainSecret chain)] := by simp

noncomputable def fixedChainOutsideTableView
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (OutsideChainSecret chain × (ChainValueIndex → Digest)) :=
  (fun material =>
    (outsideChainSecret chain material.1.2,
      fixedChainMaterialTable chain material)) <$>
        fixedChainMaterialRepresentation parameter chain

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_fixedChainOutsideTableView_eq_independent
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[fixedChainOutsideTableView parameter chain] =
      𝒟[independentOutsideTableView chain] := by
  unfold fixedChainOutsideTableView fixedChainMaterialRepresentation
    fixedChainMaterialTable independentOutsideTableView
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  calc
    𝒟[extractFixedChainSeeds chain allEpochs >>= fun secretView =>
        uniformInstalledChainEdgeCache parameter chain
            (fun epoch => secretView.2 (epoch, chain)) >>= fun edgeView =>
          pure (outsideChainSecret chain secretView.2,
            chainTableMaterialEquiv.symm
              ((fun epoch => secretView.2 (epoch, chain)),
                chainEdgeTableOfTape edgeView.1))] =
      𝒟[extractFixedChainSeeds chain allEpochs >>= fun secretView =>
        ($ᵗ (ChainEdgeIndex → Digest)) >>= fun edges =>
          pure (outsideChainSecret chain secretView.2,
            chainTableMaterialEquiv.symm
              ((fun epoch => secretView.2 (epoch, chain)), edges))] := by
        apply OracleComp.DeferredSampling.evalDist_bind_congr_left
        intro secretView
        let finish : (ChainEdgeIndex → Digest) →
            ProbComp (OutsideChainSecret chain ×
              (ChainValueIndex → Digest)) := fun edges =>
          pure (outsideChainSecret chain secretView.2,
            chainTableMaterialEquiv.symm
              ((fun epoch => secretView.2 (epoch, chain)), edges))
        calc
          𝒟[uniformInstalledChainEdgeCache parameter chain
                (fun epoch => secretView.2 (epoch, chain)) >>= fun edgeView =>
              finish (chainEdgeTableOfTape edgeView.1)] =
            𝒟[((fun edgeView :
                List Digest × (List HashOutput × QueryCache HashSpec) =>
                  chainEdgeTableOfTape edgeView.1) <$>
                    uniformInstalledChainEdgeCache parameter chain
                      (fun epoch => secretView.2 (epoch, chain))) >>= finish] := by
              simp [map_eq_bind_pure_comp, bind_assoc]
          _ = 𝒟[($ᵗ (ChainEdgeIndex → Digest)) >>= finish] := by
            rw [evalDist_bind,
              evalDist_uniformInstalledChainEdgeTable_eq_uniform parameter chain
                (fun epoch => secretView.2 (epoch, chain)),
              ← evalDist_bind]
    _ = 𝒟[($ᵗ FlatSecret) >>= fun secret =>
        ($ᵗ (ChainEdgeIndex → Digest)) >>= fun edges =>
          pure (outsideChainTableMaterialEquiv chain (secret, edges))] := by
      rw [evalDist_bind,
        evalDist_extractFixedChainSeeds_eq_uniform chain allEpochs
          allEpochs_nodup,
        ← evalDist_bind]
      simp [fixedChainSeedView, outsideChainTableMaterialEquiv]
    _ = 𝒟[outsideChainTableMaterialEquiv chain <$>
          independentOutsideSource] := by
      simp [independentOutsideSource, monad_norm]
    _ = 𝒟[outsideChainTableMaterialEquiv chain <$>
          ($ᵗ (FlatSecret × (ChainEdgeIndex → Digest)))] := by
      rw [evalDist_map, evalDist_independentOutsideSource_eq_uniform,
        ← evalDist_map]
    _ = 𝒟[$ᵗ (OutsideChainSecret chain ×
          (ChainValueIndex → Digest))] :=
      evalDist_map_bijective_uniform_cross
        (α := FlatSecret × (ChainEdgeIndex → Digest))
        (β := OutsideChainSecret chain × (ChainValueIndex → Digest))
        (outsideChainTableMaterialEquiv chain)
        (outsideChainTableMaterialEquiv chain).bijective
    _ = 𝒟[independentOutsideTarget chain] :=
      (evalDist_independentOutsideTarget_eq_uniform chain).symm
    _ = 𝒟[($ᵗ (OutsideChainSecret chain)) >>= fun outside =>
          ($ᵗ (ChainValueIndex → Digest)) >>= fun table =>
            pure (outside, table)] := by
      simp [independentOutsideTarget, monad_norm]
    _ = 𝒟[($ᵗ (OutsideChainSecret chain)) >>= fun outside =>
          uniformChainValueTable chain >>= fun table =>
            pure (outside, table)] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro outside
      unfold uniformChainValueTable
      rw [evalDist_bind,
        ← Concrete.evalDist_sampledAllEpochChainValueTableOnly_eq_uniform
          0 chain,
        ← evalDist_bind]

noncomputable def fixedChainOutsideOnly
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (OutsideChainSecret chain) :=
  (fun material => outsideChainSecret chain material.1.2) <$>
    fixedChainMaterialRepresentation parameter chain

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_fixedChainOutsideOnly_eq_uniform
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[fixedChainOutsideOnly parameter chain] =
      𝒟[$ᵗ (OutsideChainSecret chain)] := by
  calc
    𝒟[fixedChainOutsideOnly parameter chain] =
        𝒟[Prod.fst <$> fixedChainOutsideTableView parameter chain] := by
      unfold fixedChainOutsideOnly fixedChainOutsideTableView
      simp [Functor.map_map]
    _ = 𝒟[Prod.fst <$> independentOutsideTableView chain] := by
      rw [evalDist_map,
        evalDist_fixedChainOutsideTableView_eq_independent parameter chain,
        ← evalDist_map]
    _ = 𝒟[$ᵗ (OutsideChainSecret chain)] := by
      unfold independentOutsideTableView
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      calc
        𝒟[($ᵗ (OutsideChainSecret chain)) >>= fun outside =>
            uniformChainValueTable chain >>= fun _table => pure outside] =
          𝒟[($ᵗ (OutsideChainSecret chain)) >>= fun outside =>
            pure outside] := by
              apply evalDist_bind_congr
              intro outside _houtside
              exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                (uniformChainValueTable chain)
                (probFailure_eq_zero' inferInstance) (pure outside)
        _ = 𝒟[$ᵗ (OutsideChainSecret chain)] := by simp

noncomputable def fixedChainMaterialWithBase
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (((List Digest × FlatSecret) ×
      (List Digest × (List HashOutput × QueryCache HashSpec))) ×
        (ChainValueIndex → Digest)) := do
  let material ← fixedChainMaterialRepresentation parameter chain
  let base ← uniformChainValueTable chain
  pure (material, base)

def fixedChainMaterialBaseView (chain : ChainIndex)
    (result : ((List Digest × FlatSecret) ×
      (List Digest × (List HashOutput × QueryCache HashSpec))) ×
        (ChainValueIndex → Digest)) :
    OutsideChainSecret chain × (ChainValueIndex → Digest) :=
  (outsideChainSecret chain result.1.1.2, result.2)

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem evalDist_fixedChainMaterialOutsideTable_eq_baseView
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[fixedChainOutsideTableView parameter chain] =
      𝒟[fixedChainMaterialBaseView chain <$>
        fixedChainMaterialWithBase parameter chain] := by
  calc
    𝒟[fixedChainOutsideTableView parameter chain] =
        𝒟[independentOutsideTableView chain] :=
      evalDist_fixedChainOutsideTableView_eq_independent parameter chain
    _ = 𝒟[fixedChainOutsideOnly parameter chain >>= fun outside =>
          uniformChainValueTable chain >>= fun base =>
            pure (outside, base)] := by
      unfold independentOutsideTableView
      rw [evalDist_bind,
        ← evalDist_fixedChainOutsideOnly_eq_uniform parameter chain,
        ← evalDist_bind]
    _ = 𝒟[fixedChainMaterialBaseView chain <$>
          fixedChainMaterialWithBase parameter chain] := by
      simp [fixedChainOutsideOnly, fixedChainMaterialWithBase,
        fixedChainMaterialBaseView, map_eq_bind_pure_comp, bind_assoc]

end XmssSecurity
