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

noncomputable def fixedChainOutsideTableView
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (OutsideChainSecret chain × (ChainValueIndex → Digest)) :=
  (fun material =>
    (outsideChainSecret chain material.1.2,
      fixedChainMaterialTable chain material)) <$>
        fixedChainMaterialRepresentation parameter chain

noncomputable def independentOutsideTableView (chain : ChainIndex) :
    ProbComp (OutsideChainSecret chain × (ChainValueIndex → Digest)) := do
  let outside ← $ᵗ (OutsideChainSecret chain)
  let table ← uniformChainValueTable chain
  pure (outside, table)

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

end XmssSecurity
