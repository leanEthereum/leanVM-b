import XmssSecurity.Proof.CappedGlobalChainTable
import XmssSecurity.Proof.ChainTablePresampling

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

abbrev GlobalChainEdgeIndex := ChainIndex × ChainEdgeIndex

noncomputable local instance globalPresamplingSampleableTable :
    SampleableType (GlobalChainValueIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainValueIndex → Digest)

noncomputable local instance globalPresamplingSampleableSeeds :
    SampleableType (Epoch → ChainIndex → Digest) :=
  SampleableType.ofFintype (Epoch → ChainIndex → Digest)

noncomputable local instance globalPresamplingSampleableEdges :
    SampleableType (GlobalChainEdgeIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainEdgeIndex → Digest)

structure ProgrammedGlobalChainKeygenView where
  publicKey : PublicKey
  secretKey : SecretKey
  cache : QueryCache HashSpec
  table : GlobalChainValueIndex → Digest

def globalChainTableEdgeInput
    (parameter : PublicParameter) (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) : HashInput :=
  Concrete.CacheView.chainInput parameter edge.2.1 edge.1 edge.2.2
    (table (edge.1, edge.2.1, chainStepDigit edge.2.2))

def globalChainTableEdgeTarget
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) : Digest :=
  table (edge.1, edge.2.1, chainStepNextDigit edge.2.2)

def GlobalChainTableSeedsMatch
    (secretKey : SecretKey) (table : GlobalChainValueIndex → Digest) : Prop :=
  ∀ epoch chain,
    secretKey.chainStart epoch chain =
      table (chain, epoch, ⟨0, by simp [chainLength]⟩)

def GlobalChainTableEdgesMatch
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) : Prop :=
  ∀ edge, ∃ output,
    cache (globalChainTableEdgeInput parameter table edge) = some output ∧
      truncateHash output = globalChainTableEdgeTarget table edge

theorem GlobalChainTableEdgesMatch.mono
    {cache larger : QueryCache HashSpec} {parameter : PublicParameter}
    {table : GlobalChainValueIndex → Digest}
    (hmatch : GlobalChainTableEdgesMatch cache parameter table)
    (hle : cache ≤ larger) :
    GlobalChainTableEdgesMatch larger parameter table := by
  intro edge
  obtain ⟨output, hcached, htarget⟩ := hmatch edge
  exact ⟨output, hle hcached, htarget⟩

def globalChainTableSeedTargets
    (table : GlobalChainValueIndex → Digest) : Epoch → ChainIndex → Digest :=
  fun epoch chain => table (chain, epoch, ⟨0, by simp [chainLength]⟩)

/-- A global chain table is equivalently all chain seeds and all positive edge coordinates. -/
def globalChainTableMaterialEquiv :
    (GlobalChainValueIndex → Digest) ≃
      ((Epoch → ChainIndex → Digest) × (GlobalChainEdgeIndex → Digest)) where
  toFun table := (globalChainTableSeedTargets table, globalChainTableEdgeTarget table)
  invFun material index :=
    if hzero : index.2.2.val = 0 then
      material.1 index.2.1 index.1
    else
      material.2
        (index.1, index.2.1, ⟨index.2.2.val - 1, by
          have hdigit := index.2.2.isLt
          omega⟩)
  left_inv table := by
    funext index
    by_cases hzero : index.2.2.val = 0
    · simp only [hzero, ↓reduceDIte, globalChainTableSeedTargets]
      apply congrArg table
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      exact Fin.ext hzero.symm
    · simp only [hzero, ↓reduceDIte, globalChainTableEdgeTarget]
      apply congrArg table
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      apply Fin.ext
      simp [chainStepNextDigit]
      omega
  right_inv material := by
    apply Prod.ext
    · funext epoch chain
      simp [globalChainTableSeedTargets]
    · funext edge
      simp only [globalChainTableEdgeTarget]
      have hpositive : (chainStepNextDigit edge.2.2).val ≠ 0 := by
        simp [chainStepNextDigit]
      simp only [hpositive, ↓reduceDIte]
      apply congrArg material.2
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      apply Fin.ext
      simp [chainStepNextDigit]

noncomputable def independentGlobalChainTableMaterial :
    ProbComp ((Epoch → ChainIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest)) :=
  Prod.mk <$> ($ᵗ (Epoch → ChainIndex → Digest)) <*>
    ($ᵗ (GlobalChainEdgeIndex → Digest))

theorem evalDist_split_uniformGlobalChainTable_eq_independent :
    𝒟[globalChainTableMaterialEquiv <$>
        ($ᵗ (GlobalChainValueIndex → Digest))] =
      𝒟[independentGlobalChainTableMaterial] := by
  apply SPMF.ext
  intro target
  change Pr[= target | globalChainTableMaterialEquiv <$>
      ($ᵗ (GlobalChainValueIndex → Digest))] =
    Pr[= target | independentGlobalChainTableMaterial]
  rw [probOutput_map_bijective_uniform_cross
    (α := GlobalChainValueIndex → Digest)
    (β := (Epoch → ChainIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest))
    globalChainTableMaterialEquiv globalChainTableMaterialEquiv.bijective]
  calc
    Pr[= target | $ᵗ ((Epoch → ChainIndex → Digest) ×
        (GlobalChainEdgeIndex → Digest))] =
        Pr[= target.1 | $ᵗ (Epoch → ChainIndex → Digest)] *
          Pr[= target.2 | $ᵗ (GlobalChainEdgeIndex → Digest)] := by
      rw [probOutput_uniformSample, probOutput_uniformSample,
        probOutput_uniformSample, Fintype.card_prod, Nat.cast_mul,
        ENNReal.mul_inv]
      · exact Or.inr (ENNReal.natCast_ne_top _)
      · exact Or.inl (ENNReal.natCast_ne_top _)
    _ = Pr[= target | independentGlobalChainTableMaterial] := by
      symm
      rw [independentGlobalChainTableMaterial]
      rw [probOutput_seq_map_prod_mk_eq_mul]

noncomputable def allChains : List ChainIndex :=
  Finset.univ.toList

theorem allChains_nodup : allChains.Nodup := by
  exact Finset.nodup_toList _

theorem mem_allChains (chain : ChainIndex) : chain ∈ allChains := by
  simp [allChains]

noncomputable def actualGlobalChainKeygen :
    ProbComp ProgrammedGlobalChainKeygenView := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
  return {
    publicKey := keyResult.1.1
    secretKey := keyResult.1.2
    cache := keyResult.2
    table := globalKeygenChainValueTable keyResult.2 keyResult.1.2
  }

theorem actualGlobalChainKeygen_support_table
    (result : ProgrammedGlobalChainKeygenView)
    (hresult : result ∈ support actualGlobalChainKeygen) :
    globalKeygenChainValueTable result.cache result.secretKey = result.table := by
  unfold actualGlobalChainKeygen at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, _hkeyResult, hpure⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  rfl

noncomputable def explicitGlobalChainKeygen :
    ProbComp ProgrammedGlobalChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let secret ← Concrete.sampleSecret
  let rootResult ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)).run ∅
  let secretKey : SecretKey := (SecretKey.withoutPrecomputation parameter secret)
  return {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey
    cache := rootResult.2
    table := globalKeygenChainValueTable rootResult.2 secretKey
  }

theorem evalDist_actualGlobalChainKeygen_eq_explicit :
    evalDist actualGlobalChainKeygen =
      evalDist explicitGlobalChainKeygen := by
  unfold actualGlobalChainKeygen explicitGlobalChainKeygen Concrete.keygen
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, bind_assoc, pure_bind]
  have hparameter :
      (simulateQ xmssRomImpl
        (liftM Concrete.samplePublicParameter)).run ∅ =
        (fun parameter => (parameter, ∅)) <$>
          Concrete.samplePublicParameter := by
    simpa only [xmssRomImpl] using
      (roSim.run_liftM
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp))
        Concrete.samplePublicParameter ∅)
  rw [hparameter]
  simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  have hsecret :
      (simulateQ xmssRomImpl (liftM Concrete.sampleSecret)).run ∅ =
        (fun secret => (secret, ∅)) <$> Concrete.sampleSecret := by
    simpa only [xmssRomImpl] using
      (roSim.run_liftM
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp))
        Concrete.sampleSecret ∅)
  rw [hsecret]
  simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secret
  have htree :
      simulateQ xmssRomImpl
          (liftM (Concrete.treeNode parameter secret treeHeight
            Concrete.rootNode : OracleComp HashSpec Digest)) =
        simulateQ
          (randomOracle : QueryImpl HashSpec
            (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest) := by
    simp only [xmssRomImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)
  rw [htree]

end XmssSecurity.CappedChain
