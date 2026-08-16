import XmssSecurity.CappedGlobalChainTable
import XmssSecurity.CappedChain.ChainTablePresampling

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

theorem globalChainTableEdgeInput_injective
    (parameter : PublicParameter) (table : GlobalChainValueIndex → Digest) :
    Function.Injective (globalChainTableEdgeInput parameter table) := by
  intro left right heq
  have hdata := (Concrete.CacheView.chainInput_eq_iff parameter
    left.2.1 right.2.1 left.1 right.1 left.2.2 right.2.2
    (table (left.1, left.2.1, chainStepDigit left.2.2))
    (table (right.1, right.2.1, chainStepDigit right.2.2))).mp heq
  exact Prod.ext hdata.2.1 (Prod.ext hdata.1 hdata.2.2.1)

noncomputable def allGlobalChainEdges : List GlobalChainEdgeIndex :=
  Finset.univ.toList

theorem allGlobalChainEdges_nodup : allGlobalChainEdges.Nodup := by
  exact Finset.nodup_toList _

theorem mem_allGlobalChainEdges (edge : GlobalChainEdgeIndex) :
    edge ∈ allGlobalChainEdges := by
  simp [allGlobalChainEdges]

noncomputable def globalChainTableEdgeInputs
    (parameter : PublicParameter) (table : GlobalChainValueIndex → Digest) :
    List HashInput :=
  allGlobalChainEdges.map (globalChainTableEdgeInput parameter table)

theorem globalChainTableEdgeInputs_nodup
    (parameter : PublicParameter) (table : GlobalChainValueIndex → Digest) :
    (globalChainTableEdgeInputs parameter table).Nodup :=
  allGlobalChainEdges_nodup.map
    (globalChainTableEdgeInput_injective parameter table)

theorem evalDist_xmssRom_run'_eq_presample_globalChainTableTrace
    {alpha : Type} (computation : OracleComp OracleWorld alpha)
    (parameter : PublicParameter) (table : GlobalChainValueIndex → Digest) :
    𝒟[(simulateQ xmssRomImpl computation).run' ∅] =
      𝒟[do
        let trace ← OracleComp.presampleCacheEntriesTrace ∅
          (globalChainTableEdgeInputs parameter table)
        (simulateQ xmssRomImpl computation).run' trace.2] := by
  apply evalDist_xmssRom_run'_eq_presampleTrace
  · exact globalChainTableEdgeInputs_nodup parameter table
  · simp

end XmssSecurity.CappedChain
