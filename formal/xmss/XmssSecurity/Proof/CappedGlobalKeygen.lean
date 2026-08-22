import XmssSecurity.Proof.CappedChain.ChainRevealFiltering
import XmssSecurity.Proof.ChainOraclePresampling
import XmssSecurity.Proof.HashOutputHigh
import XmssSecurity.Proof.UniformFiniteTable
import XmssSecurity.Proof.CausalKeygenCoupling
import XmssSecurity.Proof.CausalTreeCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

abbrev GlobalChainValueIndex := ChainIndex × ChainValueIndex

noncomputable def globalKeygenChainValueTable
    (keygenCache : QueryCache HashSpec) (secretKey : SecretKey) :
    GlobalChainValueIndex → Digest := fun index =>
  keygenChainValueTable keygenCache secretKey index.1 index.2

noncomputable def globalChainInputProbe?
    (parameter : PublicParameter) (input : HashInput) :
    Option (GlobalChainValueIndex × Digest) :=
  if h : ∃ data : Epoch × ChainIndex × ChainStep × Digest,
      input = Concrete.CacheView.chainInput parameter data.1 data.2.1
        data.2.2.1 data.2.2.2 then
    let data := h.choose
    some ((data.2.1, data.1, chainStepDigit data.2.2.1), data.2.2.2)
  else
    none

@[simp]
theorem globalChainInputProbe?_chainInput
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    globalChainInputProbe? parameter
      (Concrete.CacheView.chainInput parameter epoch chain step value) =
      some ((chain, epoch, chainStepDigit step), value) := by
  unfold globalChainInputProbe?
  split
  · rename_i h
    let chosen := h.choose
    have hchosen := h.choose_spec
    have heq := (Concrete.CacheView.chainInput_eq_iff parameter
      chosen.1 epoch chosen.2.1 chain chosen.2.2.1 step
        chosen.2.2.2 value).mp hchosen.symm
    obtain ⟨hepoch, hchain, hstep, hvalue⟩ := heq
    simp only
    rw [hepoch, hchain, hstep, hvalue]
  · rename_i h
    exact (h ⟨(epoch, chain, step, value), rfl⟩).elim


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
  let keyResult ← (simulateQ romImpl Concrete.keygen).run ∅
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
      (simulateQ romImpl
        (liftM Concrete.samplePublicParameter)).run ∅ =
        (fun parameter => (parameter, ∅)) <$>
          Concrete.samplePublicParameter := by
    simpa only [romImpl] using
      (roSim.run_liftM
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp))
        Concrete.samplePublicParameter ∅)
  rw [hparameter]
  simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  have hsecret :
      (simulateQ romImpl (liftM Concrete.sampleSecret)).run ∅ =
        (fun secret => (secret, ∅)) <$> Concrete.sampleSecret := by
    simpa only [romImpl] using
      (roSim.run_liftM
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp))
        Concrete.sampleSecret ∅)
  rw [hsecret]
  simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secret
  have htree :
      simulateQ romImpl
          (liftM (Concrete.treeNode parameter secret treeHeight
            Concrete.rootNode : OracleComp HashSpec Digest)) =
        simulateQ
          (randomOracle : QueryImpl HashSpec
            (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest) := by
    simp only [romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)
  rw [htree]


noncomputable def globalChainEdgeHighTableOfCache
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) :
    GlobalChainEdgeIndex → Digest := fun edge =>
  match cache (globalChainTableEdgeInput parameter table edge) with
  | none => 0
  | some output => XmssSecurity.hashOutputHigh output

def globalChainEdgeOutputFromHigh
    (high : GlobalChainEdgeIndex → Digest)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) : HashOutput :=
  Rom.hashOutputEquivDigestPair.symm
    (high edge, globalChainTableEdgeTarget table edge)

theorem globalChainEdgeOutputFromHigh_eq_cached
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) (output : HashOutput)
    (hcache : cache (globalChainTableEdgeInput parameter table edge) =
      some output)
    (htarget : truncateHash output = globalChainTableEdgeTarget table edge) :
    globalChainEdgeOutputFromHigh
        (globalChainEdgeHighTableOfCache cache parameter table) table edge =
      output := by
  simp [globalChainEdgeOutputFromHigh, globalChainEdgeHighTableOfCache,
    hcache, XmssSecurity.hashOutputHigh, ← htarget]
  exact Rom.hashOutputEquivDigestPair.symm_apply_apply output

theorem globalChainEdgeHighTableOfCache_mono
    (cache larger : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (hmatches : GlobalChainTableEdgesMatch cache parameter table)
    (hle : cache ≤ larger) :
    globalChainEdgeHighTableOfCache cache parameter table =
      globalChainEdgeHighTableOfCache larger parameter table := by
  funext edge
  obtain ⟨output, hcache, _htarget⟩ := hmatches edge
  have hlarger := hle hcache
  simp [globalChainEdgeHighTableOfCache, hcache, hlarger]


abbrev GlobalChainEdgeOutputTable := GlobalChainEdgeIndex → HashOutput

def outputChainSteps : List ChainStep :=
  List.ofFn (id : ChainStep → ChainStep)

theorem outputChainSteps_nodup : outputChainSteps.Nodup :=
  List.nodup_ofFn.mpr Function.injective_id

theorem mem_outputChainSteps (step : ChainStep) :
    step ∈ outputChainSteps := by
  simp [outputChainSteps]

theorem outputChainSteps_length :
    outputChainSteps.length = chainLength - 1 := by
  simp [outputChainSteps, ChainStep]

noncomputable def globalOutputEdgeOrder : List GlobalChainEdgeIndex :=
  allChains ×ˢ (allEpochs ×ˢ outputChainSteps)

theorem globalOutputEdgeOrder_nodup : globalOutputEdgeOrder.Nodup :=
  allChains_nodup.product (allEpochs_nodup.product outputChainSteps_nodup)

theorem mem_globalOutputEdgeOrder (edge : GlobalChainEdgeIndex) :
    edge ∈ globalOutputEdgeOrder := by
  rcases edge with ⟨chain, epoch, step⟩
  exact List.mem_product.mpr ⟨mem_allChains chain,
    List.mem_product.mpr ⟨mem_allEpochs epoch,
      mem_outputChainSteps step⟩⟩

theorem globalOutputEdgeOrder_length :
    globalOutputEdgeOrder.length =
      allChains.length * (allEpochs.length * (chainLength - 1)) := by
  rw [globalOutputEdgeOrder, List.length_product,
    List.length_product, outputChainSteps_length]

noncomputable def globalChainEdgeOutputTableOfOutputTape
    (outputs : List HashOutput) : GlobalChainEdgeOutputTable :=
  finiteTableOfTape globalOutputEdgeOrder globalOutputEdgeOrder_nodup
    mem_globalOutputEdgeOrder outputs

@[simp]
theorem globalChainEdgeOutputTableOfOutputTape_map
    (table : GlobalChainEdgeOutputTable) :
    globalChainEdgeOutputTableOfOutputTape
      (globalOutputEdgeOrder.map table) = table :=
  finiteTableOfTape_map globalOutputEdgeOrder globalOutputEdgeOrder_nodup
    mem_globalOutputEdgeOrder table

theorem evalDist_globalChainEdgeOutputTableOfOutputTape_uniformSnoc_eq_uniform :
    evalDist (globalChainEdgeOutputTableOfOutputTape <$>
      uniformSnocList HashOutput globalOutputEdgeOrder.length) =
    (liftM (PMF.uniformOfFintype GlobalChainEdgeOutputTable) :
      SPMF GlobalChainEdgeOutputTable) :=
  evalDist_finiteTableOfTape_uniformSnoc_eq_uniform globalOutputEdgeOrder
    globalOutputEdgeOrder_nodup mem_globalOutputEdgeOrder

def trajectoryChainSteps : List ChainStep :=
  (List.ofFn (id : ChainStep → ChainStep)).reverse

theorem trajectoryChainSteps_nodup : trajectoryChainSteps.Nodup := by
  unfold trajectoryChainSteps
  rw [List.nodup_reverse]
  exact List.nodup_ofFn.mpr Function.injective_id

theorem mem_trajectoryChainSteps (step : ChainStep) :
    step ∈ trajectoryChainSteps := by
  simp [trajectoryChainSteps]

theorem trajectoryChainSteps_length :
    trajectoryChainSteps.length = chainLength - 1 := by
  simp [trajectoryChainSteps, ChainStep]

noncomputable def globalTrajectoryEdgeOrder : List GlobalChainEdgeIndex :=
  allChains ×ˢ (allEpochs ×ˢ trajectoryChainSteps)

theorem globalTrajectoryEdgeOrder_nodup :
    globalTrajectoryEdgeOrder.Nodup := by
  exact allChains_nodup.product
    (allEpochs_nodup.product trajectoryChainSteps_nodup)

theorem mem_globalTrajectoryEdgeOrder (edge : GlobalChainEdgeIndex) :
    edge ∈ globalTrajectoryEdgeOrder := by
  rcases edge with ⟨chain, epoch, step⟩
  exact List.mem_product.mpr ⟨mem_allChains chain,
    List.mem_product.mpr ⟨mem_allEpochs epoch,
      mem_trajectoryChainSteps step⟩⟩

theorem globalTrajectoryEdgeOrder_length :
    globalTrajectoryEdgeOrder.length =
      allChains.length * (allEpochs.length * (chainLength - 1)) := by
  rw [globalTrajectoryEdgeOrder, List.length_product,
    List.length_product, trajectoryChainSteps_length]

noncomputable def globalChainEdgeOutputTableOfTape
    (outputs : List HashOutput) : GlobalChainEdgeOutputTable :=
  finiteTableOfTape globalTrajectoryEdgeOrder
    globalTrajectoryEdgeOrder_nodup mem_globalTrajectoryEdgeOrder outputs

@[simp]
theorem globalChainEdgeOutputTableOfTape_map
    (table : GlobalChainEdgeOutputTable) :
    globalChainEdgeOutputTableOfTape
      (globalTrajectoryEdgeOrder.map table) = table :=
  finiteTableOfTape_map globalTrajectoryEdgeOrder
    globalTrajectoryEdgeOrder_nodup mem_globalTrajectoryEdgeOrder table

theorem evalDist_globalChainEdgeOutputTableOfTape_drawList_eq_uniform :
    evalDist (globalChainEdgeOutputTableOfTape <$>
      OracleComp.drawList ($ᵗ HashOutput)
        globalTrajectoryEdgeOrder.length) =
    (liftM (PMF.uniformOfFintype GlobalChainEdgeOutputTable) :
      SPMF GlobalChainEdgeOutputTable) :=
  evalDist_finiteTableOfTape_drawList_eq_uniform globalTrajectoryEdgeOrder
    globalTrajectoryEdgeOrder_nodup mem_globalTrajectoryEdgeOrder

noncomputable local instance outputTableSampleable :
    SampleableType GlobalChainEdgeOutputTable :=
  SampleableType.ofFintype GlobalChainEdgeOutputTable

noncomputable local instance secretTableSampleable :
    SampleableType (Epoch → ChainIndex → Digest) :=
  SampleableType.ofFintype (Epoch → ChainIndex → Digest)

noncomputable local instance highTableSampleable :
    SampleableType (GlobalChainEdgeIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainEdgeIndex → Digest)

noncomputable def globalChainValueTableOfRandomness
    (randomness : (Epoch → ChainIndex → Digest) ×
      GlobalChainEdgeOutputTable) :
    GlobalChainValueIndex → Digest :=
  globalChainTableMaterialEquiv.symm
    (randomness.1, fun edge => truncateHash (randomness.2 edge))

def globalChainHighTableOfRandomness
    (randomness : (Epoch → ChainIndex → Digest) ×
      GlobalChainEdgeOutputTable) :
    GlobalChainEdgeIndex → Digest :=
  fun edge => hashOutputHigh (randomness.2 edge)

noncomputable def globalChainKeygenRandomnessView
    (randomness : (Epoch → ChainIndex → Digest) ×
      GlobalChainEdgeOutputTable) :
    (GlobalChainValueIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest) :=
  (globalChainValueTableOfRandomness randomness,
    globalChainHighTableOfRandomness randomness)

noncomputable def globalChainKeygenRandomnessOfView
    (view : (GlobalChainValueIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest)) :
    (Epoch → ChainIndex → Digest) × GlobalChainEdgeOutputTable :=
  let material := globalChainTableMaterialEquiv view.1
  (material.1, fun edge =>
    Rom.hashOutputEquivDigestPair.symm (view.2 edge, material.2 edge))

theorem globalChainKeygenRandomnessOfView_view
    (randomness : (Epoch → ChainIndex → Digest) ×
      GlobalChainEdgeOutputTable) :
    globalChainKeygenRandomnessOfView
      (globalChainKeygenRandomnessView randomness) = randomness := by
  apply Prod.ext
  · change (globalChainTableMaterialEquiv
        (globalChainTableMaterialEquiv.symm
          (randomness.1, fun edge => truncateHash (randomness.2 edge)))).1 =
      randomness.1
    exact congrArg Prod.fst (globalChainTableMaterialEquiv.apply_symm_apply
      (randomness.1, fun edge => truncateHash (randomness.2 edge)))
  · funext edge
    have hmaterial := globalChainTableMaterialEquiv.apply_symm_apply
      (randomness.1, fun edge => truncateHash (randomness.2 edge))
    have hlow := congrFun (congrArg Prod.snd hmaterial) edge
    change Rom.hashOutputEquivDigestPair.symm
        (hashOutputHigh (randomness.2 edge),
          (globalChainTableMaterialEquiv
            (globalChainTableMaterialEquiv.symm
              (randomness.1, fun edge => truncateHash (randomness.2 edge)))).2
                edge) = randomness.2 edge
    rw [hlow]
    exact Rom.hashOutputEquivDigestPair.symm_apply_apply (randomness.2 edge)

theorem globalChainKeygenRandomnessView_ofView
    (view : (GlobalChainValueIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest)) :
    globalChainKeygenRandomnessView
      (globalChainKeygenRandomnessOfView view) = view := by
  apply Prod.ext
  · change globalChainTableMaterialEquiv.symm
        ((globalChainTableMaterialEquiv view.1).1, fun edge =>
          truncateHash (Rom.hashOutputEquivDigestPair.symm
            (view.2 edge, (globalChainTableMaterialEquiv view.1).2 edge))) = view.1
    have hlow : (fun edge =>
        truncateHash (Rom.hashOutputEquivDigestPair.symm
          (view.2 edge, (globalChainTableMaterialEquiv view.1).2 edge))) =
        (globalChainTableMaterialEquiv view.1).2 := by
      funext edge
      exact congrArg Prod.snd
        (Rom.hashOutputEquivDigestPair.apply_symm_apply
          (view.2 edge, (globalChainTableMaterialEquiv view.1).2 edge))
    rw [hlow, globalChainTableMaterialEquiv.symm_apply_apply]
  · funext edge
    exact congrArg Prod.fst
      (Rom.hashOutputEquivDigestPair.apply_symm_apply
        (view.2 edge, (globalChainTableMaterialEquiv view.1).2 edge))

theorem globalChainKeygenRandomnessView_bijective :
    Function.Bijective globalChainKeygenRandomnessView := by
  constructor
  · intro left right heq
    rw [← globalChainKeygenRandomnessOfView_view left,
      ← globalChainKeygenRandomnessOfView_view right, heq]
  · intro view
    exact ⟨globalChainKeygenRandomnessOfView view,
      globalChainKeygenRandomnessView_ofView view⟩

noncomputable def independentGlobalChainValueTable :
    ProbComp (GlobalChainValueIndex → Digest) :=
  $ᵗ (GlobalChainValueIndex → Digest)

noncomputable def independentGlobalChainHigh :
    ProbComp (GlobalChainEdgeIndex → Digest) :=
  $ᵗ (GlobalChainEdgeIndex → Digest)

theorem independentGlobalChainValueTable_eq_uniform :
    independentGlobalChainValueTable =
      ($ᵗ (GlobalChainValueIndex → Digest)) := rfl

theorem evalDist_independentGlobalChainValueTable_eq_uniformMeasure :
    evalDist independentGlobalChainValueTable =
      (liftM (PMF.uniformOfFintype
        (GlobalChainValueIndex → Digest)) :
        SPMF (GlobalChainValueIndex → Digest)) := by
  rw [independentGlobalChainValueTable_eq_uniform,
    evalDist_uniformSample]

noncomputable def independentGlobalChainTableHigh :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest)) := do
  let table ← independentGlobalChainValueTable
  let high ← independentGlobalChainHigh
  pure (table, high)

noncomputable def uniformGlobalChainKeygenRandomness :
    ProbComp ((Epoch → ChainIndex → Digest) ×
      GlobalChainEdgeOutputTable) :=
  Prod.mk <$> Concrete.sampleSecret <*>
    ($ᵗ GlobalChainEdgeOutputTable)

theorem Concrete.evalDist_sampleSecret_eq_uniformMeasure :
    evalDist Concrete.sampleSecret =
    (liftM (PMF.uniformOfFintype (Epoch → ChainIndex → Digest)) :
      SPMF (Epoch → ChainIndex → Digest)) := by
  calc
    _ = evalDist ($ᵗ (Epoch → ChainIndex → Digest)) :=
      congrArg evalDist Concrete.sampleSecret_eq
    _ = _ := evalDist_uniformSample (Epoch → ChainIndex → Digest)

set_option maxRecDepth 100000 in
theorem evalDist_uniformGlobalChainKeygenRandomness_eq_uniform :
    evalDist uniformGlobalChainKeygenRandomness =
      evalDist ($ᵗ ((Epoch → ChainIndex → Digest) ×
        GlobalChainEdgeOutputTable)) := by
  apply SPMF.ext
  intro target
  change Pr[= target | uniformGlobalChainKeygenRandomness] =
    Pr[= target | $ᵗ ((Epoch → ChainIndex → Digest) ×
      GlobalChainEdgeOutputTable)]
  rw [uniformGlobalChainKeygenRandomness,
    probOutput_seq_map_prod_mk_eq_mul]
  rw [Concrete.probOutput_sampleSecret, probOutput_uniformSample,
    probOutput_uniformSample, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv]
  · exact Or.inr (ENNReal.natCast_ne_top _)
  · exact Or.inl (ENNReal.natCast_ne_top _)

theorem evalDist_uniformGlobalChainKeygenRandomness_eq_uniformMeasure :
    evalDist uniformGlobalChainKeygenRandomness =
    (liftM (PMF.uniformOfFintype
      ((Epoch → ChainIndex → Digest) × GlobalChainEdgeOutputTable)) :
      SPMF ((Epoch → ChainIndex → Digest) ×
        GlobalChainEdgeOutputTable)) :=
  evalDist_uniformGlobalChainKeygenRandomness_eq_uniform.trans
    (evalDist_uniformSample
      ((Epoch → ChainIndex → Digest) × GlobalChainEdgeOutputTable))

set_option maxRecDepth 100000 in
theorem evalDist_uniformGlobalChainKeygenRandomness_eq_independent :
    evalDist (globalChainKeygenRandomnessView <$>
      ($ᵗ ((Epoch → ChainIndex → Digest) ×
        GlobalChainEdgeOutputTable))) =
    evalDist independentGlobalChainTableHigh := by
  apply SPMF.ext
  intro target
  change Pr[= target | globalChainKeygenRandomnessView <$>
      ($ᵗ ((Epoch → ChainIndex → Digest) ×
        GlobalChainEdgeOutputTable))] =
    Pr[= target | independentGlobalChainTableHigh]
  rw [probOutput_map_bijective_uniform_cross
    (α := (Epoch → ChainIndex → Digest) × GlobalChainEdgeOutputTable)
    (β := (GlobalChainValueIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest))
    globalChainKeygenRandomnessView
    globalChainKeygenRandomnessView_bijective]
  rw [show independentGlobalChainTableHigh =
      Prod.mk <$> ($ᵗ (GlobalChainValueIndex → Digest)) <*>
        ($ᵗ (GlobalChainEdgeIndex → Digest)) by
      simp [independentGlobalChainTableHigh,
        independentGlobalChainValueTable, independentGlobalChainHigh,
        monad_norm]]
  rw [probOutput_seq_map_prod_mk_eq_mul]
  rw [probOutput_uniformSample, probOutput_uniformSample,
    probOutput_uniformSample, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv]
  · exact Or.inr (ENNReal.natCast_ne_top _)
  · exact Or.inl (ENNReal.natCast_ne_top _)

theorem evalDist_globalChainKeygenRandomnessView_eq_independent :
    evalDist (globalChainKeygenRandomnessView <$>
      uniformGlobalChainKeygenRandomness) =
    evalDist independentGlobalChainTableHigh := by
  calc
    _ = evalDist (globalChainKeygenRandomnessView <$>
          ($ᵗ ((Epoch → ChainIndex → Digest) ×
            GlobalChainEdgeOutputTable))) := by
      rw [evalDist_map,
        evalDist_uniformGlobalChainKeygenRandomness_eq_uniform,
        ← evalDist_map]
    _ = _ := evalDist_uniformGlobalChainKeygenRandomness_eq_independent


abbrev AllChainTrajectories := ChainIndex → List FullChainTrajectory

noncomputable def globalChainValueTableOfTrajectories
    (trajectories : AllChainTrajectories) :
    GlobalChainValueIndex → Digest := fun index =>
  chainValueTableOfList (trajectories index.1) index.2

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

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.allChainTrajectoriesFromCache_support_info
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec)
      (result : AllChainTrajectories × QueryCache HashSpec),
      chains.Nodup →
      result ∈ support
        (Concrete.allChainTrajectoriesFromCache parameter secret cache chains) →
      cache ≤ result.2 ∧
        ∀ chain ∈ chains,
          (result.1 chain).length = lifetime ∧
            ∀ largerCache : QueryCache HashSpec, result.2 ≤ largerCache →
            List.Forall₂
              (fun epoch trajectory =>
                evalWithAnswerFn (Concrete.CacheReplay.answerFn largerCache)
                  (Concrete.chainTrajectory parameter epoch chain 0
                    (chainLength - 1) (secret epoch chain)) = trajectory)
              allEpochs (result.1 chain) := by
  intro chains
  induction chains with
  | nil =>
      intro cache result _hnodup hresult
      simp only [Concrete.allChainTrajectoriesFromCache_nil, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨le_rfl, by simp⟩
  | cons chain chains ih =>
      intro cache result hnodup hresult
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [Concrete.allChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      have hfirstInfo :=
        Concrete.fixedSeedChainTrajectoriesFromCache_support_info parameter
          secret chain (chainLength - 1) allEpochs cache first hfirst
      have hrestInfo := ih first.2 rest htailNodup hrest
      constructor
      · exact hfirstInfo.1.trans hrestInfo.1
      · intro selected hselected
        by_cases heq : selected = chain
        · subst selected
          simp only [Function.update_self]
          constructor
          · simpa [allEpochs_length] using hfirstInfo.2.1
          · intro largerCache hlarger
            exact
              Concrete.fixedSeedChainTrajectoriesFromCache_replay_in_largerCache
                parameter secret chain (chainLength - 1) allEpochs cache first
                  largerCache hfirst (hrestInfo.1.trans hlarger)
        · have htail : selected ∈ chains := by
            simpa [heq] using hselected
          simp only [Function.update_of_ne heq]
          exact hrestInfo.2 selected htail

theorem chainValueTableOfList_eq_keygenChainValueTable_of_replay
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (cache : QueryCache HashSpec)
    (trajectories : List FullChainTrajectory)
    (hlength : trajectories.length = lifetime)
    (hreplay : List.Forall₂
      (fun epoch trajectory =>
        evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
          (Concrete.chainTrajectory parameter epoch chain 0
            (chainLength - 1) (secret epoch chain)) = trajectory)
      allEpochs trajectories) :
    chainValueTableOfList trajectories =
      keygenChainValueTable cache (SecretKey.withoutPrecomputation parameter secret) chain := by
  funext index
  unfold chainValueTableOfList
  split
  · rename_i htableLength
    let position := epochPosition index.1
    have htrajectoryPosition : position.val < trajectories.length := by
      rw [← htableLength]
      exact position.isLt
    have hpair := hreplay.get position.isLt htrajectoryPosition
    have hepoch : allEpochs.get position = index.1 :=
      allEpochs_get_epochPosition index.1
    rw [hepoch] at hpair
    have hvalue := congrArg
      (fun trajectory : FullChainTrajectory =>
        trajectory[index.2.val]'(by
          have hdigit := index.2.isLt
          omega)) hpair
    rw [Concrete.chainTrajectory_getElem] at hvalue
    exact hvalue.symm
  · rename_i htableLength
    exact (htableLength (allEpochs_length.trans hlength.symm)).elim

theorem Concrete.allChainTrajectoriesFromCache_globalTable_eq
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (result : AllChainTrajectories × QueryCache HashSpec)
    (largerCache : QueryCache HashSpec)
    (hresult : result ∈ support
      (Concrete.allChainTrajectoriesFromCache parameter secret ∅ allChains))
    (hle : result.2 ≤ largerCache) :
    globalChainValueTableOfTrajectories result.1 =
      globalKeygenChainValueTable largerCache (SecretKey.withoutPrecomputation parameter secret) := by
  have hinfo := Concrete.allChainTrajectoriesFromCache_support_info parameter
    secret allChains ∅ result allChains_nodup hresult
  funext index
  have hchainInfo := hinfo.2 index.1 (mem_allChains index.1)
  have hlocal := chainValueTableOfList_eq_keygenChainValueTable_of_replay
    parameter secret index.1 largerCache (result.1 index.1) hchainInfo.1
      (hchainInfo.2 largerCache hle)
  exact congrFun hlocal index.2

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

def trajectoryTailTape {steps : Nat}
    (trajectory : Vector Digest (steps + 1)) : List Digest :=
  trajectory.toList.drop 1

@[simp]
theorem trajectoryTailTape_ofFn_seed (seed : Digest) :
    trajectoryTailTape (Vector.ofFn fun _ : Fin 1 => seed) = [] := by
  apply List.eq_nil_of_length_eq_zero
  simp [trajectoryTailTape]

theorem trajectoryTailTape_push {steps : Nat}
    (trajectory : Vector Digest (steps + 1)) (next : Digest) :
    trajectoryTailTape (trajectory.push next) =
      trajectoryTailTape trajectory ++ [next] := by
  unfold trajectoryTailTape
  rw [Vector.toList_push, List.drop_append_of_le_length]
  simp

theorem evalDist_uniformTrajectoryFromSeed_tailTape
    (steps : Nat) (seed : Digest) :
    evalDist (trajectoryTailTape <$>
      uniformTrajectoryFromSeed steps seed) =
      evalDist (uniformSnocList Digest steps) := by
  induction steps with
  | zero => simp [uniformSnocList]
  | succ steps ih =>
      rw [uniformTrajectoryFromSeed_succ, uniformSnocList]
      simp only [map_bind, bind_pure_comp]
      calc
        _ = evalDist (uniformTrajectoryFromSeed steps seed >>= fun prior =>
              ($ᵗ Digest) >>= fun next =>
              pure (trajectoryTailTape prior ++ [next])) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro prior
          simp [trajectoryTailTape_push]
        _ = evalDist (uniformSnocList Digest steps >>= fun prior =>
              ($ᵗ Digest) >>= fun next =>
              pure (prior ++ [next])) := by
          calc
            _ = evalDist ((trajectoryTailTape <$>
                  uniformTrajectoryFromSeed steps seed) >>= fun prior =>
                ($ᵗ Digest) >>= fun next =>
                pure (prior ++ [next])) := by
              simp [map_eq_bind_pure_comp, bind_assoc]
            _ = _ := by
              rw [evalDist_bind, ih, ← evalDist_bind]

def trajectoryDrawTape {steps : Nat}
    (trajectory : Vector Digest (steps + 1)) : List Digest :=
  (trajectoryTailTape trajectory).reverse

theorem trajectoryDrawTape_ofDigitTable (values : Digit → Digest) :
    trajectoryDrawTape (FullChainTrajectory.ofDigitTable values) =
      trajectoryChainSteps.map
        (fun step => values (chainStepNextDigit step)) := by
  unfold trajectoryDrawTape trajectoryTailTape trajectoryChainSteps
    FullChainTrajectory.ofDigitTable
  rw [Vector.toList_ofFn, List.ofFn_succ]
  simp only [List.drop]
  rw [List.map_reverse]
  congr 1

theorem evalDist_uniformTrajectoryFromSeed_drawTape
    (steps : Nat) (seed : Digest) :
    evalDist (trajectoryDrawTape <$>
      uniformTrajectoryFromSeed steps seed) =
      evalDist (OracleComp.drawList ($ᵗ Digest) steps) := by
  calc
    _ = evalDist (List.reverse <$>
          (trajectoryTailTape <$>
            uniformTrajectoryFromSeed steps seed)) := by
      rw [Functor.map_map]
      rfl
    _ = evalDist (List.reverse <$>
          uniformSnocList Digest steps) := by
      rw [evalDist_map,
        evalDist_uniformTrajectoryFromSeed_tailTape steps seed,
        ← evalDist_map]
    _ = evalDist (List.reverse <$>
          (List.reverse <$>
            OracleComp.drawList ($ᵗ Digest) steps)) := by
      rw [evalDist_map,
        evalDist_uniformSnocList_eq_reverse_drawList Digest steps,
        ← evalDist_map]
    _ = evalDist (OracleComp.drawList ($ᵗ Digest) steps) := by
      simp [Functor.map_map]

theorem drawList_append (firstLength secondLength : Nat) :
    (do
      let first ← OracleComp.drawList ($ᵗ Digest) firstLength
      let second ← OracleComp.drawList ($ᵗ Digest) secondLength
      pure (first ++ second)) =
      OracleComp.drawList ($ᵗ Digest) (firstLength + secondLength) := by
  induction firstLength with
  | zero => simp [OracleComp.drawList]
  | succ firstLength ih =>
      calc
        (do
            let first ← OracleComp.drawList ($ᵗ Digest) (firstLength + 1)
            let second ← OracleComp.drawList ($ᵗ Digest) secondLength
            pure (first ++ second)) =
            (do
              let head ← $ᵗ Digest
              let tail ← (do
                let first ← OracleComp.drawList ($ᵗ Digest) firstLength
                let second ← OracleComp.drawList ($ᵗ Digest) secondLength
                pure (first ++ second))
              pure (head :: tail)) := by
          simp [OracleComp.drawList, bind_assoc]
        _ = (do
              let head ← $ᵗ Digest
              let tail ← OracleComp.drawList ($ᵗ Digest)
                (firstLength + secondLength)
              pure (head :: tail)) := by
          rw [ih]
        _ = OracleComp.drawList ($ᵗ Digest)
              ((firstLength + secondLength) + 1) := rfl
        _ = OracleComp.drawList ($ᵗ Digest)
              ((firstLength + 1) + secondLength) := by
          congr 1
          omega

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

def fixedChainTrajectoryDrawTape {steps : Nat}
    (trajectories : List (Vector Digest (steps + 1))) : List Digest :=
  trajectories.flatMap trajectoryDrawTape

theorem evalDist_uniformFixedChainTrajectories_drawTape
    (secret : Epoch → ChainIndex → Digest) (chain : ChainIndex)
    (steps : Nat) : ∀ epochs : List Epoch,
    evalDist (fixedChainTrajectoryDrawTape <$>
      uniformFixedChainTrajectories secret chain steps epochs) =
      evalDist (OracleComp.drawList ($ᵗ Digest)
        (epochs.length * steps)) := by
  intro epochs
  induction epochs with
  | nil => simp [fixedChainTrajectoryDrawTape, OracleComp.drawList]
  | cons epoch epochs ih =>
      rw [uniformFixedChainTrajectories_cons]
      simp only [map_bind, bind_pure_comp]
      calc
        _ = evalDist (uniformTrajectoryFromSeed steps
              (secret epoch chain) >>= fun first =>
            uniformFixedChainTrajectories secret chain steps epochs >>=
              fun rest =>
            pure (trajectoryDrawTape first ++
              fixedChainTrajectoryDrawTape rest)) := by
          simp [fixedChainTrajectoryDrawTape]
        _ = evalDist ((trajectoryDrawTape <$>
              uniformTrajectoryFromSeed steps (secret epoch chain)) >>=
            fun first =>
            (fixedChainTrajectoryDrawTape <$>
              uniformFixedChainTrajectories secret chain steps epochs) >>=
            fun rest => pure (first ++ rest)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = evalDist (OracleComp.drawList ($ᵗ Digest) steps >>= fun first =>
            OracleComp.drawList ($ᵗ Digest) (epochs.length * steps) >>=
              fun rest => pure (first ++ rest)) := by
          rw [evalDist_bind,
            evalDist_uniformTrajectoryFromSeed_drawTape steps
              (secret epoch chain), ← evalDist_bind]
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          rw [evalDist_bind, ih, ← evalDist_bind]
        _ = evalDist (OracleComp.drawList ($ᵗ Digest)
              (steps + epochs.length * steps)) := by
          rw [drawList_append]
        _ = evalDist (OracleComp.drawList ($ᵗ Digest)
              ((epoch :: epochs).length * steps)) := by
          congr 3
          simp only [List.length_cons]
          simp [Nat.add_mul, Nat.add_comm]

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
      rfl
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

theorem uniformTrajectoryFromSeed_support_first :
    ∀ (steps : Nat) (seed : Digest)
      (trajectory : Vector Digest (steps + 1)),
      trajectory ∈ support (uniformTrajectoryFromSeed steps seed) →
      trajectory[0]'(by omega) = seed := by
  intro steps
  induction steps with
  | zero =>
      intro seed trajectory htrajectory
      simp only [uniformTrajectoryFromSeed_zero, support_pure,
        Set.mem_singleton_iff] at htrajectory
      subst trajectory
      rw [Vector.getElem_ofFn]
  | succ steps ih =>
      intro seed trajectory htrajectory
      rw [uniformTrajectoryFromSeed_succ, mem_support_bind_iff] at htrajectory
      obtain ⟨prior, hprior, hnext⟩ := htrajectory
      rw [mem_support_bind_iff] at hnext
      obtain ⟨next, _hnext, hpure⟩ := hnext
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst trajectory
      rw [Vector.getElem_push_lt (by omega)]
      exact ih seed prior hprior

theorem uniformFixedChainTrajectories_support_info
    (secret : Epoch → ChainIndex → Digest) (chain : ChainIndex)
    (steps : Nat) : ∀ (epochs : List Epoch)
      (trajectories : List (Vector Digest (steps + 1))),
      trajectories ∈ support
        (uniformFixedChainTrajectories secret chain steps epochs) →
      trajectories.length = epochs.length ∧
        List.Forall₂
          (fun epoch trajectory =>
            trajectory[0]'(by omega) = secret epoch chain)
          epochs trajectories := by
  intro epochs
  induction epochs with
  | nil =>
      intro trajectories htrajectories
      simp only [uniformFixedChainTrajectories_nil, support_pure,
        Set.mem_singleton_iff] at htrajectories
      subst trajectories
      exact ⟨rfl, List.Forall₂.nil⟩
  | cons epoch epochs ih =>
      intro trajectories htrajectories
      rw [uniformFixedChainTrajectories_cons,
        mem_support_bind_iff] at htrajectories
      obtain ⟨first, hfirst, hrest⟩ := htrajectories
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst trajectories
      have hrestInfo := ih rest hrest
      constructor
      · simp [hrestInfo.1]
      · exact List.Forall₂.cons
          (uniformTrajectoryFromSeed_support_first steps
            (secret epoch chain) first hfirst)
          hrestInfo.2

theorem uniformAllChainTrajectories_support_info
    (secret : Epoch → ChainIndex → Digest) :
    ∀ (chains : List ChainIndex) (trajectories : AllChainTrajectories),
      chains.Nodup →
      trajectories ∈ support (uniformAllChainTrajectories secret chains) →
      ∀ chain ∈ chains,
        (trajectories chain).length = lifetime ∧
          List.Forall₂
            (fun epoch trajectory =>
              trajectory[0]'(by omega) = secret epoch chain)
            allEpochs (trajectories chain) := by
  intro chains
  induction chains with
  | nil => simp
  | cons chain chains ih =>
      intro trajectories hnodup htrajectories
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [uniformAllChainTrajectories_cons,
        mem_support_bind_iff] at htrajectories
      obtain ⟨first, hfirst, hrest⟩ := htrajectories
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst trajectories
      have hfirstInfo := uniformFixedChainTrajectories_support_info secret
        chain (chainLength - 1) allEpochs first hfirst
      have hrestInfo := ih rest htailNodup hrest
      intro selected hselected
      by_cases heq : selected = chain
      · subst selected
        simp only [Function.update_self]
        exact ⟨by simpa [allEpochs_length] using hfirstInfo.1,
          hfirstInfo.2⟩
      · have htail : selected ∈ chains := by
          simpa [heq] using hselected
        simp only [Function.update_of_ne heq]
        exact hrestInfo selected htail

theorem chainValueTableOfList_zero_eq_of_forall₂
    (secret : Epoch → ChainIndex → Digest) (chain : ChainIndex)
    (trajectories : List FullChainTrajectory)
    (hlength : trajectories.length = lifetime)
    (hseeds : List.Forall₂
      (fun epoch trajectory =>
        trajectory[0]'(by simp [chainLength]) = secret epoch chain)
      allEpochs trajectories) (epoch : Epoch) :
    chainValueTableOfList trajectories
        (epoch, ⟨0, by simp [chainLength]⟩) =
      secret epoch chain := by
  unfold chainValueTableOfList
  split
  · rename_i htableLength
    let position := epochPosition epoch
    have htrajectoryPosition : position.val < trajectories.length := by
      rw [← htableLength]
      exact position.isLt
    have hpair := hseeds.get position.isLt htrajectoryPosition
    have hepoch : allEpochs.get position = epoch :=
      allEpochs_get_epochPosition epoch
    rw [hepoch] at hpair
    simpa [FullChainTrajectory.toDigitTable] using hpair
  · rename_i htableLength
    exact (htableLength (allEpochs_length.trans hlength.symm)).elim

theorem uniformAllChainTrajectories_support_seeds
    (secret : Epoch → ChainIndex → Digest)
    (trajectories : AllChainTrajectories)
    (htrajectories : trajectories ∈ support
      (uniformAllChainTrajectories secret allChains)) :
    globalChainTableSeedTargets
        (globalChainValueTableOfTrajectories trajectories) = secret := by
  have hinfo := uniformAllChainTrajectories_support_info secret allChains
    trajectories allChains_nodup htrajectories
  funext epoch chain
  have hchain := hinfo chain (mem_allChains chain)
  exact chainValueTableOfList_zero_eq_of_forall₂ secret chain
    (trajectories chain) hchain.1 hchain.2 epoch

def allChainTrajectoryDrawTape
    (trajectories : AllChainTrajectories) :
    List ChainIndex → List Digest
  | [] => []
  | chain :: chains =>
      fixedChainTrajectoryDrawTape (trajectories chain) ++
        allChainTrajectoryDrawTape trajectories chains

@[simp]
theorem allChainTrajectoryDrawTape_nil
    (trajectories : AllChainTrajectories) :
    allChainTrajectoryDrawTape trajectories [] = [] := rfl

theorem allChainTrajectoryDrawTape_update_of_not_mem
    (trajectories : AllChainTrajectories) (chain : ChainIndex)
    (values : List FullChainTrajectory) : ∀ chains : List ChainIndex,
    chain ∉ chains →
    allChainTrajectoryDrawTape (Function.update trajectories chain values)
        chains =
      allChainTrajectoryDrawTape trajectories chains := by
  intro chains
  induction chains with
  | nil => simp
  | cons current chains ih =>
      intro hnotMem
      have hne : current ≠ chain := by
        intro heq
        subst current
        exact hnotMem (by simp)
      have htail : chain ∉ chains := by
        intro hmem
        exact hnotMem (by simp [hmem])
      simp [allChainTrajectoryDrawTape, Function.update_of_ne hne, ih htail]

theorem allChainTrajectoryDrawTape_update_cons
    (trajectories : AllChainTrajectories) (chain : ChainIndex)
    (values : List FullChainTrajectory) (chains : List ChainIndex)
    (hnotMem : chain ∉ chains) :
    allChainTrajectoryDrawTape
        (Function.update trajectories chain values) (chain :: chains) =
      fixedChainTrajectoryDrawTape values ++
        allChainTrajectoryDrawTape trajectories chains := by
  simp [allChainTrajectoryDrawTape,
    allChainTrajectoryDrawTape_update_of_not_mem trajectories chain values
      chains hnotMem]

theorem evalDist_uniformAllChainTrajectories_drawTape
    (secret : Epoch → ChainIndex → Digest) :
    ∀ chains : List ChainIndex, chains.Nodup →
    evalDist ((fun trajectories =>
      allChainTrajectoryDrawTape trajectories chains) <$>
        uniformAllChainTrajectories secret chains) =
      evalDist (OracleComp.drawList ($ᵗ Digest)
        (chains.length * (allEpochs.length * (chainLength - 1)))) := by
  intro chains
  induction chains with
  | nil =>
      intro _hnodup
      simp [OracleComp.drawList]
  | cons chain chains ih =>
      intro hnodup
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [uniformAllChainTrajectories_cons]
      simp only [map_bind, bind_pure_comp]
      let blockSize := allEpochs.length * (chainLength - 1)
      calc
        _ = evalDist (uniformFixedChainTrajectories secret chain
              (chainLength - 1) allEpochs >>= fun first =>
            uniformAllChainTrajectories secret chains >>= fun rest =>
            pure (fixedChainTrajectoryDrawTape first ++
              allChainTrajectoryDrawTape rest chains)) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          calc
            _ = evalDist ((fun rest => allChainTrajectoryDrawTape
                  (Function.update rest chain first) (chain :: chains)) <$>
                uniformAllChainTrajectories secret chains) := by
              rw [Functor.map_map]
            _ = evalDist ((fun rest => fixedChainTrajectoryDrawTape first ++
                  allChainTrajectoryDrawTape rest chains) <$>
                uniformAllChainTrajectories secret chains) := by
              congr 2
              funext rest
              exact allChainTrajectoryDrawTape_update_cons rest chain first
                chains hnotMem
            _ = _ := by
              simp [map_eq_bind_pure_comp]
        _ = evalDist ((fixedChainTrajectoryDrawTape <$>
              uniformFixedChainTrajectories secret chain
                (chainLength - 1) allEpochs) >>= fun first =>
            ((fun rest => allChainTrajectoryDrawTape rest chains) <$>
              uniformAllChainTrajectories secret chains) >>= fun rest =>
            pure (first ++ rest)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = evalDist (OracleComp.drawList ($ᵗ Digest) blockSize >>=
            fun first =>
            OracleComp.drawList ($ᵗ Digest)
              (chains.length * blockSize) >>= fun rest =>
            pure (first ++ rest)) := by
          rw [evalDist_bind,
            evalDist_uniformFixedChainTrajectories_drawTape secret chain
              (chainLength - 1) allEpochs, ← evalDist_bind]
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          rw [evalDist_bind, ih htailNodup, ← evalDist_bind]
        _ = evalDist (OracleComp.drawList ($ᵗ Digest)
              (blockSize + chains.length * blockSize)) := by
          rw [drawList_append]
        _ = evalDist (OracleComp.drawList ($ᵗ Digest)
              ((chain :: chains).length *
                (allEpochs.length * (chainLength - 1)))) := by
          congr 3
          dsimp only [blockSize]
          simp [Nat.add_mul, Nat.add_comm]

noncomputable def globalTrajectoryEdgeTableTapeEquiv :
    (GlobalChainEdgeIndex → Digest) ≃
      (Fin globalTrajectoryEdgeOrder.length → Digest) :=
  (Equiv.piCongrLeft (fun _ : GlobalChainEdgeIndex => Digest)
    (globalTrajectoryEdgeOrder_nodup.getEquivOfForallMemList
      globalTrajectoryEdgeOrder mem_globalTrajectoryEdgeOrder)).symm

theorem listOfFn_globalTrajectoryEdgeTableTapeEquiv
    (table : GlobalChainEdgeIndex → Digest) :
    List.ofFn (globalTrajectoryEdgeTableTapeEquiv table) =
      globalTrajectoryEdgeOrder.map table := by
  rw [← List.ofFn_get (globalTrajectoryEdgeOrder.map table)]
  apply List.ext_get
  · simp
  · intro index hleft hright
    simp [globalTrajectoryEdgeTableTapeEquiv]

noncomputable def globalTrajectoryEdgeTableOfTape
    (targets : List Digest) : GlobalChainEdgeIndex → Digest :=
  if hlength : targets.length = globalTrajectoryEdgeOrder.length then
    globalTrajectoryEdgeTableTapeEquiv.symm fun index =>
      targets.get (Fin.cast hlength.symm index)
  else
    fun _ => 0

@[simp]
theorem globalTrajectoryEdgeTableOfTape_map
    (table : GlobalChainEdgeIndex → Digest) :
    globalTrajectoryEdgeTableOfTape
      (globalTrajectoryEdgeOrder.map table) = table := by
  unfold globalTrajectoryEdgeTableOfTape
  split
  · rename_i hlength
    apply globalTrajectoryEdgeTableTapeEquiv.injective
    rw [globalTrajectoryEdgeTableTapeEquiv.apply_symm_apply]
    funext index
    simp [globalTrajectoryEdgeTableTapeEquiv]
  · rename_i hlength
    exact (hlength (by simp)).elim

theorem evalDist_uniformGlobalTrajectoryEdgeTableTape_eq_drawList :
    evalDist ((fun table : GlobalChainEdgeIndex → Digest =>
      globalTrajectoryEdgeOrder.map table) <$>
        ($ᵗ (GlobalChainEdgeIndex → Digest))) =
      evalDist (OracleComp.drawList ($ᵗ Digest)
        globalTrajectoryEdgeOrder.length) := by
  calc
    _ = evalDist (List.ofFn <$>
        (globalTrajectoryEdgeTableTapeEquiv <$>
          ($ᵗ (GlobalChainEdgeIndex → Digest)))) := by
      simp only [Functor.map_map]
      congr 2
      funext table
      exact (listOfFn_globalTrajectoryEdgeTableTapeEquiv table).symm
    _ = evalDist (List.ofFn <$>
        ($ᵗ (Fin globalTrajectoryEdgeOrder.length → Digest))) := by
      rw [evalDist_map]
      rw [evalDist_map_bijective_uniform_cross
        (α := GlobalChainEdgeIndex → Digest)
        (β := Fin globalTrajectoryEdgeOrder.length → Digest)
        globalTrajectoryEdgeTableTapeEquiv
          globalTrajectoryEdgeTableTapeEquiv.bijective]
      rw [← evalDist_map]
    _ = evalDist (OracleComp.drawList ($ᵗ Digest)
        globalTrajectoryEdgeOrder.length) :=
      evalDist_listOfFn_uniform_eq_drawList
        globalTrajectoryEdgeOrder.length

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_globalTrajectoryEdgeTableOfTape_drawList_eq_uniform :
    evalDist (globalTrajectoryEdgeTableOfTape <$>
      OracleComp.drawList ($ᵗ Digest)
        globalTrajectoryEdgeOrder.length) =
      evalDist ($ᵗ (GlobalChainEdgeIndex → Digest)) := by
  calc
    _ = evalDist (globalTrajectoryEdgeTableOfTape <$>
        ((fun table : GlobalChainEdgeIndex → Digest =>
          globalTrajectoryEdgeOrder.map table) <$>
            ($ᵗ (GlobalChainEdgeIndex → Digest)))) := by
      rw [evalDist_map, evalDist_map,
        evalDist_uniformGlobalTrajectoryEdgeTableTape_eq_drawList]
    _ = evalDist ($ᵗ (GlobalChainEdgeIndex → Digest)) := by
      simp [Functor.map_map]

noncomputable def globalChainEdgeTableOfTrajectories
    (trajectories : AllChainTrajectories) :
    GlobalChainEdgeIndex → Digest := fun edge =>
  chainValueTableOfList (trajectories edge.1)
    (edge.2.1, chainStepNextDigit edge.2.2)

theorem fixedChainTrajectoryDrawTape_eq_edgeMap
    (trajectories : List FullChainTrajectory)
    (hlength : trajectories.length = lifetime) :
    fixedChainTrajectoryDrawTape trajectories =
      (allEpochs ×ˢ trajectoryChainSteps).map fun edge =>
        chainValueTableOfList trajectories
          (edge.1, chainStepNextDigit edge.2) := by
  let table := chainValueTableOfList trajectories
  have hinverse : listOfChainValueTable table = trajectories :=
    listOfChainValueTable_chainValueTableOfList trajectories hlength
  conv_lhs => rw [← hinverse]
  change List.flatMap trajectoryDrawTape (allEpochs.map fun epoch =>
      FullChainTrajectory.ofDigitTable fun digit => table (epoch, digit)) =
    (allEpochs ×ˢ trajectoryChainSteps).map fun edge =>
      table (edge.1, chainStepNextDigit edge.2)
  have hgeneral : ∀ epochs : List Epoch,
      List.flatMap trajectoryDrawTape (epochs.map fun epoch =>
        FullChainTrajectory.ofDigitTable fun digit => table (epoch, digit)) =
      (epochs ×ˢ trajectoryChainSteps).map fun edge =>
        table (edge.1, chainStepNextDigit edge.2) := by
    intro epochs
    induction epochs with
    | nil => simp
    | cons epoch epochs ih =>
        rw [List.map_cons, List.flatMap_cons, List.product_cons,
          List.map_append, ih]
        rw [trajectoryDrawTape_ofDigitTable]
        simp
  exact hgeneral allEpochs

theorem allChainTrajectoryDrawTape_eq_edgeMap
    (trajectories : AllChainTrajectories) :
    ∀ chains : List ChainIndex,
      (∀ chain ∈ chains, (trajectories chain).length = lifetime) →
      allChainTrajectoryDrawTape trajectories chains =
        (chains ×ˢ (allEpochs ×ˢ trajectoryChainSteps)).map
          (globalChainEdgeTableOfTrajectories trajectories) := by
  intro chains
  induction chains with
  | nil => simp
  | cons chain chains ih =>
      intro hlength
      have hhead := hlength chain (by simp)
      have htail : ∀ selected ∈ chains,
          (trajectories selected).length = lifetime := by
        intro selected hselected
        exact hlength selected (by simp [hselected])
      rw [allChainTrajectoryDrawTape, List.product_cons, List.map_append, ih htail]
      rw [fixedChainTrajectoryDrawTape_eq_edgeMap (trajectories chain) hhead]
      simp [globalChainEdgeTableOfTrajectories]

theorem globalTrajectoryEdgeTableOfTape_drawTape
    (trajectories : AllChainTrajectories)
    (hlength : ∀ chain, (trajectories chain).length = lifetime) :
    globalTrajectoryEdgeTableOfTape
        (allChainTrajectoryDrawTape trajectories allChains) =
      globalChainEdgeTableOfTrajectories trajectories := by
  rw [allChainTrajectoryDrawTape_eq_edgeMap trajectories allChains
    (fun chain _hchain => hlength chain)]
  exact globalTrajectoryEdgeTableOfTape_map
    (globalChainEdgeTableOfTrajectories trajectories)

set_option maxRecDepth 100000 in
theorem evalDist_uniformAllChainTrajectories_edgeTable_eq_uniform
    (secret : Epoch → ChainIndex → Digest) :
    evalDist (globalChainEdgeTableOfTrajectories <$>
      uniformAllChainTrajectories secret allChains) =
      evalDist ($ᵗ (GlobalChainEdgeIndex → Digest)) := by
  calc
    _ = evalDist (globalTrajectoryEdgeTableOfTape <$>
          ((fun trajectories =>
            allChainTrajectoryDrawTape trajectories allChains) <$>
              uniformAllChainTrajectories secret allChains)) := by
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply evalDist_bind_congr
      intro trajectories htrajectories
      have hinfo := uniformAllChainTrajectories_support_info secret allChains
        trajectories allChains_nodup htrajectories
      rw [globalTrajectoryEdgeTableOfTape_drawTape trajectories
        (fun chain => (hinfo chain (mem_allChains chain)).1)]
      simp
    _ = evalDist (globalTrajectoryEdgeTableOfTape <$>
          OracleComp.drawList ($ᵗ Digest)
            (allChains.length *
              (allEpochs.length * (chainLength - 1)))) := by
      rw [evalDist_map,
        evalDist_uniformAllChainTrajectories_drawTape secret allChains
          allChains_nodup,
        ← evalDist_map]
    _ = evalDist (globalTrajectoryEdgeTableOfTape <$>
          OracleComp.drawList ($ᵗ Digest)
            globalTrajectoryEdgeOrder.length) := by
      rw [globalTrajectoryEdgeOrder_length]
    _ = evalDist ($ᵗ (GlobalChainEdgeIndex → Digest)) :=
      evalDist_globalTrajectoryEdgeTableOfTape_drawList_eq_uniform

theorem globalChainTableMaterialEquiv_trajectories
    (secret : Epoch → ChainIndex → Digest)
    (trajectories : AllChainTrajectories)
    (htrajectories : trajectories ∈ support
      (uniformAllChainTrajectories secret allChains)) :
    globalChainTableMaterialEquiv
        (globalChainValueTableOfTrajectories trajectories) =
      (secret, globalChainEdgeTableOfTrajectories trajectories) := by
  apply Prod.ext
  · exact uniformAllChainTrajectories_support_seeds secret trajectories
      htrajectories
  · rfl

noncomputable def uniformGlobalChainTableFromTrajectories :
    ProbComp (GlobalChainValueIndex → Digest) := do
  let secret ← Concrete.sampleSecret
  let trajectories ← uniformAllChainTrajectories secret allChains
  pure (globalChainValueTableOfTrajectories trajectories)

noncomputable def sampleSecretGlobalChainMaterial :
    ProbComp ((Epoch → ChainIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest)) :=
  Prod.mk <$> Concrete.sampleSecret <*>
    ($ᵗ (GlobalChainEdgeIndex → Digest))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000000 in
theorem evalDist_sampleSecretGlobalChainMaterial_eq_independent :
    evalDist sampleSecretGlobalChainMaterial =
      evalDist independentGlobalChainTableMaterial := by
  apply SPMF.ext
  intro target
  change Pr[= target | sampleSecretGlobalChainMaterial] =
    Pr[= target | independentGlobalChainTableMaterial]
  rw [sampleSecretGlobalChainMaterial, independentGlobalChainTableMaterial,
    probOutput_seq_map_prod_mk_eq_mul,
    probOutput_seq_map_prod_mk_eq_mul]
  simp only [Concrete.probOutput_sampleSecret, probOutput_uniformSample]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000000 in
theorem evalDist_uniformGlobalChainTableFromTrajectories_eq_uniform :
    evalDist uniformGlobalChainTableFromTrajectories =
      evalDist ($ᵗ (GlobalChainValueIndex → Digest)) := by
  unfold uniformGlobalChainTableFromTrajectories
  calc
    _ = evalDist (Concrete.sampleSecret >>= fun secret =>
          uniformAllChainTrajectories secret allChains >>= fun trajectories =>
          pure (globalChainTableMaterialEquiv.symm
            (secret, globalChainEdgeTableOfTrajectories trajectories))) := by
      apply evalDist_bind_congr
      intro secret _hsecret
      apply evalDist_bind_congr
      intro trajectories htrajectories
      rw [← globalChainTableMaterialEquiv_trajectories secret trajectories
        htrajectories, globalChainTableMaterialEquiv.symm_apply_apply]
    _ = evalDist (Concrete.sampleSecret >>= fun secret =>
          (globalChainEdgeTableOfTrajectories <$>
            uniformAllChainTrajectories secret allChains) >>= fun edges =>
          pure (globalChainTableMaterialEquiv.symm (secret, edges))) := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (Concrete.sampleSecret >>= fun secret =>
          ($ᵗ (GlobalChainEdgeIndex → Digest)) >>= fun edges =>
          pure (globalChainTableMaterialEquiv.symm (secret, edges))) := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro secret
      rw [evalDist_bind,
        evalDist_uniformAllChainTrajectories_edgeTable_eq_uniform secret,
        ← evalDist_bind]
    _ = evalDist (globalChainTableMaterialEquiv.symm <$>
          sampleSecretGlobalChainMaterial) := by
      simp [sampleSecretGlobalChainMaterial, monad_norm]
    _ = evalDist (globalChainTableMaterialEquiv.symm <$>
          independentGlobalChainTableMaterial) := by
      exact evalDist_map_eq_of_evalDist_eq
        evalDist_sampleSecretGlobalChainMaterial_eq_independent
        globalChainTableMaterialEquiv.symm
    _ = evalDist ($ᵗ (GlobalChainValueIndex → Digest)) := by
      have h := evalDist_map_eq_of_evalDist_eq
        evalDist_split_uniformGlobalChainTable_eq_independent
        globalChainTableMaterialEquiv.symm
      simpa [Functor.map_map] using h.symm

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
  let secretKey : SecretKey := (SecretKey.withoutPrecomputation parameter secret)
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
  let secretKey : SecretKey := (SecretKey.withoutPrecomputation parameter secret)
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
    let secretKey : SecretKey := (SecretKey.withoutPrecomputation parameter secret)
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


theorem Concrete.fixedSeedChainTrajectoriesFromCache_avoids_leaf
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (targetEpoch : Epoch)
    (input : HashInput)
    (hinput : AtHashAddress parameter (.leaf targetEpoch) input) :
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
            (p' := AtHashAddress parameter (.leaf targetEpoch))
          · intro candidate heq
            subst candidate
            exact hinput
          · apply Concrete.chainTrajectory_queryBound_zero_of_avoids
            intro offset hoffset hvalid heq
            simp at heq
        · exact hcache
        · exact hfirst
      · exact hrest

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

theorem Concrete.allChainTrajectoriesFromCache_avoids_leaf
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (targetEpoch : Epoch) (input : HashInput)
    (hinput : AtHashAddress parameter (.leaf targetEpoch) input) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec)
      (result : AllChainTrajectories × QueryCache HashSpec),
      cache input = none →
      result ∈ support
        (Concrete.allChainTrajectoriesFromCache parameter secret cache chains) →
      result.2 input = none := by
  intro chains
  induction chains with
  | nil =>
      intro cache result hcache hresult
      simp only [Concrete.allChainTrajectoriesFromCache_nil, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact hcache
  | cons chain chains ih =>
      intro cache result hcache hresult
      rw [Concrete.allChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      apply ih first.2 rest
      · exact Concrete.fixedSeedChainTrajectoriesFromCache_avoids_leaf
          parameter secret chain (chainLength - 1) targetEpoch input hinput
            allEpochs cache first hcache hfirst
      · exact hrest

theorem Concrete.allChainTrajectoriesFromCache_avoids_merkle
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (level : MerkleLevel) (node : MerkleNode) (input : HashInput)
    (hinput : AtHashAddress parameter (.merkle level node) input) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec)
      (result : AllChainTrajectories × QueryCache HashSpec),
      cache input = none →
      result ∈ support
        (Concrete.allChainTrajectoriesFromCache parameter secret cache chains) →
      result.2 input = none := by
  intro chains
  induction chains with
  | nil =>
      intro cache result hcache hresult
      simp only [Concrete.allChainTrajectoriesFromCache_nil, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact hcache
  | cons chain chains ih =>
      intro cache result hcache hresult
      rw [Concrete.allChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      apply ih first.2 rest
      · exact Concrete.fixedSeedChainTrajectoriesFromCache_avoids_merkle
          parameter secret chain (chainLength - 1) level node input hinput
            allEpochs cache first hcache hfirst
      · exact hrest

theorem programmedAllChainTrajectories_treeValuesFresh
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (result : AllChainTrajectories × QueryCache HashSpec)
    (hresult : result ∈ support
      (programmedAllChainTrajectoriesFromCache parameter secret ∅
        allChains)) :
    TreeValuesFresh parameter allTreeValueIndices result.2 := by
  have hactual : result ∈ support
      (Concrete.allChainTrajectoriesFromCache parameter secret ∅
        allChains) := by
    apply (mem_support_iff_of_evalDist_eq
      (evalDist_allChainTrajectories_eq_programmed parameter secret allChains ∅
        allChains_nodup (by simp [AllChainAddressesAbsent])) result).mpr
    exact hresult
  intro index _hindex input hinput
  by_cases hzero : index.1.val = 0
  · unfold TreeValueIndex.domain at hinput
    rw [dif_pos hzero] at hinput
    exact Concrete.allChainTrajectoriesFromCache_avoids_leaf parameter secret
      index.node input hinput allChains ∅ result (by simp) hactual
  · unfold TreeValueIndex.domain at hinput
    rw [dif_neg hzero] at hinput
    exact Concrete.allChainTrajectoriesFromCache_avoids_merkle parameter secret
      ⟨index.1.val - 1, by omega⟩ index.node input hinput allChains ∅
        result (by simp) hactual

abbrev GlobalChainTrajectoryMaterial :=
  (Epoch → ChainIndex → Digest) ×
    (AllChainTrajectories × QueryCache HashSpec)

noncomputable def globalChainTrajectoryMaterialTable
    (material : GlobalChainTrajectoryMaterial) :
    GlobalChainValueIndex → Digest :=
  globalChainValueTableOfTrajectories material.2.1

noncomputable def programmedGlobalChainTrajectoryMaterial
    (parameter : PublicParameter) : ProbComp GlobalChainTrajectoryMaterial := do
  let secret ← Concrete.sampleSecret
  let trajectories ← programmedAllChainTrajectoriesFromCache parameter
    secret ∅ allChains
  pure (secret, trajectories)

noncomputable def programmedGlobalChainTrajectoryMaterialWithBase
    (parameter : PublicParameter) :
    ProbComp (GlobalChainTrajectoryMaterial ×
      (GlobalChainValueIndex → Digest)) := do
  let base ← $ᵗ (GlobalChainValueIndex → Digest)
  let material ← programmedGlobalChainTrajectoryMaterial parameter
  pure (material, base)

theorem programmedGlobalChainTrajectoryMaterial_support_trajectories
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter)) :
    material.2 ∈ support
      (programmedAllChainTrajectoriesFromCache parameter material.1 ∅
        allChains) := by
  unfold programmedGlobalChainTrajectoryMaterial at hmaterial
  rw [mem_support_bind_iff] at hmaterial
  obtain ⟨secret, _hsecret, htrajectories⟩ := hmaterial
  rw [mem_support_bind_iff] at htrajectories
  obtain ⟨trajectories, htrajectories, hpure⟩ := htrajectories
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst material
  exact htrajectories

theorem evalDist_programmedGlobalChainTrajectoryMaterial_table_eq_uniform
    (parameter : PublicParameter) :
    evalDist (globalChainTrajectoryMaterialTable <$>
      programmedGlobalChainTrajectoryMaterial parameter) =
      evalDist ($ᵗ (GlobalChainValueIndex → Digest)) := by
  unfold programmedGlobalChainTrajectoryMaterial
    globalChainTrajectoryMaterialTable
  simp only [map_eq_bind_pure_comp, bind_assoc]
  calc
    _ = evalDist (Concrete.sampleSecret >>= fun secret =>
          globalChainValueTableOfTrajectories <$>
            (Prod.fst <$> programmedAllChainTrajectoriesFromCache parameter
              secret ∅ allChains)) := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro secret
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (Concrete.sampleSecret >>= fun secret =>
          globalChainValueTableOfTrajectories <$>
            uniformAllChainTrajectories secret allChains) := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro secret
      rw [evalDist_map,
        evalDist_programmedAllChainTrajectories_fst_eq_uniform parameter
          secret allChains ∅,
        ← evalDist_map]
    _ = evalDist uniformGlobalChainTableFromTrajectories := rfl
    _ = evalDist ($ᵗ (GlobalChainValueIndex → Digest)) :=
      evalDist_uniformGlobalChainTableFromTrajectories_eq_uniform

def globalChainTrajectoryMaterialBase
    (result : GlobalChainTrajectoryMaterial ×
      (GlobalChainValueIndex → Digest)) :
    GlobalChainValueIndex → Digest := result.2

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
set_option linter.constructorNameAsVariable false in
theorem evalDist_programmedGlobalChainTrajectoryMaterial_table_eq_base
    (parameter : PublicParameter) :
    evalDist (globalChainTrajectoryMaterialTable <$>
        programmedGlobalChainTrajectoryMaterial parameter) =
      evalDist (globalChainTrajectoryMaterialBase <$>
        programmedGlobalChainTrajectoryMaterialWithBase parameter) := by
  calc
    _ = evalDist ($ᵗ (GlobalChainValueIndex → Digest)) :=
      evalDist_programmedGlobalChainTrajectoryMaterial_table_eq_uniform
        parameter
    _ = evalDist (globalChainTrajectoryMaterialBase <$>
        programmedGlobalChainTrajectoryMaterialWithBase parameter) := by
      unfold programmedGlobalChainTrajectoryMaterialWithBase
        globalChainTrajectoryMaterialBase
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
      symm
      calc
        _ = evalDist ($ᵗ (GlobalChainValueIndex → Digest) >>= fun base =>
              pure base) := by
          apply evalDist_bind_congr
          intro base _hbase
          exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
            (programmedGlobalChainTrajectoryMaterial parameter)
            (probFailure_eq_zero' inferInstance) (pure base)
        _ = _ := by simp

structure CoupledGlobalChainKeygenView where
  secret : Epoch → ChainIndex → Digest
  table : GlobalChainValueIndex → Digest
  values : List Digest
  cache : QueryCache HashSpec

def CoupledGlobalChainKeygenView.root
    (parameter : PublicParameter) (view : CoupledGlobalChainKeygenView) :
    Digest :=
  Concrete.CacheReplay.treeNode view.cache parameter view.secret
    treeHeight Concrete.rootNode

def CoupledGlobalChainKeygenView.authenticationPath
    (parameter : PublicParameter) (view : CoupledGlobalChainKeygenView)
    (epoch : Epoch) : MerkleLevel → Digest :=
  Concrete.CacheReplay.authenticationPath view.cache
    (SecretKey.withoutPrecomputation parameter view.secret) epoch

noncomputable def coupledGlobalChainKeygenExperiment
    (parameter : PublicParameter) : ProbComp CoupledGlobalChainKeygenView := do
  let material ← programmedGlobalChainTrajectoryMaterial parameter
  let tree ← treeValues parameter material.1 allTreeValueIndices
    material.2.2
  pure {
    secret := material.1
    table := globalChainTrajectoryMaterialTable material
    values := tree.1
    cache := tree.2
  }

def CoupledGlobalChainKeygenRelation
    (parameter : PublicParameter)
    (left : CoupledGlobalChainKeygenView)
    (right : CoupledGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  left.table = right.2 ∧
    left.root parameter = right.1.root parameter ∧
    (∀ epoch,
      left.authenticationPath parameter epoch =
        right.1.authenticationPath parameter epoch) ∧
    left.values = right.1.values ∧
    TreeValuesReplay parameter left.secret left.cache
      allTreeValueIndices left.values ∧
    TreeValuesReplay parameter right.1.secret right.1.cache
      allTreeValueIndices right.1.values

theorem programmedGlobalChainTrajectoryMaterial_table_eq_keygenTable
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (tree : List Digest × QueryCache HashSpec)
    (htree : tree ∈ support
      (treeValues parameter material.1 allTreeValueIndices material.2.2)) :
    globalChainTrajectoryMaterialTable material =
      globalKeygenChainValueTable tree.2
        (SecretKey.withoutPrecomputation parameter material.1) := by
  have hprogrammed :=
    programmedGlobalChainTrajectoryMaterial_support_trajectories parameter
      material hmaterial
  have hactual : material.2 ∈ support
      (Concrete.allChainTrajectoriesFromCache parameter material.1 ∅
        allChains) := by
    apply (mem_support_iff_of_evalDist_eq
      (evalDist_allChainTrajectories_eq_programmed parameter material.1
        allChains ∅ allChains_nodup
          (by simp [AllChainAddressesAbsent])) material.2).mpr
    exact hprogrammed
  exact Concrete.allChainTrajectoriesFromCache_globalTable_eq parameter
    material.1 material.2 tree.2 hactual
      (treeValues_cache_le parameter material.1 allTreeValueIndices
        material.2.2 tree htree)

def CoupledGlobalChainKeygenView.toProgrammedView
    (parameter : PublicParameter) (view : CoupledGlobalChainKeygenView) :
    ProgrammedGlobalChainKeygenView := {
  publicKey := ⟨view.root parameter, parameter⟩
  secretKey := SecretKey.withoutPrecomputation parameter view.secret
  cache := view.cache
  table := view.table
}

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_coupledGlobalChainKeygen_toProgrammedView_eq
    (parameter : PublicParameter) :
    evalDist (CoupledGlobalChainKeygenView.toProgrammedView parameter <$>
      coupledGlobalChainKeygenExperiment parameter) =
    evalDist (programmedGlobalChainTrajectoryMaterial parameter >>=
      fun material =>
      (simulateQ randomOracle
        (Concrete.treeNode parameter material.1 treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run material.2.2 >>= fun rootResult =>
      pure ({
        publicKey := ⟨rootResult.1, parameter⟩
        secretKey := SecretKey.withoutPrecomputation parameter material.1
        cache := rootResult.2
        table := globalKeygenChainValueTable rootResult.2
          (SecretKey.withoutPrecomputation parameter material.1)
      } : ProgrammedGlobalChainKeygenView)) := by
  unfold coupledGlobalChainKeygenExperiment
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply evalDist_bind_congr
  intro material hmaterial
  let finish : Digest × QueryCache HashSpec →
      ProbComp ProgrammedGlobalChainKeygenView := fun rootResult => pure {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey := SecretKey.withoutPrecomputation parameter material.1
    cache := rootResult.2
    table := globalKeygenChainValueTable rootResult.2
      (SecretKey.withoutPrecomputation parameter material.1)
  }
  symm
  calc
    evalDist ((simulateQ randomOracle
          (Concrete.treeNode parameter material.1 treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run material.2.2 >>= finish) =
      evalDist (((fun tree : List Digest × QueryCache HashSpec =>
          (Concrete.CacheReplay.treeNode tree.2 parameter material.1
            treeHeight Concrete.rootNode, tree.2)) <$>
            treeValues parameter material.1 allTreeValueIndices
              material.2.2) >>= finish) := by
        rw [evalDist_bind,
          evalDist_rootTree_run_eq_treeValues_root_cache,
          ← evalDist_bind]
    _ = evalDist (treeValues parameter material.1 allTreeValueIndices
          material.2.2 >>= fun tree =>
        pure (CoupledGlobalChainKeygenView.toProgrammedView parameter {
          secret := material.1
          table := globalChainTrajectoryMaterialTable material
          values := tree.1
          cache := tree.2
        })) := by
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply evalDist_bind_congr
      intro tree htree
      unfold finish CoupledGlobalChainKeygenView.toProgrammedView
        CoupledGlobalChainKeygenView.root
      rw [programmedGlobalChainTrajectoryMaterial_table_eq_keygenTable
        parameter material hmaterial tree htree]

noncomputable def coupledGlobalChainKeygen :
    ProbComp ProgrammedGlobalChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let view ← coupledGlobalChainKeygenExperiment parameter
  pure (view.toProgrammedView parameter)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_coupledGlobalChainKeygen_eq_programmedTrajectories :
    evalDist coupledGlobalChainKeygen =
      evalDist (eraseAllChainTrajectories <$>
        programmedAllChainTrajectoryKeygen) := by
  unfold coupledGlobalChainKeygen programmedAllChainTrajectoryKeygen
    eraseAllChainTrajectories
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  change evalDist
      (CoupledGlobalChainKeygenView.toProgrammedView parameter <$>
        coupledGlobalChainKeygenExperiment parameter) = _
  rw [evalDist_coupledGlobalChainKeygen_toProgrammedView_eq parameter]
  unfold programmedGlobalChainTrajectoryMaterial
  simp only [bind_assoc, pure_bind]

def ProgrammedGlobalChainKeygenRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  left.table = right.2 ∧
    left.publicKey = right.1.publicKey ∧
    (∀ epoch,
      Concrete.CacheReplay.authenticationPath left.cache left.secretKey epoch =
        Concrete.CacheReplay.authenticationPath right.1.cache
          right.1.secretKey epoch)

def ProgrammedGlobalChainKeygenFullRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  ProgrammedGlobalChainKeygenRelation left right ∧
    ∃ values,
      TreeValuesReplay left.secretKey.parameter left.secretKey.chainStart
        left.cache allTreeValueIndices values ∧
      TreeValuesReplay right.1.secretKey.parameter
        right.1.secretKey.chainStart right.1.cache allTreeValueIndices values

end XmssSecurity.CappedChain
