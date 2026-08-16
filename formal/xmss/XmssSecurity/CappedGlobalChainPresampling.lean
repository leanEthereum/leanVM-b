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

noncomputable def globalChainTableEdgeTargets
    (table : GlobalChainValueIndex → Digest) : List Digest :=
  allGlobalChainEdges.map (globalChainTableEdgeTarget table)

noncomputable def programGlobalChainTableEdgesTrace
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) :
    List GlobalChainEdgeIndex →
      ProbComp (List HashOutput × QueryCache HashSpec)
  | [] => pure ([], cache)
  | edge :: edges => do
      let output ← Rom.sampleHashOutputWithDigest
        (globalChainTableEdgeTarget table edge)
      let rest ← programGlobalChainTableEdgesTrace
        (cache.cacheQuery (globalChainTableEdgeInput parameter table edge) output)
        parameter table edges
      return (output :: rest.1, rest.2)

@[simp]
theorem programGlobalChainTableEdgesTrace_nil
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) :
    programGlobalChainTableEdgesTrace cache parameter table [] =
      pure ([], cache) := rfl

theorem programGlobalChainTableEdgesTrace_cons
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) (edges : List GlobalChainEdgeIndex) :
    programGlobalChainTableEdgesTrace cache parameter table (edge :: edges) = (do
      let output ← Rom.sampleHashOutputWithDigest
        (globalChainTableEdgeTarget table edge)
      let rest ← programGlobalChainTableEdgesTrace
        (cache.cacheQuery (globalChainTableEdgeInput parameter table edge) output)
        parameter table edges
      return (output :: rest.1, rest.2)) := rfl

theorem programGlobalChainTableEdgesTrace_neverFail
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (edges : List GlobalChainEdgeIndex) :
    NeverFail (programGlobalChainTableEdgesTrace cache parameter table edges) := by
  induction edges generalizing cache with
  | nil => simp
  | cons edge edges ih =>
      rw [programGlobalChainTableEdgesTrace_cons]
      simp only [neverFail_bind_iff]
      constructor
      · infer_instance
      · intro output _houtput
        constructor
        · exact ih _
        · intro rest _hrest
          infer_instance

theorem evalDist_programGlobalChainTableEdgesTrace_discard
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (edges : List GlobalChainEdgeIndex) :
    evalDist (programGlobalChainTableEdgesTrace cache parameter table edges >>=
      fun _result => (pure table : ProbComp
        (GlobalChainValueIndex → Digest))) =
      evalDist (pure table : ProbComp (GlobalChainValueIndex → Digest)) :=
  OracleComp.DeferredSampling.evalDist_bind_const_neverFails
    (programGlobalChainTableEdgesTrace cache parameter table edges)
    (probFailure_eq_zero'
      (programGlobalChainTableEdgesTrace_neverFail cache parameter table edges))
    (pure table : ProbComp (GlobalChainValueIndex → Digest))

set_option linter.constructorNameAsVariable false in
theorem programGlobalChainTableEdgesTrace_support_info
    (parameter : PublicParameter) (table : GlobalChainValueIndex → Digest) :
    ∀ (edges : List GlobalChainEdgeIndex) (cache : QueryCache HashSpec),
      edges.Nodup →
      (∀ edge ∈ edges,
        cache (globalChainTableEdgeInput parameter table edge) = none) →
      ∀ result ∈ support
        (programGlobalChainTableEdgesTrace cache parameter table edges),
        result.1.length = edges.length ∧ cache ≤ result.2 ∧
          List.Forall₂
            (fun edge output =>
              result.2 (globalChainTableEdgeInput parameter table edge) =
                  some output ∧
                truncateHash output = globalChainTableEdgeTarget table edge)
            edges result.1 := by
  intro edges
  induction edges with
  | nil =>
      intro cache _hnodup _habsent result hresult
      simp only [programGlobalChainTableEdgesTrace_nil, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp
  | cons edge edges ih =>
      intro cache hnodup habsent result hresult
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [programGlobalChainTableEdgesTrace_cons, mem_support_bind_iff] at hresult
      obtain ⟨output, houtput, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      have htailAbsent : ∀ target ∈ edges,
          (cache.cacheQuery
            (globalChainTableEdgeInput parameter table edge) output)
            (globalChainTableEdgeInput parameter table target) = none := by
        intro target htarget
        rw [QueryCache.cacheQuery_of_ne]
        · exact habsent target (by simp [htarget])
        · intro heq
          exact hnotMem
            ((globalChainTableEdgeInput_injective parameter table) heq.symm ▸
              htarget)
      obtain ⟨hlength, hcacheLe, hpairs⟩ :=
        ih (cache.cacheQuery
          (globalChainTableEdgeInput parameter table edge) output)
          htailNodup htailAbsent rest hrest
      refine ⟨by simp [hlength], ?_, ?_⟩
      · exact (QueryCache.le_cacheQuery cache
          (habsent edge (by simp))).trans hcacheLe
      · apply List.Forall₂.cons
        · constructor
          · exact hcacheLe (QueryCache.cacheQuery_self cache
              (globalChainTableEdgeInput parameter table edge) output)
          · exact Rom.sampleHashOutputWithDigest_support_truncate _ _ houtput
        · exact hpairs

theorem programAllGlobalChainTableEdgesTrace_edgesMatch
    (parameter : PublicParameter) (table : GlobalChainValueIndex → Digest)
    (result : List HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support
      (programGlobalChainTableEdgesTrace ∅ parameter table
        allGlobalChainEdges)) :
    GlobalChainTableEdgesMatch result.2 parameter table := by
  have hinfo := programGlobalChainTableEdgesTrace_support_info parameter table
    allGlobalChainEdges ∅ allGlobalChainEdges_nodup (by simp) result hresult
  intro edge
  obtain ⟨output, hcache, htruncate⟩ :=
    exists_right_of_forall₂ hinfo.2.2 edge (mem_allGlobalChainEdges edge)
  exact ⟨output, hcache, htruncate⟩

theorem globalChainTableSeedTargets_materialEquiv_symm
    (seeds : Epoch → ChainIndex → Digest)
    (edges : GlobalChainEdgeIndex → Digest) :
    globalChainTableSeedTargets
      (globalChainTableMaterialEquiv.symm (seeds, edges)) = seeds := by
  have hmaterial := globalChainTableMaterialEquiv.apply_symm_apply (seeds, edges)
  exact congrArg Prod.fst hmaterial

theorem globalChainTableEdgeTarget_materialEquiv_symm
    (seeds : Epoch → ChainIndex → Digest)
    (edges : GlobalChainEdgeIndex → Digest) :
    globalChainTableEdgeTarget
      (globalChainTableMaterialEquiv.symm (seeds, edges)) = edges := by
  have hmaterial := globalChainTableMaterialEquiv.apply_symm_apply (seeds, edges)
  exact congrArg Prod.snd hmaterial

theorem globalChainTableSeedsMatch_materialEquiv_symm
    (parameter : PublicParameter) (seeds : Epoch → ChainIndex → Digest)
    (edges : GlobalChainEdgeIndex → Digest) :
    GlobalChainTableSeedsMatch ⟨parameter, seeds⟩
      (globalChainTableMaterialEquiv.symm (seeds, edges)) := by
  intro epoch chain
  have hseed := congrFun (congrFun
    (globalChainTableSeedTargets_materialEquiv_symm seeds edges) epoch) chain
  simpa [globalChainTableSeedTargets] using hseed.symm

theorem globalChainTableSeedsMatch_local
    (secretKey : SecretKey) (table : GlobalChainValueIndex → Digest)
    (hmatches : GlobalChainTableSeedsMatch secretKey table)
    (chain : ChainIndex) :
    XmssSecurity.CappedChain.ChainTableSeedsMatch secretKey chain
      (fun index => table (chain, index)) := by
  intro epoch
  exact hmatches epoch chain

theorem globalChainTableEdgesMatch_local
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (hmatches : GlobalChainTableEdgesMatch cache parameter table)
    (chain : ChainIndex) :
    XmssSecurity.CappedChain.ChainTableEdgesMatch cache parameter chain
      (fun index => table (chain, index)) := by
  intro edge
  obtain ⟨output, hcached, htarget⟩ := hmatches (chain, edge)
  refine ⟨output, ?_, ?_⟩
  · have hdigit : XmssSecurity.CappedChain.chainStepDigit edge.2 =
        XmssSecurity.chainStepDigit edge.2 := by
      apply Fin.ext
      rfl
    simp only [globalChainTableEdgeInput] at hcached
    rw [hdigit] at hcached
    exact hcached
  · simpa [globalChainTableEdgeTarget,
      XmssSecurity.CappedChain.chainTableEdgeTarget] using htarget

theorem globalKeygenChainValueTable_eq_of_matches
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (table : GlobalChainValueIndex → Digest)
    (hseeds : GlobalChainTableSeedsMatch secretKey table)
    (hedges : GlobalChainTableEdgesMatch cache secretKey.parameter table) :
    globalKeygenChainValueTable cache secretKey = table := by
  funext index
  have hlocal := XmssSecurity.CappedChain.keygenChainValueTable_eq_of_matches
    cache secretKey index.1
    (fun coordinate => table (index.1, coordinate))
    (globalChainTableSeedsMatch_local secretKey table hseeds index.1)
    (globalChainTableEdgesMatch_local cache secretKey.parameter table hedges
      index.1)
  exact congrFun hlocal index.2

noncomputable def programmedGlobalChainKeygenFor
    (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) :
    ProbComp ProgrammedGlobalChainKeygenView := do
  let secret := globalChainTableSeedTargets table
  let edgeResult ← programGlobalChainTableEdgesTrace ∅ parameter table
    allGlobalChainEdges
  let rootResult ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)).run edgeResult.2
  return {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey := ⟨parameter, secret⟩
    cache := rootResult.2
    table
  }

noncomputable def programmedGlobalChainKeygen :
    ProbComp ProgrammedGlobalChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let table ← $ᵗ (GlobalChainValueIndex → Digest)
  programmedGlobalChainKeygenFor parameter table

theorem programmedGlobalChainKeygenFor_neverFail
    (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) :
    NeverFail (programmedGlobalChainKeygenFor parameter table) := by
  unfold programmedGlobalChainKeygenFor
  simp only [neverFail_bind_iff]
  constructor
  · exact programGlobalChainTableEdgesTrace_neverFail ∅ parameter table
      allGlobalChainEdges
  · intro edgeResult _hedgeResult
    constructor
    · exact neverFail_simulateQ_randomOracle_run
        (Concrete.treeNode parameter (globalChainTableSeedTargets table)
          treeHeight Concrete.rootNode : OracleComp HashSpec Digest)
        edgeResult.2
    · intro rootResult _hrootResult
      infer_instance

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
set_option linter.constructorNameAsVariable false in
theorem programmedGlobalChainKeygen_support_table
    (result : ProgrammedGlobalChainKeygenView)
    (hresult : result ∈ support programmedGlobalChainKeygen) :
    globalKeygenChainValueTable result.cache result.secretKey = result.table := by
  unfold programmedGlobalChainKeygen at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨parameter, _hparameter, htable⟩ := hresult
  rw [mem_support_bind_iff] at htable
  obtain ⟨table, _htable, hedge⟩ := htable
  unfold programmedGlobalChainKeygenFor at hedge
  rw [mem_support_bind_iff] at hedge
  obtain ⟨edgeResult, hedge, hroot⟩ := hedge
  rw [mem_support_bind_iff] at hroot
  obtain ⟨rootResult, hroot, hpure⟩ := hroot
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  rcases hpure with rfl
  apply globalKeygenChainValueTable_eq_of_matches
  · change GlobalChainTableSeedsMatch
      ⟨parameter, globalChainTableSeedTargets table⟩ table
    intro epoch chain
    rfl
  · exact (programAllGlobalChainTableEdgesTrace_edgesMatch parameter table
      edgeResult hedge).mono
        (Concrete.CacheReplay.randomOracle_cache_le
          (Concrete.treeNode parameter (globalChainTableSeedTargets table)
            treeHeight Concrete.rootNode : OracleComp HashSpec Digest)
          edgeResult.2 rootResult hroot)

noncomputable def programmedGlobalChainKeygenTableOnly :
    ProbComp (GlobalChainValueIndex → Digest) :=
  ProgrammedGlobalChainKeygenView.table <$> programmedGlobalChainKeygen

theorem evalDist_programmedGlobalChainKeygenFor_table
    (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) :
    evalDist (ProgrammedGlobalChainKeygenView.table <$>
      programmedGlobalChainKeygenFor parameter table) =
      evalDist (pure table : ProbComp (GlobalChainValueIndex → Digest)) := by
  unfold programmedGlobalChainKeygenFor
  simp only [map_bind, bind_pure_comp]
  calc
    _ = evalDist (programGlobalChainTableEdgesTrace ∅ parameter table
          allGlobalChainEdges >>= fun _edgeResult =>
        (pure table : ProbComp (GlobalChainValueIndex → Digest))) := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro edgeResult
      simpa [map_eq_bind_pure_comp, bind_assoc] using
        (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        ((simulateQ randomOracle
          (Concrete.treeNode parameter (globalChainTableSeedTargets table)
            treeHeight Concrete.rootNode : OracleComp HashSpec Digest)).run
              edgeResult.2)
        (probFailure_eq_zero' (neverFail_simulateQ_randomOracle_run
          (Concrete.treeNode parameter (globalChainTableSeedTargets table)
            treeHeight Concrete.rootNode : OracleComp HashSpec Digest)
          edgeResult.2))
        (pure table : ProbComp (GlobalChainValueIndex → Digest)))
    _ = evalDist (pure table :
        ProbComp (GlobalChainValueIndex → Digest)) :=
      evalDist_programGlobalChainTableEdgesTrace_discard ∅ parameter table
        allGlobalChainEdges

set_option maxRecDepth 1000000 in
theorem evalDist_programmedGlobalChainKeygenTableOnly_eq_uniform :
    evalDist programmedGlobalChainKeygenTableOnly =
      evalDist ($ᵗ (GlobalChainValueIndex → Digest)) := by
  unfold programmedGlobalChainKeygenTableOnly programmedGlobalChainKeygen
  simp only [map_bind]
  calc
    _ = evalDist (($ᵗ (GlobalChainValueIndex → Digest)) >>= fun table =>
          Concrete.samplePublicParameter >>= fun parameter =>
          ProgrammedGlobalChainKeygenView.table <$>
            programmedGlobalChainKeygenFor parameter table) :=
      OracleComp.DeferredSampling.evalDist_bind_comm
        Concrete.samplePublicParameter
        ($ᵗ (GlobalChainValueIndex → Digest))
        (fun parameter table => ProgrammedGlobalChainKeygenView.table <$>
          programmedGlobalChainKeygenFor parameter table)
    _ = evalDist (($ᵗ (GlobalChainValueIndex → Digest)) >>= fun table =>
          (pure table : ProbComp (GlobalChainValueIndex → Digest))) := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      calc
        _ = evalDist (Concrete.samplePublicParameter >>= fun _parameter =>
              (pure table : ProbComp
                (GlobalChainValueIndex → Digest))) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro parameter
          exact evalDist_programmedGlobalChainKeygenFor_table parameter table
        _ = evalDist (pure table :
            ProbComp (GlobalChainValueIndex → Digest)) :=
          OracleComp.DeferredSampling.evalDist_bind_const_neverFails
            Concrete.samplePublicParameter (probFailure_eq_zero' inferInstance)
            (pure table : ProbComp (GlobalChainValueIndex → Digest))
    _ = evalDist ($ᵗ (GlobalChainValueIndex → Digest)) := by
      simp

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

noncomputable def allChains : List ChainIndex :=
  Finset.univ.toList

theorem allChains_nodup : allChains.Nodup := by
  exact Finset.nodup_toList _

theorem mem_allChains (chain : ChainIndex) : chain ∈ allChains := by
  simp [allChains]

noncomputable def Concrete.warmAllChains
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    List ChainIndex → OracleComp HashSpec Unit
  | [] => pure ()
  | chain :: chains => do
      let _ ← Concrete.warmFixedChainEpochs parameter secret chain allEpochs
      Concrete.warmAllChains parameter secret chains

@[simp]
theorem Concrete.warmAllChains_nil
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    Concrete.warmAllChains parameter secret [] = pure () := rfl

theorem Concrete.warmAllChains_cons
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (chains : List ChainIndex) :
    Concrete.warmAllChains parameter secret (chain :: chains) = (do
      let _ ← Concrete.warmFixedChainEpochs parameter secret chain allEpochs
      Concrete.warmAllChains parameter secret chains) := rfl

theorem evalDist_rootTree_run_eq_warmAllChains_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chains : List ChainIndex) (initialCache : QueryCache HashSpec) :
    𝒟[(simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache] =
      𝒟[(simulateQ randomOracle
        (Concrete.warmAllChains parameter secret chains)).run initialCache >>=
          fun warmResult =>
            (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run warmResult.2] := by
  induction chains generalizing initialCache with
  | nil => simp
  | cons chain chains ih =>
      calc
        𝒟[(simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run initialCache] =
          𝒟[(simulateQ randomOracle
            (Concrete.warmFixedChainEpochs parameter secret chain allEpochs)).run
              initialCache >>= fun firstResult =>
                (simulateQ randomOracle
                  (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                    OracleComp HashSpec Digest)).run firstResult.2] :=
          evalDist_rootTree_run_eq_warmFixedChainEpochs_then_rootTree
            parameter secret chain allEpochs initialCache
        _ = 𝒟[(simulateQ randomOracle
            (Concrete.warmFixedChainEpochs parameter secret chain allEpochs)).run
              initialCache >>= fun firstResult =>
                (simulateQ randomOracle
                  (Concrete.warmAllChains parameter secret chains)).run
                    firstResult.2 >>= fun restResult =>
                (simulateQ randomOracle
                  (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                    OracleComp HashSpec Digest)).run restResult.2] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro firstResult
          exact ih firstResult.2
        _ = 𝒟[(simulateQ randomOracle
            (Concrete.warmAllChains parameter secret (chain :: chains))).run
              initialCache >>= fun warmResult =>
                (simulateQ randomOracle
                  (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                    OracleComp HashSpec Digest)).run warmResult.2] := by
          rw [Concrete.warmAllChains_cons, simulateQ_bind, StateT.run_bind]
          simp only [bind_assoc]

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
  let secretKey : SecretKey := ⟨parameter, secret⟩
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

noncomputable def chronologicallyWarmedGlobalChainKeygen :
    ProbComp ProgrammedGlobalChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let secret ← Concrete.sampleSecret
  let warmResult ← (simulateQ randomOracle
    (Concrete.warmAllChains parameter secret allChains)).run ∅
  let rootResult ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)).run warmResult.2
  let secretKey : SecretKey := ⟨parameter, secret⟩
  return {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey
    cache := rootResult.2
    table := globalKeygenChainValueTable rootResult.2 secretKey
  }

theorem evalDist_explicitGlobalChainKeygen_eq_chronologicallyWarmed :
    evalDist explicitGlobalChainKeygen =
      evalDist chronologicallyWarmedGlobalChainKeygen := by
  unfold explicitGlobalChainKeygen chronologicallyWarmedGlobalChainKeygen
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secret
  let finish : Digest × QueryCache HashSpec →
      ProbComp ProgrammedGlobalChainKeygenView := fun rootResult =>
    let secretKey : SecretKey := ⟨parameter, secret⟩
    pure ({
      publicKey := ⟨rootResult.1, parameter⟩
      secretKey
      cache := rootResult.2
      table := globalKeygenChainValueTable rootResult.2 secretKey
    } : ProgrammedGlobalChainKeygenView)
  change evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run ∅ >>= finish) =
    evalDist ((simulateQ randomOracle
      (Concrete.warmAllChains parameter secret allChains)).run ∅ >>=
        fun warmResult =>
      (simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run warmResult.2 >>= finish)
  conv_lhs => rw [evalDist_bind]
  conv_rhs => rw [evalDist_bind]
  rw [evalDist_rootTree_run_eq_warmAllChains_then_rootTree parameter secret
    allChains ∅]
  simp only [evalDist_bind, bind_assoc]

theorem evalDist_actualGlobalChainKeygen_eq_chronologicallyWarmed :
    evalDist actualGlobalChainKeygen =
      evalDist chronologicallyWarmedGlobalChainKeygen :=
  evalDist_actualGlobalChainKeygen_eq_explicit.trans
    evalDist_explicitGlobalChainKeygen_eq_chronologicallyWarmed

end XmssSecurity.CappedChain
