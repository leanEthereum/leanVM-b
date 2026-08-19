import XmssSecurity.Proof.CappedGlobalChainTable
import XmssSecurity.Proof.CappedChain.ChainTablePresampling

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

noncomputable def globalChainEdgeTableTapeEquiv :
    (GlobalChainEdgeIndex → Digest) ≃
      (Fin allGlobalChainEdges.length → Digest) :=
  (Equiv.piCongrLeft (fun _ : GlobalChainEdgeIndex => Digest)
    (allGlobalChainEdges_nodup.getEquivOfForallMemList
      allGlobalChainEdges mem_allGlobalChainEdges)).symm

theorem listOfFn_globalChainEdgeTableTapeEquiv
    (table : GlobalChainEdgeIndex → Digest) :
    List.ofFn (globalChainEdgeTableTapeEquiv table) =
      allGlobalChainEdges.map table := by
  rw [← List.ofFn_get (allGlobalChainEdges.map table)]
  apply List.ext_get
  · simp
  · intro index hleft hright
    simp [globalChainEdgeTableTapeEquiv]

noncomputable def globalChainEdgeTableOfTape
    (targets : List Digest) : GlobalChainEdgeIndex → Digest :=
  if hlength : targets.length = allGlobalChainEdges.length then
    globalChainEdgeTableTapeEquiv.symm fun index =>
      targets.get (Fin.cast hlength.symm index)
  else
    fun _ => 0

@[simp]
theorem globalChainEdgeTableOfTape_map
    (table : GlobalChainEdgeIndex → Digest) :
    globalChainEdgeTableOfTape (allGlobalChainEdges.map table) = table := by
  unfold globalChainEdgeTableOfTape
  split
  · rename_i hlength
    apply globalChainEdgeTableTapeEquiv.injective
    rw [globalChainEdgeTableTapeEquiv.apply_symm_apply]
    funext index
    simp [globalChainEdgeTableTapeEquiv]
  · rename_i hlength
    exact (hlength (by simp)).elim

theorem evalDist_uniformGlobalChainEdgeTableTape_eq_drawList :
    evalDist ((fun table : GlobalChainEdgeIndex → Digest =>
      allGlobalChainEdges.map table) <$>
        ($ᵗ (GlobalChainEdgeIndex → Digest))) =
      evalDist (OracleComp.drawList ($ᵗ Digest)
        allGlobalChainEdges.length) := by
  calc
    _ = evalDist (List.ofFn <$>
        (globalChainEdgeTableTapeEquiv <$>
          ($ᵗ (GlobalChainEdgeIndex → Digest)))) := by
      simp only [Functor.map_map]
      congr 2
      funext table
      exact (listOfFn_globalChainEdgeTableTapeEquiv table).symm
    _ = evalDist (List.ofFn <$>
        ($ᵗ (Fin allGlobalChainEdges.length → Digest))) := by
      rw [evalDist_map]
      rw [evalDist_map_bijective_uniform_cross
        (α := GlobalChainEdgeIndex → Digest)
        (β := Fin allGlobalChainEdges.length → Digest)
        globalChainEdgeTableTapeEquiv
          globalChainEdgeTableTapeEquiv.bijective]
      rw [← evalDist_map]
    _ = evalDist (OracleComp.drawList ($ᵗ Digest)
        allGlobalChainEdges.length) :=
      evalDist_listOfFn_uniform_eq_drawList allGlobalChainEdges.length

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_globalChainEdgeTableOfTape_drawList_eq_uniform :
    evalDist (globalChainEdgeTableOfTape <$>
      OracleComp.drawList ($ᵗ Digest) allGlobalChainEdges.length) =
    evalDist ($ᵗ (GlobalChainEdgeIndex → Digest)) := by
  calc
    _ = evalDist (globalChainEdgeTableOfTape <$>
        ((fun table : GlobalChainEdgeIndex → Digest =>
          allGlobalChainEdges.map table) <$>
            ($ᵗ (GlobalChainEdgeIndex → Digest)))) := by
      rw [evalDist_map, evalDist_map,
        evalDist_uniformGlobalChainEdgeTableTape_eq_drawList]
    _ = evalDist ($ᵗ (GlobalChainEdgeIndex → Digest)) := by
      simp [Functor.map_map]

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

def installGlobalChainTableEdgeOutputs
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) :
    List GlobalChainEdgeIndex → List HashOutput → QueryCache HashSpec
  | [], _ => cache
  | _, [] => cache
  | edge :: edges, output :: outputs =>
      installGlobalChainTableEdgeOutputs
        (cache.cacheQuery
          (globalChainTableEdgeInput parameter table edge) output)
        parameter table edges outputs

@[simp]
theorem installGlobalChainTableEdgeOutputs_nil
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (outputs : List HashOutput) :
    installGlobalChainTableEdgeOutputs cache parameter table [] outputs =
      cache := rfl

@[simp]
theorem installGlobalChainTableEdgeOutputs_cons
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) (edges : List GlobalChainEdgeIndex)
    (output : HashOutput) (outputs : List HashOutput) :
    installGlobalChainTableEdgeOutputs cache parameter table
      (edge :: edges) (output :: outputs) =
      installGlobalChainTableEdgeOutputs
        (cache.cacheQuery
          (globalChainTableEdgeInput parameter table edge) output)
        parameter table edges outputs := rfl

theorem evalDist_programGlobalChainTableEdgesTrace_eq_install
    (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) :
    ∀ (edges : List GlobalChainEdgeIndex) (cache : QueryCache HashSpec),
      evalDist (programGlobalChainTableEdgesTrace cache parameter table edges) =
      evalDist ((fun outputs =>
          (outputs, installGlobalChainTableEdgeOutputs cache parameter table
            edges outputs)) <$>
        sampleHashOutputsWithDigests
          (edges.map (globalChainTableEdgeTarget table))) := by
  intro edges
  induction edges with
  | nil =>
      intro cache
      simp
  | cons edge edges ih =>
      intro cache
      rw [programGlobalChainTableEdgesTrace_cons]
      simp only [List.map_cons, sampleHashOutputsWithDigests_cons,
        map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro output
      conv_lhs => rw [evalDist_bind]
      rw [ih]
      simp [map_eq_bind_pure_comp, bind_assoc]

theorem evalDist_programGlobalChainTableEdgesTrace_fst
    (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) :
    ∀ (edges : List GlobalChainEdgeIndex) (cache : QueryCache HashSpec),
      evalDist (Prod.fst <$>
        programGlobalChainTableEdgesTrace cache parameter table edges) =
      evalDist (sampleHashOutputsWithDigests
        (edges.map (globalChainTableEdgeTarget table))) := by
  intro edges
  induction edges with
  | nil =>
      intro cache
      simp
  | cons edge edges ih =>
      intro cache
      simp only [List.map_cons]
      rw [programGlobalChainTableEdgesTrace_cons,
        sampleHashOutputsWithDigests_cons]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro output
      change evalDist ((fun rest => output :: rest.1) <$>
          programGlobalChainTableEdgesTrace
            (cache.cacheQuery
              (globalChainTableEdgeInput parameter table edge) output)
            parameter table edges) =
        evalDist ((fun outputs => output :: outputs) <$>
          sampleHashOutputsWithDigests
            (edges.map (globalChainTableEdgeTarget table)))
      calc
        evalDist ((fun rest => output :: rest.1) <$>
            programGlobalChainTableEdgesTrace
              (cache.cacheQuery
                (globalChainTableEdgeInput parameter table edge) output)
              parameter table edges) =
            evalDist ((fun outputs => output :: outputs) <$> (Prod.fst <$>
              programGlobalChainTableEdgesTrace
                (cache.cacheQuery
                  (globalChainTableEdgeInput parameter table edge) output)
                parameter table edges)) := by
          simp [Functor.map_map]
        _ = evalDist ((fun outputs => output :: outputs) <$>
              sampleHashOutputsWithDigests
                (edges.map (globalChainTableEdgeTarget table))) := by
          rw [evalDist_map, ih, ← evalDist_map]

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

noncomputable def programmedUniformGlobalChainEdgeTape
    (parameter : PublicParameter)
    (seeds : Epoch → ChainIndex → Digest) :
    ProbComp (List Digest × List HashOutput) := do
  let edges ← $ᵗ (GlobalChainEdgeIndex → Digest)
  let table := globalChainTableMaterialEquiv.symm (seeds, edges)
  let outputs ← Prod.fst <$>
    programGlobalChainTableEdgesTrace ∅ parameter table allGlobalChainEdges
  pure (allGlobalChainEdges.map edges, outputs)

noncomputable def sampledUniformGlobalChainEdgeTape
    (seeds : Epoch → ChainIndex → Digest) :
    ProbComp (List Digest × List HashOutput) := do
  let edges ← $ᵗ (GlobalChainEdgeIndex → Digest)
  let table := globalChainTableMaterialEquiv.symm (seeds, edges)
  let outputs ← sampleHashOutputsWithDigests
    (allGlobalChainEdges.map (globalChainTableEdgeTarget table))
  pure (allGlobalChainEdges.map edges, outputs)

noncomputable def installedGlobalChainEdgeTapeResult
    (parameter : PublicParameter)
    (seeds : Epoch → ChainIndex → Digest)
    (tape : List Digest × List HashOutput) :
    List Digest × (List HashOutput × QueryCache HashSpec) :=
  let edges := globalChainEdgeTableOfTape tape.1
  let table := globalChainTableMaterialEquiv.symm (seeds, edges)
  (tape.1, (tape.2,
    installGlobalChainTableEdgeOutputs ∅ parameter table
      allGlobalChainEdges tape.2))

noncomputable def programmedUniformGlobalChainEdgeCache
    (parameter : PublicParameter)
    (seeds : Epoch → ChainIndex → Digest) :
    ProbComp (List Digest × (List HashOutput × QueryCache HashSpec)) := do
  let edges ← $ᵗ (GlobalChainEdgeIndex → Digest)
  let table := globalChainTableMaterialEquiv.symm (seeds, edges)
  let trace ← programGlobalChainTableEdgesTrace ∅ parameter table
    allGlobalChainEdges
  pure (allGlobalChainEdges.map edges, trace)

noncomputable def uniformInstalledGlobalChainEdgeCache
    (parameter : PublicParameter)
    (seeds : Epoch → ChainIndex → Digest) :
    ProbComp (List Digest × (List HashOutput × QueryCache HashSpec)) :=
  installedGlobalChainEdgeTapeResult parameter seeds <$>
    Rom.uniformHashTape allGlobalChainEdges.length

theorem evalDist_programmedUniformGlobalChainEdgeTape_eq_sampled
    (parameter : PublicParameter)
    (seeds : Epoch → ChainIndex → Digest) :
    evalDist (programmedUniformGlobalChainEdgeTape parameter seeds) =
      evalDist (sampledUniformGlobalChainEdgeTape seeds) := by
  unfold programmedUniformGlobalChainEdgeTape
    sampledUniformGlobalChainEdgeTape
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro edges
  conv_lhs => rw [evalDist_bind]
  conv_rhs => rw [evalDist_bind]
  rw [evalDist_programGlobalChainTableEdgesTrace_fst]

theorem evalDist_programmedGlobalChainEdgeCache_fixedTable_eq_installed
    (parameter : PublicParameter)
    (seeds : Epoch → ChainIndex → Digest)
    (edges : GlobalChainEdgeIndex → Digest) :
    let table := globalChainTableMaterialEquiv.symm (seeds, edges)
    evalDist ((fun trace => (allGlobalChainEdges.map edges, trace)) <$>
      programGlobalChainTableEdgesTrace ∅ parameter table
        allGlobalChainEdges) =
    evalDist (installedGlobalChainEdgeTapeResult parameter seeds <$>
      ((fun outputs => (allGlobalChainEdges.map edges, outputs)) <$>
        sampleHashOutputsWithDigests
          (allGlobalChainEdges.map
            (globalChainTableEdgeTarget table)))) := by
  dsimp only
  rw [evalDist_map, evalDist_programGlobalChainTableEdgesTrace_eq_install,
    ← evalDist_map]
  simp [Functor.map_map, installedGlobalChainEdgeTapeResult]

theorem evalDist_programmedUniformGlobalChainEdgeTape_eq_uniformHashTape
    (parameter : PublicParameter)
    (seeds : Epoch → ChainIndex → Digest) :
    evalDist (programmedUniformGlobalChainEdgeTape parameter seeds) =
      evalDist (Rom.uniformHashTape allGlobalChainEdges.length) := by
  calc
    _ = evalDist (sampledUniformGlobalChainEdgeTape seeds) :=
      evalDist_programmedUniformGlobalChainEdgeTape_eq_sampled parameter seeds
    _ = evalDist (($ᵗ (GlobalChainEdgeIndex → Digest)) >>= fun edges =>
          sampleHashOutputsWithDigests (allGlobalChainEdges.map edges) >>=
            fun outputs => pure (allGlobalChainEdges.map edges, outputs)) := by
      unfold sampledUniformGlobalChainEdgeTape
      simp only [globalChainTableEdgeTarget_materialEquiv_symm]
    _ = evalDist (((fun edges : GlobalChainEdgeIndex → Digest =>
          allGlobalChainEdges.map edges) <$>
            ($ᵗ (GlobalChainEdgeIndex → Digest))) >>= fun targets =>
          sampleHashOutputsWithDigests targets >>= fun outputs =>
            pure (targets, outputs)) := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (OracleComp.drawList ($ᵗ Digest)
          allGlobalChainEdges.length >>= fun targets =>
        sampleHashOutputsWithDigests targets >>= fun outputs =>
          pure (targets, outputs)) := by
      rw [evalDist_bind,
        evalDist_uniformGlobalChainEdgeTableTape_eq_drawList,
        ← evalDist_bind]
    _ = evalDist (batchProgrammedHashTape allGlobalChainEdges.length) := by
      rfl
    _ = evalDist (Rom.programmedHashTape allGlobalChainEdges.length) :=
      evalDist_batchProgrammedHashTape_eq_programmedHashTape
        allGlobalChainEdges.length
    _ = evalDist (Rom.uniformHashTape allGlobalChainEdges.length) :=
      Rom.evalDist_programmedHashTape_eq_uniformHashTape
        allGlobalChainEdges.length

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
theorem evalDist_programmedUniformGlobalChainEdgeCache_eq_uniformInstalled
    (parameter : PublicParameter)
    (seeds : Epoch → ChainIndex → Digest) :
    evalDist (programmedUniformGlobalChainEdgeCache parameter seeds) =
      evalDist (uniformInstalledGlobalChainEdgeCache parameter seeds) := by
  calc
    _ = evalDist (installedGlobalChainEdgeTapeResult parameter seeds <$>
        sampledUniformGlobalChainEdgeTape seeds) := by
      unfold programmedUniformGlobalChainEdgeCache
        sampledUniformGlobalChainEdgeTape
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro edges
      simpa [map_eq_bind_pure_comp, bind_assoc] using
        (evalDist_programmedGlobalChainEdgeCache_fixedTable_eq_installed
          parameter seeds edges)
    _ = evalDist (installedGlobalChainEdgeTapeResult parameter seeds <$>
        programmedUniformGlobalChainEdgeTape parameter seeds) := by
      conv_lhs => rw [evalDist_map]
      conv_rhs => rw [evalDist_map]
      rw [← evalDist_programmedUniformGlobalChainEdgeTape_eq_sampled]
    _ = evalDist (installedGlobalChainEdgeTapeResult parameter seeds <$>
        Rom.uniformHashTape allGlobalChainEdges.length) := by
      rw [evalDist_map,
        evalDist_programmedUniformGlobalChainEdgeTape_eq_uniformHashTape,
        ← evalDist_map]
    _ = evalDist (uniformInstalledGlobalChainEdgeCache parameter seeds) := by
      rfl

theorem globalChainTableSeedsMatch_materialEquiv_symm
    (parameter : PublicParameter) (seeds : Epoch → ChainIndex → Digest)
    (edges : GlobalChainEdgeIndex → Digest) :
    GlobalChainTableSeedsMatch
      (SecretKey.withoutPrecomputation parameter seeds)
      (globalChainTableMaterialEquiv.symm (seeds, edges)) := by
  intro epoch chain
  have hseed := congrFun (congrFun
    (globalChainTableSeedTargets_materialEquiv_symm seeds edges) epoch) chain
  simpa [globalChainTableSeedTargets,
    SecretKey.withoutPrecomputation] using hseed.symm

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
    secretKey := (SecretKey.withoutPrecomputation parameter secret)
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
      (SecretKey.withoutPrecomputation parameter
        (globalChainTableSeedTargets table)) table
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

noncomputable def chronologicallyWarmedGlobalChainKeygen :
    ProbComp ProgrammedGlobalChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let secret ← Concrete.sampleSecret
  let warmResult ← (simulateQ randomOracle
    (Concrete.warmAllChains parameter secret allChains)).run ∅
  let rootResult ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)).run warmResult.2
  let secretKey : SecretKey := (SecretKey.withoutPrecomputation parameter secret)
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
    let secretKey : SecretKey := (SecretKey.withoutPrecomputation parameter secret)
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
