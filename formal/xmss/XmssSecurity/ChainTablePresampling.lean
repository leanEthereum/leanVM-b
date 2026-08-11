import XmssSecurity.ChainTableUniformity
import XmssSecurity.MixedOraclePresampling

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

abbrev ChainEdgeIndex := Epoch × ChainStep

def chainTableEdgeInput
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) (edge : ChainEdgeIndex) : HashInput :=
  Concrete.CacheView.chainInput parameter edge.1 chain edge.2
    (table (edge.1, chainStepDigit edge.2))

def chainStepNextDigit (step : ChainStep) : Digit :=
  ⟨step.val + 1, by
    have hstep := step.isLt
    omega⟩

def chainTableEdgeTarget
    (table : ChainValueIndex → Digest) (edge : ChainEdgeIndex) : Digest :=
  table (edge.1, chainStepNextDigit edge.2)

def ChainTableSeedsMatch
    (secretKey : SecretKey) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) : Prop :=
  ∀ epoch, secretKey.chainStart epoch chain = table (epoch, ⟨0, by simp [chainLength]⟩)

def chainTableSeedTargets
    (table : ChainValueIndex → Digest) : Epoch → Digest :=
  fun epoch => table (epoch, ⟨0, by simp [chainLength]⟩)

def ChainTableEdgesMatch
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (chain : ChainIndex) (table : ChainValueIndex → Digest) : Prop :=
  ∀ edge, ∃ output,
    cache (chainTableEdgeInput parameter chain table edge) = some output ∧
      truncateHash output = chainTableEdgeTarget table edge

noncomputable local instance presamplingSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

noncomputable local instance presamplingSampleableChainSeeds :
    SampleableType (Epoch → Digest) :=
  SampleableType.ofFintype (Epoch → Digest)

noncomputable local instance presamplingSampleableChainEdges :
    SampleableType (ChainEdgeIndex → Digest) :=
  SampleableType.ofFintype (ChainEdgeIndex → Digest)

noncomputable local instance presamplingSampleableChainCoordinates :
    SampleableType ((Epoch → Digest) × (ChainEdgeIndex → Digest)) :=
  SampleableType.ofFintype ((Epoch → Digest) × (ChainEdgeIndex → Digest))

/-- A chain table is equivalently its epoch seeds and the target value of every positive edge. -/
def chainTableMaterialEquiv :
    (ChainValueIndex → Digest) ≃
      ((Epoch → Digest) × (ChainEdgeIndex → Digest)) where
  toFun table :=
    (chainTableSeedTargets table, chainTableEdgeTarget table)
  invFun material index :=
    if hzero : index.2.val = 0 then
      material.1 index.1
    else
      material.2
        (index.1, ⟨index.2.val - 1, by
          have hdigit := index.2.isLt
          omega⟩)
  left_inv table := by
    funext index
    by_cases hzero : index.2.val = 0
    · simp only [hzero, ↓reduceDIte, chainTableSeedTargets]
      congr 2
      exact Fin.ext hzero.symm
    · simp only [hzero, ↓reduceDIte, chainTableEdgeTarget]
      congr 2
      apply Fin.ext
      simp [chainStepNextDigit]
      omega
  right_inv material := by
    apply Prod.ext
    · funext epoch
      simp [chainTableSeedTargets]
    · funext edge
      simp only [chainTableEdgeTarget]
      have hpositive : (chainStepNextDigit edge.2).val ≠ 0 := by
        simp [chainStepNextDigit]
      simp only [hpositive, ↓reduceDIte]
      congr 2

noncomputable def independentChainTableMaterial :
    ProbComp ((Epoch → Digest) × (ChainEdgeIndex → Digest)) :=
  Prod.mk <$> ($ᵗ (Epoch → Digest)) <*>
    ($ᵗ (ChainEdgeIndex → Digest))

/-- Splitting a uniform chain table gives independent uniform seed and positive-edge coordinate tables. -/
theorem evalDist_split_uniformChainTable_eq_independent :
    𝒟[chainTableMaterialEquiv <$> ($ᵗ (ChainValueIndex → Digest))] =
      𝒟[independentChainTableMaterial] := by
  apply SPMF.ext
  intro target
  change Pr[= target |
      chainTableMaterialEquiv <$> ($ᵗ (ChainValueIndex → Digest))] =
    Pr[= target | independentChainTableMaterial]
  rw [probOutput_map_bijective_uniform_cross
    (α := ChainValueIndex → Digest)
    (β := (Epoch → Digest) × (ChainEdgeIndex → Digest))
    chainTableMaterialEquiv chainTableMaterialEquiv.bijective]
  calc
    Pr[= target | $ᵗ ((Epoch → Digest) × (ChainEdgeIndex → Digest))] =
        Pr[= target.1 | $ᵗ (Epoch → Digest)] *
          Pr[= target.2 | $ᵗ (ChainEdgeIndex → Digest)] := by
      rw [probOutput_uniformSample, probOutput_uniformSample,
        probOutput_uniformSample, Fintype.card_prod, Nat.cast_mul,
        ENNReal.mul_inv]
      · exact Or.inr (ENNReal.natCast_ne_top _)
      · exact Or.inl (ENNReal.natCast_ne_top _)
    _ = Pr[= target | independentChainTableMaterial] := by
      symm
      rw [independentChainTableMaterial]
      rw [probOutput_seq_map_prod_mk_eq_mul]

theorem chainTableEdgeInput_injective
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) :
    Function.Injective (chainTableEdgeInput parameter chain table) := by
  rintro ⟨leftEpoch, leftStep⟩ ⟨rightEpoch, rightStep⟩ heq
  have hparts := (Concrete.CacheView.chainInput_eq_iff parameter
    leftEpoch rightEpoch chain chain leftStep rightStep
    (table (leftEpoch, chainStepDigit leftStep))
    (table (rightEpoch, chainStepDigit rightStep))).mp heq
  exact Prod.ext hparts.1 hparts.2.2.1

noncomputable def allChainEdges : List ChainEdgeIndex :=
  Finset.univ.toList

theorem allChainEdges_nodup : allChainEdges.Nodup := by
  exact (Finset.univ : Finset ChainEdgeIndex).nodup_toList

theorem mem_allChainEdges (edge : ChainEdgeIndex) : edge ∈ allChainEdges := by
  simp [allChainEdges]

theorem allChainEdges_length :
    allChainEdges.length = lifetime * (chainLength - 1) := by
  simp [allChainEdges, ChainEdgeIndex, Epoch, ChainStep]

attribute [irreducible] allChainEdges

theorem evalDist_map_truncate_drawList (count : Nat) :
    𝒟[List.map truncateHash <$>
      OracleComp.drawList ($ᵗ HashOutput) count] =
      𝒟[OracleComp.drawList ($ᵗ Digest) count] := by
  induction count with
  | zero => simp [OracleComp.drawList]
  | succ count ih =>
      simp only [OracleComp.drawList, map_eq_bind_pure_comp, bind_assoc,
        pure_bind, Function.comp_apply, List.map_cons]
      calc
        𝒟[$ᵗ HashOutput >>= fun output =>
            OracleComp.drawList ($ᵗ HashOutput) count >>= fun outputs =>
              pure (truncateHash output :: outputs.map truncateHash)] =
            𝒟[(truncateHash <$> ($ᵗ HashOutput)) >>= fun output =>
              (List.map truncateHash <$>
                OracleComp.drawList ($ᵗ HashOutput) count) >>= fun outputs =>
                pure (output :: outputs)] := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = 𝒟[$ᵗ Digest >>= fun output =>
              (List.map truncateHash <$>
                OracleComp.drawList ($ᵗ HashOutput) count) >>= fun outputs =>
                pure (output :: outputs)] := by
          conv_lhs => rw [evalDist_bind]
          conv_rhs => rw [evalDist_bind]
          rw [Rom.evalDist_truncate_uniformHashOutput]
        _ = 𝒟[$ᵗ Digest >>= fun output =>
              OracleComp.drawList ($ᵗ Digest) count >>= fun outputs =>
                pure (output :: outputs)] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro output
          conv_lhs => rw [evalDist_bind]
          conv_rhs => rw [evalDist_bind]
          rw [ih]

/-- The truncated values recorded by finite random-oracle presampling form an i.i.d. uniform digest tape. -/
theorem evalDist_presampleCacheEntriesTrace_truncate
    (cache : QueryCache HashSpec) (inputs : List HashInput) :
    𝒟[(fun result : List HashOutput × QueryCache HashSpec =>
        result.1.map truncateHash) <$>
      OracleComp.presampleCacheEntriesTrace cache inputs] =
      𝒟[OracleComp.drawList ($ᵗ Digest) inputs.length] := by
  calc
    𝒟[(fun result : List HashOutput × QueryCache HashSpec =>
          result.1.map truncateHash) <$>
        OracleComp.presampleCacheEntriesTrace cache inputs] =
        𝒟[List.map truncateHash <$>
          (Prod.fst <$>
            OracleComp.presampleCacheEntriesTrace cache inputs)] := by
      simp [Functor.map_map]
    _ = 𝒟[List.map truncateHash <$>
          OracleComp.drawList ($ᵗ HashOutput) inputs.length] := by
      rw [evalDist_map,
        OracleComp.evalDist_presampleCacheEntriesTrace_fst_eq_drawList,
        ← evalDist_map]
    _ = 𝒟[OracleComp.drawList ($ᵗ Digest) inputs.length] :=
      evalDist_map_truncate_drawList inputs.length

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
theorem drawList_truncate_probability (targets : List Digest) :
    Pr[fun outputs : List HashOutput => outputs.map truncateHash = targets |
      OracleComp.drawList ($ᵗ HashOutput) targets.length] =
      ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ targets.length) := by
  induction targets with
  | nil => simp [OracleComp.drawList]
  | cons target targets ih =>
      rw [List.length_cons, OracleComp.drawList, probEvent_bind_eq_tsum]
      let tailProbability : ℝ≥0∞ :=
        ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ targets.length)
      calc
        (∑' output : HashOutput, Pr[= output | $ᵗ HashOutput] *
            Pr[fun outputs : List HashOutput => outputs.map truncateHash = target :: targets |
              do
                let rest ← OracleComp.drawList ($ᵗ HashOutput) targets.length
                pure (output :: rest)]) =
            ∑' output : HashOutput, Pr[= output | $ᵗ HashOutput] *
              (if truncateHash output = target then tailProbability else 0) := by
          apply tsum_congr
          intro output
          congr 1
          rw [bind_pure_comp, probEvent_map]
          by_cases htarget : truncateHash output = target
          · rw [if_pos htarget]
            change Pr[fun rest : List HashOutput =>
              truncateHash output :: rest.map truncateHash = target :: targets |
                OracleComp.drawList ($ᵗ HashOutput) targets.length] = tailProbability
            simpa [htarget, tailProbability] using ih
          · rw [if_neg htarget]
            apply probEvent_eq_zero
            intro rest _ heq
            exact htarget (List.cons.inj heq).1
        _ = (∑' output : HashOutput,
              if truncateHash output = target then
                Pr[= output | $ᵗ HashOutput] else 0) * tailProbability := by
          rw [← ENNReal.tsum_mul_right]
          apply tsum_congr
          intro output
          by_cases htarget : truncateHash output = target <;> simp [htarget]
        _ = Pr[fun output : HashOutput => truncateHash output = target |
              $ᵗ HashOutput] * tailProbability := by
          rw [probEvent_eq_tsum_ite]
        _ = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ * tailProbability := by
          rw [Rom.uniform_truncate_probability]
        _ = ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^
          (target :: targets).length) := by
          simp [tailProbability, pow_succ, mul_comm]

noncomputable def chainTableEdgeInputs
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) : List HashInput :=
  allChainEdges.map (chainTableEdgeInput parameter chain table)

noncomputable def chainTableEdgeTargets
    (table : ChainValueIndex → Digest) : List Digest :=
  allChainEdges.map (chainTableEdgeTarget table)

noncomputable def programChainTableEdgesTrace
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (chain : ChainIndex) (table : ChainValueIndex → Digest) :
    List ChainEdgeIndex → ProbComp (List HashOutput × QueryCache HashSpec)
  | [] => pure ([], cache)
  | edge :: edges => do
      let output ← Rom.sampleHashOutputWithDigest
        (chainTableEdgeTarget table edge)
      let rest ← programChainTableEdgesTrace
        (cache.cacheQuery
          (chainTableEdgeInput parameter chain table edge) output)
        parameter chain table edges
      return (output :: rest.1, rest.2)

@[simp]
theorem programChainTableEdgesTrace_nil
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (chain : ChainIndex) (table : ChainValueIndex → Digest) :
    programChainTableEdgesTrace cache parameter chain table [] =
      pure ([], cache) := rfl

theorem programChainTableEdgesTrace_cons
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (chain : ChainIndex) (table : ChainValueIndex → Digest)
    (edge : ChainEdgeIndex) (edges : List ChainEdgeIndex) :
    programChainTableEdgesTrace cache parameter chain table (edge :: edges) = (do
      let output ← Rom.sampleHashOutputWithDigest
        (chainTableEdgeTarget table edge)
      let rest ← programChainTableEdgesTrace
        (cache.cacheQuery
          (chainTableEdgeInput parameter chain table edge) output)
        parameter chain table edges
      return (output :: rest.1, rest.2)) := rfl

theorem chainTableEdgeInputs_nodup
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) :
    (chainTableEdgeInputs parameter chain table).Nodup := by
  exact allChainEdges_nodup.map
    (chainTableEdgeInput_injective parameter chain table)

theorem chainTableEdgeInputs_length
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) :
    (chainTableEdgeInputs parameter chain table).length =
      lifetime * (chainLength - 1) := by
  simp [chainTableEdgeInputs, allChainEdges_length]

theorem chainTableEdgeTargets_length
    (table : ChainValueIndex → Digest) :
    (chainTableEdgeTargets table).length = lifetime * (chainLength - 1) := by
  simp [chainTableEdgeTargets, allChainEdges_length]

set_option maxHeartbeats 1600000 in
theorem presampledChainTableEdges_probability
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) :
    Pr[fun result : List HashOutput × QueryCache HashSpec =>
        result.1.map truncateHash = chainTableEdgeTargets table |
      OracleComp.presampleCacheEntriesTrace ∅
        (chainTableEdgeInputs parameter chain table)] =
      ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^
        (lifetime * (chainLength - 1))) := by
  calc
    Pr[fun result : List HashOutput × QueryCache HashSpec =>
          result.1.map truncateHash = chainTableEdgeTargets table |
        OracleComp.presampleCacheEntriesTrace ∅
          (chainTableEdgeInputs parameter chain table)] =
        Pr[fun outputs : List HashOutput =>
          outputs.map truncateHash = chainTableEdgeTargets table |
          Prod.fst <$> OracleComp.presampleCacheEntriesTrace ∅
            (chainTableEdgeInputs parameter chain table)] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun outputs : List HashOutput =>
          outputs.map truncateHash = chainTableEdgeTargets table |
          OracleComp.drawList ($ᵗ HashOutput)
            (chainTableEdgeInputs parameter chain table).length] := by
      apply probEvent_congr' (fun _ _ => Iff.rfl)
      exact OracleComp.evalDist_presampleCacheEntriesTrace_fst_eq_drawList ∅
        (chainTableEdgeInputs parameter chain table)
    _ = ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^
          (chainTableEdgeTargets table).length) := by
      simpa only [chainTableEdgeInputs_length, chainTableEdgeTargets_length] using
        drawList_truncate_probability (chainTableEdgeTargets table)
    _ = ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^
          (lifetime * (chainLength - 1))) := by
      rw [chainTableEdgeTargets_length]

theorem forall_of_forall₂_mapped
    {Edge Input Output Target : Type}
    (relation : Input → Output → Prop) (toInput : Edge → Input)
    (toTarget : Edge → Target) (project : Output → Target) :
    ∀ (edges : List Edge) (outputs : List Output),
      List.Forall₂ relation (edges.map toInput) outputs →
      outputs.map project = edges.map toTarget →
      ∀ edge ∈ edges, ∃ output,
        relation (toInput edge) output ∧ project output = toTarget edge := by
  intro edges
  induction edges with
  | nil => simp
  | cons first edges ih =>
      intro outputs hpairs htargets edge hedge
      cases hpairs with
      | cons hfirst hrest =>
          simp only [List.map_cons, List.cons.injEq] at htargets
          rcases List.mem_cons.mp hedge with heq | hedge
          · subst edge
            exact ⟨_, hfirst, htargets.1⟩
          · exact ih _ hrest htargets.2 edge hedge

theorem exists_right_of_forall₂
    {Left Right : Type} {relation : Left → Right → Prop} :
    ∀ {lefts : List Left} {rights : List Right},
      List.Forall₂ relation lefts rights →
      ∀ left ∈ lefts, ∃ right, relation left right := by
  intro lefts rights hpairs
  induction hpairs with
  | nil => simp
  | cons hfirst hrest ih =>
      intro left hmem
      rcases List.mem_cons.mp hmem with heq | hmem
      · subst left
        exact ⟨_, hfirst⟩
      · exact ih left hmem

set_option maxRecDepth 10000 in
theorem presampleCacheEntriesTrace_edgesMatch
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest)
    (result : List HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support
      (OracleComp.presampleCacheEntriesTrace ∅
        (chainTableEdgeInputs parameter chain table)))
    (htargets : result.1.map truncateHash = chainTableEdgeTargets table) :
    ChainTableEdgesMatch result.2 parameter chain table := by
  have hinfo := OracleComp.presampleCacheEntriesTrace_support_info
    (chainTableEdgeInputs parameter chain table) ∅
    (chainTableEdgeInputs_nodup parameter chain table) (by simp) result hresult
  intro edge
  exact forall_of_forall₂_mapped
    (fun input output => result.2 input = some output)
    (chainTableEdgeInput parameter chain table)
    (chainTableEdgeTarget table) truncateHash allChainEdges result.1 hinfo.2.2
    htargets edge (mem_allChainEdges edge)

set_option linter.constructorNameAsVariable false in
theorem programChainTableEdgesTrace_support_info
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) :
    ∀ (edges : List ChainEdgeIndex) (cache : QueryCache HashSpec),
      edges.Nodup →
      (∀ edge ∈ edges,
        cache (chainTableEdgeInput parameter chain table edge) = none) →
      ∀ result ∈ support
        (programChainTableEdgesTrace cache parameter chain table edges),
        result.1.length = edges.length ∧ cache ≤ result.2 ∧
          List.Forall₂
            (fun edge output =>
              result.2 (chainTableEdgeInput parameter chain table edge) = some output ∧
                truncateHash output = chainTableEdgeTarget table edge)
            edges result.1 := by
  intro edges
  induction edges with
  | nil =>
      intro cache _hnodup _habsent result hresult
      simp only [programChainTableEdgesTrace_nil, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp
  | cons edge edges ih =>
      intro cache hnodup habsent result hresult
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [programChainTableEdgesTrace_cons, mem_support_bind_iff] at hresult
      obtain ⟨output, houtput, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      have htailAbsent : ∀ target ∈ edges,
          (cache.cacheQuery
            (chainTableEdgeInput parameter chain table edge) output)
            (chainTableEdgeInput parameter chain table target) = none := by
        intro target htarget
        rw [QueryCache.cacheQuery_of_ne]
        · exact habsent target (by simp [htarget])
        · intro heq
          exact hnotMem
            ((chainTableEdgeInput_injective parameter chain table) heq.symm ▸ htarget)
      obtain ⟨hlength, hcacheLe, hpairs⟩ :=
        ih (cache.cacheQuery
          (chainTableEdgeInput parameter chain table edge) output)
          htailNodup htailAbsent rest hrest
      refine ⟨by simp [hlength], ?_, ?_⟩
      · exact (QueryCache.le_cacheQuery cache
          (habsent edge (by simp))).trans hcacheLe
      · apply List.Forall₂.cons
        · constructor
          · exact hcacheLe (QueryCache.cacheQuery_self cache
              (chainTableEdgeInput parameter chain table edge) output)
          · exact Rom.sampleHashOutputWithDigest_support_truncate _ _ houtput
        · exact hpairs

/-- Programming every candidate edge with an independent uniform high half makes the candidate table hold in the resulting cache with probability one. -/
theorem programAllChainTableEdgesTrace_edgesMatch
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest)
    (result : List HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support
      (programChainTableEdgesTrace ∅ parameter chain table allChainEdges)) :
    ChainTableEdgesMatch result.2 parameter chain table := by
  have hinfo := programChainTableEdgesTrace_support_info parameter chain table
    allChainEdges ∅ allChainEdges_nodup (by simp) result hresult
  intro edge
  obtain ⟨output, hcache, htruncate⟩ :=
    exists_right_of_forall₂ hinfo.2.2 edge (mem_allChainEdges edge)
  exact ⟨output, hcache, htruncate⟩

theorem chainWalk_eq_of_chainTable_matches
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) (table : ChainValueIndex → Digest)
    (hseeds : ChainTableSeedsMatch secretKey chain table)
    (hedges : ChainTableEdgesMatch cache secretKey.parameter chain table)
    (epoch : Epoch) (steps : Nat) (hsteps : steps < chainLength) :
    Wots.walk
      (Concrete.CacheView.chainStep cache secretKey.parameter epoch chain)
      0 steps (secretKey.chainStart epoch chain) =
      table (epoch, ⟨steps, hsteps⟩) := by
  induction steps with
  | zero =>
      exact hseeds epoch
  | succ steps ih =>
      have hstep : steps < chainLength - 1 := by omega
      let edge : ChainEdgeIndex := (epoch, ⟨steps, hstep⟩)
      obtain ⟨output, hcached, houtput⟩ := hedges edge
      simp only [Wots.walk, zero_add]
      rw [ih (by omega)]
      rw [Concrete.CacheView.chainStep_eq cache secretKey.parameter epoch chain
        steps (table (epoch, ⟨steps, by omega⟩)) hstep]
      rw [Concrete.CacheView.digestAt_eq_of_cache_eq_some]
      · simpa [chainTableEdgeTarget, chainStepNextDigit, edge] using houtput
      · simpa [chainTableEdgeInput, chainStepDigit, edge] using hcached

theorem keygenChainValueTable_eq_of_matches
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) (table : ChainValueIndex → Digest)
    (hseeds : ChainTableSeedsMatch secretKey chain table)
    (hedges : ChainTableEdgesMatch cache secretKey.parameter chain table) :
    keygenChainValueTable cache secretKey chain = table := by
  funext index
  exact chainWalk_eq_of_chainTable_matches cache secretKey chain table hseeds hedges
    index.1 index.2.val index.2.isLt

theorem keygenChainValueTable_seedsMatch
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (chain : ChainIndex) :
    ChainTableSeedsMatch secretKey chain
      (keygenChainValueTable cache secretKey chain) := by
  intro epoch
  simp [keygenChainValueTable]

set_option maxRecDepth 100000 in
theorem sampleSecret_chainTableSeedsMatch_probability
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) :
    Pr[fun secret : Epoch → ChainIndex → Digest =>
        ChainTableSeedsMatch ⟨parameter, secret⟩ chain table |
      Concrete.sampleSecret] =
      ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ lifetime) := by
  let target := chainTableSeedTargets table
  calc
    Pr[fun secret : Epoch → ChainIndex → Digest =>
          ChainTableSeedsMatch ⟨parameter, secret⟩ chain table |
        Concrete.sampleSecret] =
        Pr[= target |
          (fun secret : Epoch → ChainIndex → Digest =>
            fun epoch => secret epoch chain) <$> Concrete.sampleSecret] := by
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      apply probEvent_congr' (fun secret _ => ?_) rfl
      change (ChainTableSeedsMatch ⟨parameter, secret⟩ chain table ↔
        (fun epoch => secret epoch chain) = target)
      constructor
      · intro hmatch
        funext epoch
        exact hmatch epoch
      · intro heq epoch
        exact congrFun heq epoch
    _ = ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ lifetime) :=
      sampleSecret_fixedChain_probability chain target

noncomputable def presampledChainTableMaterial
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) :
    ProbComp ((Epoch → ChainIndex → Digest) ×
      (List HashOutput × QueryCache HashSpec)) :=
  Prod.mk <$> Concrete.sampleSecret <*>
    OracleComp.presampleCacheEntriesTrace ∅
      (chainTableEdgeInputs parameter chain table)

def ChainTableMaterialMatches
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest)
    (result : (Epoch → ChainIndex → Digest) ×
      (List HashOutput × QueryCache HashSpec)) : Prop :=
  ChainTableSeedsMatch ⟨parameter, result.1⟩ chain table ∧
    result.2.1.map truncateHash = chainTableEdgeTargets table

set_option maxHeartbeats 1600000 in
theorem presampledChainTableMaterial_probability
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) :
    Pr[ChainTableMaterialMatches parameter chain table |
      presampledChainTableMaterial parameter chain table] =
      ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^
        (lifetime * chainLength)) := by
  rw [presampledChainTableMaterial]
  calc
    Pr[ChainTableMaterialMatches parameter chain table |
        Prod.mk <$> Concrete.sampleSecret <*>
          OracleComp.presampleCacheEntriesTrace ∅
            (chainTableEdgeInputs parameter chain table)] =
        Pr[fun secret : Epoch → ChainIndex → Digest =>
            ChainTableSeedsMatch ⟨parameter, secret⟩ chain table |
          Concrete.sampleSecret] *
        Pr[fun result : List HashOutput × QueryCache HashSpec =>
            result.1.map truncateHash = chainTableEdgeTargets table |
          OracleComp.presampleCacheEntriesTrace ∅
            (chainTableEdgeInputs parameter chain table)] := by
      apply probEvent_seq_map_eq_mul
      intro secret _ result _
      rfl
    _ = ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ lifetime) *
        ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^
          (lifetime * (chainLength - 1))) := by
      rw [sampleSecret_chainTableSeedsMatch_probability,
        presampledChainTableEdges_probability]
    _ = ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^
        (lifetime * chainLength)) := by
      rw [← pow_add]
      congr 1

theorem presampledChainTableMaterial_eq_table
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest)
    (result : (Epoch → ChainIndex → Digest) ×
      (List HashOutput × QueryCache HashSpec))
    (hresult : result ∈ support
      (presampledChainTableMaterial parameter chain table))
    (hmatches : ChainTableMaterialMatches parameter chain table result) :
    keygenChainValueTable result.2.2 ⟨parameter, result.1⟩ chain = table := by
  have hedgeSupport : result.2 ∈ support
      (OracleComp.presampleCacheEntriesTrace ∅
        (chainTableEdgeInputs parameter chain table)) := by
    rw [presampledChainTableMaterial, support_seq_map_prod_mk] at hresult
    exact hresult.2
  apply keygenChainValueTable_eq_of_matches
  · exact hmatches.1
  · apply presampleCacheEntriesTrace_edgesMatch parameter chain table result.2
    · exact hedgeSupport
    · exact hmatches.2

set_option maxRecDepth 10000 in
theorem Concrete.keygenChainValueTable_edgesMatch
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (chain : ChainIndex) :
    ChainTableEdgesMatch keyResult.2 keyResult.1.2.parameter chain
      (keygenChainValueTable keyResult.2 keyResult.1.2 chain) := by
  intro edge
  let nextDigit := chainStepNextDigit edge.2
  have hpositive : 0 < nextDigit.val := by
    simp [nextDigit, chainStepNextDigit]
  obtain ⟨previous, output, hprevious, hcached, houtput⟩ :=
    Concrete.keygen_cache_has_chainValue_preimage keyResult hkeygen edge.1 chain
      nextDigit hpositive
  have hstep : previous = edge.2 := by
    apply Fin.ext
    dsimp only [nextDigit, chainStepNextDigit] at hprevious
    omega
  subst previous
  refine ⟨output, ?_, ?_⟩
  · simpa [chainTableEdgeInput, keygenChainValueTable, chainStepDigit] using hcached
  · simpa [chainTableEdgeTarget, keygenChainValueTable, nextDigit,
      Wots.signChain] using houtput

/-- All random-oracle entries that would advance a candidate fixed-chain table may be sampled before an arbitrary computation. -/
theorem evalDist_randomOracle_run'_eq_presample_chainTable
    {α : Type} (computation : OracleComp HashSpec α)
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) :
    𝒟[(simulateQ randomOracle computation).run' ∅] =
      𝒟[do
        let sampledCache ← OracleComp.presampleCacheEntries ∅
          (chainTableEdgeInputs parameter chain table)
        (simulateQ randomOracle computation).run' sampledCache] := by
  apply OracleComp.evalDist_randomOracle_run'_eq_presampleList
  · exact chainTableEdgeInputs_nodup parameter chain table
  · simp

/-- The candidate fixed-chain edge entries may also be sampled before an arbitrary computation over the full XMSS oracle. -/
theorem evalDist_xmssRom_run'_eq_presample_chainTable
    {α : Type} (computation : OracleComp OracleWorld α)
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) :
    𝒟[(simulateQ xmssRomImpl computation).run' ∅] =
      𝒟[do
        let sampledCache ← OracleComp.presampleCacheEntries ∅
          (chainTableEdgeInputs parameter chain table)
        (simulateQ xmssRomImpl computation).run' sampledCache] := by
  apply evalDist_xmssRom_run'_eq_presampleList
  · exact chainTableEdgeInputs_nodup parameter chain table
  · simp

/-- Traced form of fixed-chain presampling for the full XMSS oracle. -/
theorem evalDist_xmssRom_run'_eq_presample_chainTableTrace
    {α : Type} (computation : OracleComp OracleWorld α)
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) :
    𝒟[(simulateQ xmssRomImpl computation).run' ∅] =
      𝒟[do
        let trace ← OracleComp.presampleCacheEntriesTrace ∅
          (chainTableEdgeInputs parameter chain table)
        (simulateQ xmssRomImpl computation).run' trace.2] := by
  apply evalDist_xmssRom_run'_eq_presampleTrace
  · exact chainTableEdgeInputs_nodup parameter chain table
  · simp

/-- Candidate chain edges may be presampled conditionally after the public parameter is drawn. -/
theorem evalDist_samplePublicParameter_then_xmssRom_eq_presample_chainTableTrace
    {α : Type} (computation : PublicParameter → OracleComp OracleWorld α)
    (chain : ChainIndex) (table : ChainValueIndex → Digest) :
    𝒟[Concrete.samplePublicParameter >>= fun parameter =>
        (simulateQ xmssRomImpl (computation parameter)).run' ∅] =
      𝒟[Concrete.samplePublicParameter >>= fun parameter => do
        let trace ← OracleComp.presampleCacheEntriesTrace ∅
          (chainTableEdgeInputs parameter chain table)
        (simulateQ xmssRomImpl (computation parameter)).run' trace.2] := by
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  exact evalDist_xmssRom_run'_eq_presample_chainTableTrace
    (computation parameter) parameter chain table

noncomputable def Concrete.keygenAfterParameter
    (parameter : PublicParameter) :
    OracleComp OracleWorld (PublicKey × SecretKey) := do
  let secret ← liftM Concrete.sampleSecret
  let root ← liftM
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)
  return (⟨root, parameter⟩, ⟨parameter, secret⟩)

theorem Concrete.keygen_eq_samplePublicParameter_bind :
    Concrete.keygen =
      (liftM Concrete.samplePublicParameter >>= Concrete.keygenAfterParameter) := by
  unfold Concrete.keygen Concrete.keygenAfterParameter
  rfl

/-- After separating the public-parameter draw, every candidate fixed-chain edge can be front-loaded before the remainder of key generation. -/
theorem evalDist_keygen_eq_presample_chainTableTrace
    (chain : ChainIndex) (table : ChainValueIndex → Digest) :
    𝒟[(simulateQ xmssRomImpl Concrete.keygen).run' ∅] =
      𝒟[Concrete.samplePublicParameter >>= fun parameter => do
        let trace ← OracleComp.presampleCacheEntriesTrace ∅
          (chainTableEdgeInputs parameter chain table)
        (simulateQ xmssRomImpl (Concrete.keygenAfterParameter parameter)).run' trace.2] := by
  rw [Concrete.keygen_eq_samplePublicParameter_bind, simulateQ_bind]
  change 𝒟[(simulateQ
    (unifFwdImpl HashSpec +
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)))
    (liftM Concrete.samplePublicParameter) >>= fun parameter =>
      simulateQ xmssRomImpl (Concrete.keygenAfterParameter parameter)).run' ∅] = _
  rw [roSim.run'_liftM_bind]
  exact evalDist_samplePublicParameter_then_xmssRom_eq_presample_chainTableTrace
    Concrete.keygenAfterParameter chain table

noncomputable def Concrete.detailedGameAfterParameter
    (adversary : Adversary Concrete.scheme) (parameter : PublicParameter) :
    OracleComp OracleWorld GameOutcome := do
  let keys ← Concrete.keygenAfterParameter parameter
  detailedGameAfterKeygen Concrete.scheme adversary keys.1 keys.2

theorem Concrete.detailedGameCore_eq_samplePublicParameter_bind
    (adversary : Adversary Concrete.scheme) :
    detailedGameCore Concrete.scheme adversary =
      (liftM Concrete.samplePublicParameter >>=
        Concrete.detailedGameAfterParameter adversary) := by
  unfold detailedGameCore Concrete.detailedGameAfterParameter
  change (Concrete.keygen >>= fun keys =>
    detailedGameAfterKeygen Concrete.scheme adversary keys.1 keys.2) = _
  rw [Concrete.keygen_eq_samplePublicParameter_bind]
  simp only [bind_assoc]

/-- The full detailed game admits candidate fixed-chain presampling after the real public parameter is sampled. -/
theorem evalDist_detailedGame_eq_presample_chainTableTrace
    (adversary : Adversary Concrete.scheme)
    (chain : ChainIndex) (table : ChainValueIndex → Digest) :
    𝒟[(simulateQ xmssRomImpl
      (detailedGameCore Concrete.scheme adversary)).run' ∅] =
      𝒟[Concrete.samplePublicParameter >>= fun parameter => do
        let trace ← OracleComp.presampleCacheEntriesTrace ∅
          (chainTableEdgeInputs parameter chain table)
        (simulateQ xmssRomImpl
          (Concrete.detailedGameAfterParameter adversary parameter)).run' trace.2] := by
  rw [Concrete.detailedGameCore_eq_samplePublicParameter_bind, simulateQ_bind]
  change 𝒟[(simulateQ
    (unifFwdImpl HashSpec +
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)))
    (liftM Concrete.samplePublicParameter) >>= fun parameter =>
      simulateQ xmssRomImpl
        (Concrete.detailedGameAfterParameter adversary parameter)).run' ∅] = _
  rw [roSim.run'_liftM_bind]
  exact evalDist_samplePublicParameter_then_xmssRom_eq_presample_chainTableTrace
    (Concrete.detailedGameAfterParameter adversary) chain table

end XmssSecurity
