import XmssSecurity.ChainTableUniformity
import XmssSecurity.RandomOraclePresampling

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

end XmssSecurity
