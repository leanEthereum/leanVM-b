import XmssSecurity.Proof.ChainTableUniformity
import XmssSecurity.Proof.ChainQueryPresence
import XmssSecurity.Proof.AdaptiveFreshTarget
import XmssSecurity.Proof.MixedOraclePresampling
import XmssSecurity.Proof.SecretTableUniformity

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

theorem ChainTableEdgesMatch.mono
    {cache larger : QueryCache HashSpec} {parameter : PublicParameter}
    {chain : ChainIndex} {table : ChainValueIndex → Digest}
    (hmatch : ChainTableEdgesMatch cache parameter chain table)
    (hle : cache ≤ larger) :
    ChainTableEdgesMatch larger parameter chain table := by
  intro edge
  obtain ⟨output, hcached, htarget⟩ := hmatch edge
  exact ⟨output, hle hcached, htarget⟩

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

def secretWithFixedChainSeeds
    (other : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (seeds : Epoch → Digest) :
    Epoch → ChainIndex → Digest := fun epoch candidate =>
  if candidate = chain then seeds epoch else other epoch candidate

@[simp]
theorem secretWithFixedChainSeeds_fixedChain
    (other : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (seeds : Epoch → Digest) (epoch : Epoch) :
    secretWithFixedChainSeeds other chain seeds epoch chain = seeds epoch := by
  simp [secretWithFixedChainSeeds]

abbrev FlatSecret := Epoch × ChainIndex → Digest

noncomputable local instance presamplingSampleableFlatSecret :
    SampleableType FlatSecret :=
  SampleableType.ofFintype FlatSecret

noncomputable local instance presamplingSampleableSecret :
    SampleableType (Epoch → ChainIndex → Digest) :=
  SampleableType.ofFintype (Epoch → ChainIndex → Digest)

def unflattenSecret (table : FlatSecret) :
    Epoch → ChainIndex → Digest := fun epoch chain => table (epoch, chain)

theorem secretWithOwnFixedChainSeeds
    (table : FlatSecret) (chain : ChainIndex) :
    secretWithFixedChainSeeds (unflattenSecret table) chain
      (fun epoch => table (epoch, chain)) = unflattenSecret table := by
  funext epoch candidate
  by_cases heq : candidate = chain
  · subst candidate
    simp [secretWithFixedChainSeeds, unflattenSecret]
  · simp [secretWithFixedChainSeeds, heq, unflattenSecret]

def flatSecretEquiv :
    (Epoch → ChainIndex → Digest) ≃ FlatSecret where
  toFun secret index := secret index.1 index.2
  invFun := unflattenSecret
  left_inv secret := by
    funext epoch chain
    rfl
  right_inv table := by
    funext index
    rfl

noncomputable def extractFixedChainSeeds
    (chain : ChainIndex) : List Epoch →
      ProbComp (List Digest × FlatSecret)
  | [] => do
      let table ← $ᵗ FlatSecret
      return ([], table)
  | epoch :: epochs => do
      let value ← $ᵗ Digest
      let rest ← extractFixedChainSeeds chain epochs
      return (value :: rest.1,
        Function.update rest.2 (epoch, chain) value)

@[simp]
theorem extractFixedChainSeeds_nil (chain : ChainIndex) :
    extractFixedChainSeeds chain [] = do
      let table ← $ᵗ FlatSecret
      return ([], table) := rfl

theorem extractFixedChainSeeds_cons
    (chain : ChainIndex) (epoch : Epoch) (epochs : List Epoch) :
    extractFixedChainSeeds chain (epoch :: epochs) = do
      let value ← $ᵗ Digest
      let rest ← extractFixedChainSeeds chain epochs
      return (value :: rest.1,
        Function.update rest.2 (epoch, chain) value) := rfl

def fixedChainSeedView (chain : ChainIndex) (epochs : List Epoch)
    (table : FlatSecret) : List Digest × FlatSecret :=
  (epochs.map (fun target => table (target, chain)), table)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
/-- Exposing the selected chain's seed tape and patching it back into a uniform flat secret preserves the joint distribution of the tape read from that secret. -/
theorem evalDist_extractFixedChainSeeds_eq_uniform
    (chain : ChainIndex) :
    ∀ (epochs : List Epoch), epochs.Nodup →
      𝒟[extractFixedChainSeeds chain epochs] =
      𝒟[fixedChainSeedView chain epochs <$> ($ᵗ FlatSecret)] := by
  intro epochs
  induction epochs with
  | nil =>
      intro _hnodup
      simp only [extractFixedChainSeeds_nil, map_eq_bind_pure_comp,
        bind_pure_comp]
      congr 2
  | cons epoch epochs ih =>
      intro hnodup
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      have htailUpdate (table : FlatSecret) (value : Digest) :
          epochs.map (fun target =>
              Function.update table (epoch, chain) value (target, chain)) =
            epochs.map (fun target => table (target, chain)) := by
        apply List.map_congr_left
        intro target htarget
        rw [Function.update_of_ne]
        intro heq
        have htargetEpoch : target = epoch := congrArg Prod.fst heq
        subst target
        exact hnotMem htarget
      rw [extractFixedChainSeeds_cons]
      calc
        𝒟[$ᵗ Digest >>= fun value =>
            extractFixedChainSeeds chain epochs >>= fun rest =>
              pure (value :: rest.1,
                Function.update rest.2 (epoch, chain) value)] =
            𝒟[$ᵗ Digest >>= fun value =>
              (fixedChainSeedView chain epochs <$> ($ᵗ FlatSecret)) >>=
                  fun rest => pure (value :: rest.1,
                    Function.update rest.2 (epoch, chain) value)] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro value
          conv_lhs => rw [evalDist_bind]
          conv_rhs => rw [evalDist_bind]
          rw [ih htailNodup]
        _ = 𝒟[$ᵗ Digest >>= fun value =>
              $ᵗ FlatSecret >>= fun table =>
                pure (value :: epochs.map (fun target => table (target, chain)),
                  Function.update table (epoch, chain) value)] := by
          simp [fixedChainSeedView]
        _ = 𝒟[$ᵗ Digest >>= fun value =>
              $ᵗ FlatSecret >>= fun table =>
                pure ((fun updated : FlatSecret =>
                  ((epoch :: epochs).map
                    (fun target => updated (target, chain)), updated))
                  (Function.update table (epoch, chain) value))] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro value
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro table
          simp [htailUpdate table value]
        _ = 𝒟[fixedChainSeedView chain (epoch :: epochs) <$>
              ($ᵗ FlatSecret)] :=
          OracleComp.evalDist_uniformSample_bind_update_map
            (R := Digest) (epoch, chain)
            (fixedChainSeedView chain (epoch :: epochs))

theorem evalDist_extractFixedChainSeeds_fst_eq_drawList
    (chain : ChainIndex) (epochs : List Epoch) :
    evalDist (Prod.fst <$> extractFixedChainSeeds chain epochs) =
      evalDist (OracleComp.drawList ($ᵗ Digest) epochs.length) := by
  induction epochs with
  | nil =>
      simp only [extractFixedChainSeeds_nil, map_eq_bind_pure_comp,
        bind_assoc, pure_bind, Function.comp_apply, List.length_nil,
        OracleComp.drawList]
      exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        ($ᵗ FlatSecret) (probFailure_uniformSample FlatSecret) (pure [])
  | cons epoch epochs ih =>
      rw [extractFixedChainSeeds_cons]
      simp only [List.length_cons]
      rw [OracleComp.drawList]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro value
      calc
        evalDist (extractFixedChainSeeds chain epochs >>= fun rest =>
            pure (value :: rest.1)) =
            evalDist (List.cons value <$>
              (Prod.fst <$> extractFixedChainSeeds chain epochs)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = evalDist (List.cons value <$>
              OracleComp.drawList ($ᵗ Digest) epochs.length) := by
          rw [evalDist_map, ih, ← evalDist_map]
        _ = evalDist (OracleComp.drawList ($ᵗ Digest) epochs.length >>=
              fun rest => pure (value :: rest)) := by
          simp [map_eq_bind_pure_comp]

theorem forall₂_imp_of_forall_mem_left
    {Left Right : Type} {relation nextRelation : Left → Right → Prop} :
    ∀ {lefts : List Left} {rights : List Right},
      List.Forall₂ relation lefts rights →
      (∀ left ∈ lefts, ∀ right, relation left right →
        nextRelation left right) →
      List.Forall₂ nextRelation lefts rights := by
  intro lefts rights hpairs
  induction hpairs with
  | nil => simp
  | cons hfirst hrest ih =>
      intro himp
      apply List.Forall₂.cons
      · exact himp _ (by simp) _ hfirst
      · apply ih
        intro left hleft
        exact himp left (by simp [hleft])

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
set_option linter.constructorNameAsVariable false in
theorem extractFixedChainSeeds_support_info
    (chain : ChainIndex) :
    ∀ (epochs : List Epoch), epochs.Nodup →
      ∀ result ∈ support (extractFixedChainSeeds chain epochs),
        result.1.length = epochs.length ∧
          List.Forall₂
            (fun epoch value => result.2 (epoch, chain) = value)
            epochs result.1 := by
  intro epochs
  induction epochs with
  | nil =>
      intro _hnodup result hresult
      simp only [extractFixedChainSeeds_nil, mem_support_bind_iff] at hresult
      obtain ⟨table, _htable, hpure⟩ := hresult
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      exact ⟨rfl, List.Forall₂.nil⟩
  | cons epoch epochs ih =>
      intro hnodup result hresult
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [extractFixedChainSeeds_cons, mem_support_bind_iff] at hresult
      obtain ⟨value, _hvalue, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      obtain ⟨hlength, hpairs⟩ := ih htailNodup rest hrest
      constructor
      · simp [hlength]
      · apply List.Forall₂.cons
        · simp
        · apply forall₂_imp_of_forall_mem_left hpairs
          intro target htarget targetValue hvalue
          change Function.update rest.2 (epoch, chain) value
            (target, chain) = targetValue
          rw [Function.update_of_ne]
          · exact hvalue
          · intro heq
            have htargetEpoch := congrArg Prod.fst heq
            change target = epoch at htargetEpoch
            apply hnotMem
            rw [htargetEpoch] at htarget
            exact htarget

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

theorem allChainEdges_nodup : allChainEdges.Nodup :=
  Finset.nodup_toList _

noncomputable def chainTableEdgeInputs
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) : List HashInput :=
  allChainEdges.map (chainTableEdgeInput parameter chain table)

theorem chainTableEdgeInputs_nodup
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) :
    (chainTableEdgeInputs parameter chain table).Nodup :=
  allChainEdges_nodup.map (chainTableEdgeInput_injective parameter chain table)

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
set_option maxRecDepth 1000000 in
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

theorem drawList_support_length
    {Value : Type} (draw : ProbComp Value) :
    ∀ (count : Nat) (values : List Value),
      values ∈ support (OracleComp.drawList draw count) →
      values.length = count := by
  intro count
  induction count with
  | zero =>
      intro values hvalues
      simp only [OracleComp.drawList, support_pure,
        Set.mem_singleton_iff] at hvalues
      subst values
      rfl
  | succ count ih =>
      intro values hvalues
      rw [OracleComp.drawList, mem_support_bind_iff] at hvalues
      obtain ⟨value, _hvalue, hrest⟩ := hvalues
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst values
      simp [ih rest hrest]

theorem drawList_digest_probability (targets : List Digest) :
    Pr[= targets |
      OracleComp.drawList ($ᵗ Digest) targets.length] =
      ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ targets.length) := by
  calc
    Pr[= targets | OracleComp.drawList ($ᵗ Digest) targets.length] =
        Pr[= targets | List.map truncateHash <$>
          OracleComp.drawList ($ᵗ HashOutput) targets.length] :=
      probOutput_congr rfl
        (evalDist_map_truncate_drawList targets.length).symm
    _ = Pr[fun outputs : List HashOutput =>
          outputs.map truncateHash = targets |
        OracleComp.drawList ($ᵗ HashOutput) targets.length] := by
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      rfl
    _ = ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ targets.length) :=
      drawList_truncate_probability targets

theorem evalDist_listOfFn_uniform_eq_drawList (count : Nat) :
    𝒟[List.ofFn <$> ($ᵗ (Fin count → Digest))] =
      𝒟[OracleComp.drawList ($ᵗ Digest) count] := by
  apply SPMF.ext
  intro target
  change Pr[= target | List.ofFn <$> ($ᵗ (Fin count → Digest))] =
    Pr[= target | OracleComp.drawList ($ᵗ Digest) count]
  by_cases hlength : target.length = count
  · let targetFunction : Fin count → Digest := fun index =>
      target.get (Fin.cast hlength.symm index)
    have hofFn : List.ofFn targetFunction = target := by
      calc
        List.ofFn targetFunction = List.ofFn (List.get target) := by
          exact List.ofFn_congr hlength (List.get target) |>.symm
        _ = target := List.ofFn_get target
    calc
      Pr[= target | List.ofFn <$> ($ᵗ (Fin count → Digest))] =
          Pr[= targetFunction | $ᵗ (Fin count → Digest)] := by
        rw [← hofFn, probOutput_map_injective _ List.ofFn_injective]
      _ = ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ count) := by
        rw [probOutput_uniformSample, Fintype.card_fun, Fintype.card_fin,
          HiddenValue.card_digest, Nat.cast_pow, ENNReal.inv_pow]
      _ = Pr[= target |
          OracleComp.drawList ($ᵗ Digest) count] := by
        rw [← hlength]
        exact (drawList_digest_probability target).symm
  · have hleft : Pr[= target |
        List.ofFn <$> ($ᵗ (Fin count → Digest))] = 0 := by
      apply probOutput_eq_zero_of_not_mem_support
      intro htarget
      rw [support_map] at htarget
      obtain ⟨values, _hvalues, heq⟩ := htarget
      apply hlength
      rw [← heq]
      simp
    have hright : Pr[= target |
        OracleComp.drawList ($ᵗ Digest) count] = 0 := by
      apply probOutput_eq_zero_of_not_mem_support
      intro htarget
      exact hlength
        (drawList_support_length ($ᵗ Digest) count target htarget)
    rw [hleft, hright]

structure ProgrammedFixedChainKeygenView where
  publicKey : PublicKey
  secretKey : SecretKey
  cache : QueryCache HashSpec
  table : ChainValueIndex → Digest

noncomputable def actualFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
  return {
    publicKey := keyResult.1.1
    secretKey := keyResult.1.2
    cache := keyResult.2
    table := keygenChainValueTable keyResult.2 keyResult.1.2 chain
  }

theorem actualFixedChainKeygen_support_table
    (chain : ChainIndex) (result : ProgrammedFixedChainKeygenView)
    (hresult : result ∈ support (actualFixedChainKeygen chain)) :
    keygenChainValueTable result.cache result.secretKey chain = result.table := by
  unfold actualFixedChainKeygen at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, _hkeyResult, hpure⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  rfl

noncomputable def explicitFixedChainKeygenFromSecret
    (parameter : PublicParameter) (chain : ChainIndex)
    (secret : Epoch → ChainIndex → Digest) :
    ProbComp ProgrammedFixedChainKeygenView := do
  let rootResult ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)).run ∅
  return {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey := (SecretKey.withoutPrecomputation parameter secret)
    cache := rootResult.2
    table := keygenChainValueTable rootResult.2 (SecretKey.withoutPrecomputation parameter secret) chain
  }

noncomputable def explicitFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let secret ← Concrete.sampleSecret
  explicitFixedChainKeygenFromSecret parameter chain secret

theorem evalDist_actualFixedChainKeygen_eq_explicit
    (chain : ChainIndex) :
    evalDist (actualFixedChainKeygen chain) =
      evalDist (explicitFixedChainKeygen chain) := by
  unfold actualFixedChainKeygen explicitFixedChainKeygen
    explicitFixedChainKeygenFromSecret Concrete.keygen
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

set_option maxRecDepth 100000 in
theorem evalDist_unflatten_uniformFlatSecret_eq_sampleSecret :
    evalDist (unflattenSecret <$> ($ᵗ FlatSecret)) =
      evalDist Concrete.sampleSecret := by
  unfold Concrete.sampleSecret
  exact evalDist_map_bijective_uniform_cross
    (α := FlatSecret) (β := Epoch → ChainIndex → Digest)
    (fun table : FlatSecret => unflattenSecret table)
    flatSecretEquiv.symm.bijective

noncomputable def flatExplicitFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let flatSecret ← $ᵗ FlatSecret
  explicitFixedChainKeygenFromSecret parameter chain
    (unflattenSecret flatSecret)

theorem evalDist_explicitFixedChainKeygen_eq_flat
    (chain : ChainIndex) :
    evalDist (explicitFixedChainKeygen chain) =
      evalDist (flatExplicitFixedChainKeygen chain) := by
  unfold explicitFixedChainKeygen flatExplicitFixedChainKeygen
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  calc
    evalDist (Concrete.sampleSecret >>= fun secret =>
        explicitFixedChainKeygenFromSecret parameter chain secret) =
        evalDist ((unflattenSecret <$> ($ᵗ FlatSecret)) >>= fun secret =>
          explicitFixedChainKeygenFromSecret parameter chain secret) := by
      conv_lhs => rw [evalDist_bind]
      conv_rhs => rw [evalDist_bind]
      rw [evalDist_unflatten_uniformFlatSecret_eq_sampleSecret]
    _ = evalDist (($ᵗ FlatSecret) >>= fun flatSecret =>
          explicitFixedChainKeygenFromSecret parameter chain
            (unflattenSecret flatSecret)) := by
      simp [map_eq_bind_pure_comp, bind_assoc]

noncomputable def extractedExplicitFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let secretView ← extractFixedChainSeeds chain allEpochs
  explicitFixedChainKeygenFromSecret parameter chain
    (unflattenSecret secretView.2)

theorem evalDist_flatExplicitFixedChainKeygen_eq_extracted
    (chain : ChainIndex) :
    evalDist (flatExplicitFixedChainKeygen chain) =
      evalDist (extractedExplicitFixedChainKeygen chain) := by
  unfold flatExplicitFixedChainKeygen extractedExplicitFixedChainKeygen
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  symm
  calc
    evalDist (extractFixedChainSeeds chain allEpochs >>= fun secretView =>
        explicitFixedChainKeygenFromSecret parameter chain
          (unflattenSecret secretView.2)) =
        evalDist ((fixedChainSeedView chain allEpochs <$>
          ($ᵗ FlatSecret)) >>= fun secretView =>
            explicitFixedChainKeygenFromSecret parameter chain
              (unflattenSecret secretView.2)) := by
      conv_lhs => rw [evalDist_bind]
      conv_rhs => rw [evalDist_bind]
      rw [evalDist_extractFixedChainSeeds_eq_uniform chain allEpochs allEpochs_nodup]
    _ = evalDist (($ᵗ FlatSecret) >>= fun flatSecret =>
          explicitFixedChainKeygenFromSecret parameter chain
            (unflattenSecret flatSecret)) := by
      simp [map_eq_bind_pure_comp, bind_assoc, fixedChainSeedView]

theorem evalDist_actualFixedChainKeygen_eq_extracted
    (chain : ChainIndex) :
    evalDist (actualFixedChainKeygen chain) =
      evalDist (extractedExplicitFixedChainKeygen chain) :=
  (evalDist_actualFixedChainKeygen_eq_explicit chain).trans
    ((evalDist_explicitFixedChainKeygen_eq_flat chain).trans
      (evalDist_flatExplicitFixedChainKeygen_eq_extracted chain))

theorem keygenChainValueTable_seedsMatch
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (chain : ChainIndex) :
    ChainTableSeedsMatch secretKey chain
      (keygenChainValueTable cache secretKey chain) := by
  intro epoch
  simp [keygenChainValueTable]

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

theorem Concrete.CacheReplay.rootTree_chain_query_cached_from_cache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep)
    (initialCache : QueryCache HashSpec)
    (result : Digest × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run initialCache)) :
    ∃ output, result.2
      (Concrete.CacheView.chainInput parameter epoch chain step
        (Wots.walk
          (Concrete.CacheView.chainStep result.2 parameter epoch chain)
          0 step.val (secret epoch chain))) = some output := by
  apply Concrete.CacheReplay.treeNode_chain_query_cached_in_largerCache
    parameter secret epoch chain step treeHeight Concrete.rootNode le_rfl
  · unfold TreeSubtreeValid Concrete.rootNode lifetime
    norm_num
  · unfold TreeCovers Concrete.rootNode
    constructor
    · simp
    · simp [lifetime]
  · exact hresult
  · exact le_rfl

theorem evalDist_rootTree_run_eq_chainHash_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (steps : Nat)
    (previous : Digest)
    (initialCache prefixCache : QueryCache HashSpec)
    (hvalid : steps < chainLength - 1)
    (hprefix : (previous, prefixCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch chain 0 steps
          (secret epoch chain) :
          OracleComp HashSpec Digest)).run initialCache)) :
    evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run prefixCache) =
      evalDist ((simulateQ randomOracle
        (Concrete.chainHash parameter epoch chain
          ⟨steps, hvalid⟩ previous : OracleComp HashSpec Digest)).run
            prefixCache >>= fun hashResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run hashResult.2) := by
  let target := Concrete.CacheView.chainInput parameter epoch chain
    ⟨steps, hvalid⟩ previous
  have hcached : ∀ result ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run prefixCache),
      ∃ output, result.2 target = some output := by
    intro result hresult
    have hprefixLe := Concrete.CacheReplay.randomOracle_cache_le
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest) prefixCache result hresult
    have hreplay := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
      (Concrete.chainWalk parameter epoch chain 0 steps
        (secret epoch chain) :
        OracleComp HashSpec Digest)
      initialCache prefixCache result.2 previous hprefix hprefixLe
    rw [Concrete.CacheReplay.eval_chainWalk] at hreplay
    obtain ⟨output, houtput⟩ :=
      Concrete.CacheReplay.rootTree_chain_query_cached_from_cache
        parameter secret epoch chain ⟨steps, hvalid⟩
        prefixCache result hresult
    refine ⟨output, ?_⟩
    change result.2
      (Concrete.CacheView.chainInput parameter epoch chain
        ⟨steps, hvalid⟩ previous) = some output
    rw [← hreplay]
    exact houtput
  calc
    evalDist ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run prefixCache) =
        evalDist ((randomOracle (spec := HashSpec) target).run prefixCache >>=
          fun queryResult =>
            (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run queryResult.2) :=
      OracleComp.evalDist_randomOracle_run_eq_query_then_of_cached
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest) prefixCache target hcached
    _ = evalDist ((simulateQ randomOracle
          (Concrete.chainHash parameter epoch chain
            ⟨steps, hvalid⟩ previous :
              OracleComp HashSpec Digest)).run prefixCache >>= fun hashResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run hashResult.2) := by
      simp [Concrete.chainHash, Concrete.tweakableHash, Concrete.oracleHash,
        target, Concrete.CacheView.chainInput]

theorem evalDist_rootTree_run_eq_chainWalk_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1)
    (initialCache : QueryCache HashSpec) :
    evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache) =
      evalDist ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch chain 0 steps
          (secret epoch chain) : OracleComp HashSpec Digest)).run initialCache >>=
            fun chainResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run chainResult.2) := by
  induction steps generalizing initialCache with
  | zero =>
      simp [Concrete.chainWalk]
  | succ steps ih =>
      have hvalid : steps < chainLength - 1 := by omega
      calc
        evalDist ((simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run initialCache) =
            evalDist ((simulateQ randomOracle
              (Concrete.chainWalk parameter epoch chain 0 steps
                (secret epoch chain) : OracleComp HashSpec Digest)).run
                  initialCache >>= fun prefixResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run prefixResult.2) :=
          ih (by omega) initialCache
        _ = evalDist ((simulateQ randomOracle
              (Concrete.chainWalk parameter epoch chain 0 steps
                (secret epoch chain) : OracleComp HashSpec Digest)).run
                  initialCache >>= fun prefixResult =>
              (simulateQ randomOracle
                (Concrete.chainHash parameter epoch chain ⟨steps, hvalid⟩
                  prefixResult.1 : OracleComp HashSpec Digest)).run
                    prefixResult.2 >>= fun hashResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run hashResult.2) := by
          apply evalDist_bind_congr
          intro prefixResult hprefix
          exact evalDist_rootTree_run_eq_chainHash_then_rootTree
            parameter secret epoch chain steps prefixResult.1 initialCache
            prefixResult.2 hvalid hprefix
        _ = evalDist ((simulateQ randomOracle
              (Concrete.chainWalk parameter epoch chain 0 (steps + 1)
                (secret epoch chain) : OracleComp HashSpec Digest)).run
                  initialCache >>= fun chainResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run chainResult.2) := by
          rw [Concrete.chainWalk, simulateQ_bind, StateT.run_bind]
          simp only [zero_add]
          simp only [hvalid, ↓reduceDIte, bind_assoc]

theorem Concrete.chainTrajectory_back_map_eq_chainWalk
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    Vector.back <$> Concrete.chainTrajectory parameter epoch chain position steps value =
      (Concrete.chainWalk parameter epoch chain position steps value :
        OracleComp HashSpec Digest) := by
  induction steps with
  | zero =>
      rw [Concrete.chainTrajectory_zero]
      simp only [map_pure, Concrete.chainWalk]
      simp [Vector.back_ofFn]
  | succ steps ih =>
      calc
        Vector.back <$>
            Concrete.chainTrajectory parameter epoch chain position
              (steps + 1) value =
            (Vector.back <$> Concrete.chainTrajectory parameter epoch chain
              position steps value) >>= fun previous =>
              if hvalid : position + steps < chainLength - 1 then
                Concrete.chainHash parameter epoch chain
                  ⟨position + steps, hvalid⟩ previous
              else pure 0 := by
          rw [Concrete.chainTrajectory_succ]
          by_cases hvalid : position + steps < chainLength - 1
          · simp [hvalid, map_eq_bind_pure_comp, bind_assoc]
          · simp [hvalid, map_eq_bind_pure_comp, bind_assoc]
        _ = Concrete.chainWalk parameter epoch chain position
            (steps + 1) value := by
          rw [ih]
          rfl

theorem evalDist_chainTrajectory_run_cache_eq_chainWalk_run_cache
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (value : Digest)
    (initialCache : QueryCache HashSpec) :
    evalDist ((fun result : Vector Digest (steps + 1) × QueryCache HashSpec =>
      (result.1.back, result.2)) <$>
        (simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain position steps value)).run
            initialCache) =
      evalDist ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch chain position steps value :
          OracleComp HashSpec Digest)).run initialCache) := by
  rw [← StateT.run_map]
  rw [← simulateQ_map]
  rw [Concrete.chainTrajectory_back_map_eq_chainWalk]

theorem evalDist_rootTree_run_eq_chainTrajectory_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1)
    (initialCache : QueryCache HashSpec) :
    evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache) =
      evalDist ((simulateQ randomOracle
        (Concrete.chainTrajectory parameter epoch chain 0 steps
          (secret epoch chain))).run initialCache >>= fun trajectoryResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run trajectoryResult.2) := by
  calc
    evalDist ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run initialCache) =
        evalDist ((simulateQ randomOracle
          (Concrete.chainWalk parameter epoch chain 0 steps
            (secret epoch chain) : OracleComp HashSpec Digest)).run initialCache >>=
              fun chainResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run chainResult.2) :=
      evalDist_rootTree_run_eq_chainWalk_then_rootTree parameter secret epoch
        chain steps hsteps initialCache
    _ = evalDist (((fun result : Vector Digest (steps + 1) × QueryCache HashSpec =>
          (result.1.back, result.2)) <$>
            (simulateQ randomOracle
              (Concrete.chainTrajectory parameter epoch chain 0 steps
                (secret epoch chain))).run initialCache) >>= fun chainResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run chainResult.2) := by
      conv_lhs => rw [evalDist_bind]
      conv_rhs => rw [evalDist_bind]
      rw [evalDist_chainTrajectory_run_cache_eq_chainWalk_run_cache]
    _ = evalDist ((simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain 0 steps
            (secret epoch chain))).run initialCache >>= fun trajectoryResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run trajectoryResult.2) := by
      simp [map_eq_bind_pure_comp, bind_assoc]

noncomputable def Concrete.fixedSeedChainTrajectoriesFromCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    QueryCache HashSpec → List Epoch →
      ProbComp (List (Vector Digest (steps + 1)) × QueryCache HashSpec)
  | cache, [] => pure ([], cache)
  | cache, epoch :: epochs => do
      let first ← (simulateQ randomOracle
        (Concrete.chainTrajectory parameter epoch chain 0 steps
          (secret epoch chain))).run cache
      let rest ← Concrete.fixedSeedChainTrajectoriesFromCache
        parameter secret chain steps first.2 epochs
      return (first.1 :: rest.1, rest.2)

@[simp]
theorem Concrete.fixedSeedChainTrajectoriesFromCache_nil
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (cache : QueryCache HashSpec) :
    Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain steps
      cache [] = pure ([], cache) := rfl

theorem Concrete.fixedSeedChainTrajectoriesFromCache_cons
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (cache : QueryCache HashSpec)
    (epoch : Epoch) (epochs : List Epoch) :
    Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain steps
      cache (epoch :: epochs) = (do
        let first ← (simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain 0 steps
            (secret epoch chain))).run cache
        let rest ← Concrete.fixedSeedChainTrajectoriesFromCache
          parameter secret chain steps first.2 epochs
        return (first.1 :: rest.1, rest.2)) := rfl

noncomputable def Concrete.fixedChainTrajectoriesFromTape
    (parameter : PublicParameter) (chain : ChainIndex) (steps : Nat) :
    QueryCache HashSpec → List Epoch → List Digest →
      ProbComp (List (Vector Digest (steps + 1)) × QueryCache HashSpec)
  | cache, [], _ => pure ([], cache)
  | cache, _ :: _, [] => pure ([], cache)
  | cache, epoch :: epochs, seed :: seeds => do
      let first ← (simulateQ randomOracle
        (Concrete.chainTrajectory parameter epoch chain 0 steps seed)).run cache
      let rest ← Concrete.fixedChainTrajectoriesFromTape
        parameter chain steps first.2 epochs seeds
      return (first.1 :: rest.1, rest.2)

@[simp]
theorem Concrete.fixedChainTrajectoriesFromTape_nil_epochs
    (parameter : PublicParameter) (chain : ChainIndex) (steps : Nat)
    (cache : QueryCache HashSpec) (seeds : List Digest) :
    Concrete.fixedChainTrajectoriesFromTape parameter chain steps cache [] seeds =
      pure ([], cache) := rfl

@[simp]
theorem Concrete.fixedChainTrajectoriesFromTape_nil_seeds
    (parameter : PublicParameter) (chain : ChainIndex) (steps : Nat)
    (cache : QueryCache HashSpec) (epoch : Epoch) (epochs : List Epoch) :
    Concrete.fixedChainTrajectoriesFromTape parameter chain steps cache
      (epoch :: epochs) [] = pure ([], cache) := rfl

theorem Concrete.fixedChainTrajectoriesFromTape_cons
    (parameter : PublicParameter) (chain : ChainIndex) (steps : Nat)
    (cache : QueryCache HashSpec) (epoch : Epoch) (epochs : List Epoch)
    (seed : Digest) (seeds : List Digest) :
    Concrete.fixedChainTrajectoriesFromTape parameter chain steps cache
      (epoch :: epochs) (seed :: seeds) = (do
        let first ← (simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain 0 steps seed)).run cache
        let rest ← Concrete.fixedChainTrajectoriesFromTape
          parameter chain steps first.2 epochs seeds
        return (first.1 :: rest.1, rest.2)) := rfl

theorem Concrete.fixedSeedChainTrajectories_eq_fromTape_of_forall₂
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat)
    {epochs : List Epoch} {seeds : List Digest}
    (hpairs : List.Forall₂ (fun epoch seed => secret epoch chain = seed)
      epochs seeds) (cache : QueryCache HashSpec) :
    Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain steps
      cache epochs =
      Concrete.fixedChainTrajectoriesFromTape parameter chain steps
        cache epochs seeds := by
  induction hpairs generalizing cache with
  | nil => simp
  | cons heq _hpairs ih =>
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        Concrete.fixedChainTrajectoriesFromTape_cons, heq]
      apply bind_congr
      intro first
      rw [ih]

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.fixedSeedChainTrajectoriesFromCache_support_info
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec)
      (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec),
      result ∈ support
        (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
          steps cache epochs) →
      cache ≤ result.2 ∧ result.1.length = epochs.length ∧
        List.Forall₂
          (fun epoch trajectory =>
            evalWithAnswerFn (Concrete.CacheReplay.answerFn result.2)
              (Concrete.chainTrajectory parameter epoch chain 0 steps
                (secret epoch chain)) = trajectory)
          epochs result.1 := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache result hresult
      simp only [Concrete.fixedSeedChainTrajectoriesFromCache_nil,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨le_rfl, rfl, List.Forall₂.nil⟩
  | cons epoch epochs ih =>
      intro cache result hresult
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      obtain ⟨hfirstCacheLe, hlength, hpairs⟩ :=
        ih first.2 rest hrest
      constructor
      · exact (Concrete.CacheReplay.randomOracle_cache_le
          (Concrete.chainTrajectory parameter epoch chain 0 steps
            (secret epoch chain)) cache first hfirst).trans hfirstCacheLe
      · constructor
        · simp [hlength]
        · apply List.Forall₂.cons
          · exact Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
              (Concrete.chainTrajectory parameter epoch chain 0 steps
                (secret epoch chain)) cache first.2 rest.2 first.1 hfirst
                hfirstCacheLe
          · exact hpairs

theorem Concrete.fixedSeedChainTrajectoriesFromCache_table_eq
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (result : List FullChainTrajectory × QueryCache HashSpec)
    (hresult : result ∈ support
      (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs)) :
    chainValueTableOfList result.1 =
      keygenChainValueTable result.2 (SecretKey.withoutPrecomputation parameter secret) chain := by
  obtain ⟨_hcache, hlength, hpairs⟩ :=
    Concrete.fixedSeedChainTrajectoriesFromCache_support_info parameter secret
      chain (chainLength - 1) allEpochs ∅ result hresult
  funext index
  unfold chainValueTableOfList
  split
  · rename_i htableLength
    let position := epochPosition index.1
    have hresultPosition : position.val < result.1.length := by
      rw [← htableLength]
      exact position.isLt
    have hpair := hpairs.get position.isLt hresultPosition
    have hepoch : allEpochs.get position = index.1 := by
      exact allEpochs_get_epochPosition index.1
    rw [hepoch] at hpair
    have hvalue := congrArg
      (fun trajectory : FullChainTrajectory =>
        trajectory[index.2.val]'(by
          have hdigit := index.2.isLt
          omega)) hpair
    rw [Concrete.chainTrajectory_getElem] at hvalue
    exact hvalue.symm
  · rename_i htableLength
    exact (htableLength hlength.symm).elim

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.fixedSeedChainTrajectoriesFromCache_replay_in_largerCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec)
      (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec)
      (largerCache : QueryCache HashSpec),
      result ∈ support
        (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
          steps cache epochs) →
      result.2 ≤ largerCache →
      List.Forall₂
        (fun epoch trajectory =>
          evalWithAnswerFn (Concrete.CacheReplay.answerFn largerCache)
            (Concrete.chainTrajectory parameter epoch chain 0 steps
              (secret epoch chain)) = trajectory)
        epochs result.1 := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache result largerCache hresult _hle
      simp only [Concrete.fixedSeedChainTrajectoriesFromCache_nil,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact List.Forall₂.nil
  | cons epoch epochs ih =>
      intro cache result largerCache hresult hlarger
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      have hrestInfo :=
        Concrete.fixedSeedChainTrajectoriesFromCache_support_info parameter
          secret chain steps epochs first.2 rest hrest
      apply List.Forall₂.cons
      · exact Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
          (Concrete.chainTrajectory parameter epoch chain 0 steps
            (secret epoch chain)) cache first.2 largerCache first.1 hfirst
            (hrestInfo.1.trans hlarger)
      · exact ih first.2 rest largerCache hrest hlarger

theorem Concrete.fixedSeedChainTrajectoriesFromCache_table_eq_in_largerCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (result : List FullChainTrajectory × QueryCache HashSpec)
    (largerCache : QueryCache HashSpec)
    (hresult : result ∈ support
      (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (hle : result.2 ≤ largerCache) :
    chainValueTableOfList result.1 =
      keygenChainValueTable largerCache (SecretKey.withoutPrecomputation parameter secret) chain := by
  have hinfo := Concrete.fixedSeedChainTrajectoriesFromCache_support_info
    parameter secret chain (chainLength - 1) allEpochs ∅ result hresult
  have hpairs :=
    Concrete.fixedSeedChainTrajectoriesFromCache_replay_in_largerCache
      parameter secret chain (chainLength - 1) allEpochs ∅ result largerCache
      hresult hle
  funext index
  unfold chainValueTableOfList
  split
  · rename_i htableLength
    let position := epochPosition index.1
    have hresultPosition : position.val < result.1.length := by
      rw [← htableLength]
      exact position.isLt
    have hpair := hpairs.get position.isLt hresultPosition
    have hepoch : allEpochs.get position = index.1 := by
      exact allEpochs_get_epochPosition index.1
    rw [hepoch] at hpair
    have hvalue := congrArg
      (fun trajectory : FullChainTrajectory =>
        trajectory[index.2.val]'(by
          have hdigit := index.2.isLt
          omega)) hpair
    rw [Concrete.chainTrajectory_getElem] at hvalue
    exact hvalue.symm
  · rename_i htableLength
    exact (htableLength hinfo.2.1.symm).elim

noncomputable def Concrete.extractedFixedChainTrajectoriesFromCache
    (parameter : PublicParameter) (chain : ChainIndex) (steps : Nat)
    (cache : QueryCache HashSpec) (epochs : List Epoch) :
    ProbComp (List (Vector Digest (steps + 1)) × QueryCache HashSpec) := do
  let secretView ← extractFixedChainSeeds chain epochs
  Concrete.fixedSeedChainTrajectoriesFromCache parameter
    (unflattenSecret secretView.2) chain steps cache epochs

noncomputable def Concrete.tapedFixedChainTrajectoriesFromCache
    (parameter : PublicParameter) (chain : ChainIndex) (steps : Nat)
    (cache : QueryCache HashSpec) (epochs : List Epoch) :
    ProbComp (List (Vector Digest (steps + 1)) × QueryCache HashSpec) := do
  let seeds ← OracleComp.drawList ($ᵗ Digest) epochs.length
  Concrete.fixedChainTrajectoriesFromTape parameter chain steps cache
    epochs seeds

theorem Concrete.evalDist_extractedFixedChainTrajectories_eq_taped
    (parameter : PublicParameter) (chain : ChainIndex) (steps : Nat)
    (cache : QueryCache HashSpec) (epochs : List Epoch)
    (hnodup : epochs.Nodup) :
    evalDist (Concrete.extractedFixedChainTrajectoriesFromCache parameter
      chain steps cache epochs) =
      evalDist (Concrete.tapedFixedChainTrajectoriesFromCache parameter
        chain steps cache epochs) := by
  unfold Concrete.extractedFixedChainTrajectoriesFromCache
    Concrete.tapedFixedChainTrajectoriesFromCache
  calc
    evalDist (extractFixedChainSeeds chain epochs >>= fun secretView =>
        Concrete.fixedSeedChainTrajectoriesFromCache parameter
          (unflattenSecret secretView.2) chain steps cache epochs) =
        evalDist (extractFixedChainSeeds chain epochs >>= fun secretView =>
          Concrete.fixedChainTrajectoriesFromTape parameter chain steps cache
            epochs secretView.1) := by
      apply evalDist_bind_congr
      intro secretView hsecretView
      rw [Concrete.fixedSeedChainTrajectories_eq_fromTape_of_forall₂]
      exact (extractFixedChainSeeds_support_info chain epochs hnodup
        secretView hsecretView).2
    _ = evalDist ((Prod.fst <$> extractFixedChainSeeds chain epochs) >>=
          fun seeds => Concrete.fixedChainTrajectoriesFromTape parameter chain
            steps cache epochs seeds) := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (OracleComp.drawList ($ᵗ Digest) epochs.length >>= fun seeds =>
          Concrete.fixedChainTrajectoriesFromTape parameter chain steps cache
            epochs seeds) := by
      conv_lhs => rw [evalDist_bind]
      conv_rhs => rw [evalDist_bind]
      rw [evalDist_extractFixedChainSeeds_fst_eq_drawList]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem Concrete.evalDist_tapedFixedChainTrajectories_cons
    (parameter : PublicParameter) (chain : ChainIndex) (steps : Nat)
    (cache : QueryCache HashSpec) (epoch : Epoch) (epochs : List Epoch) :
    evalDist (Concrete.tapedFixedChainTrajectoriesFromCache parameter
      chain steps cache (epoch :: epochs)) =
      evalDist (($ᵗ Digest) >>= fun seed =>
        (simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain 0 steps seed)).run
            cache >>= fun first =>
        Concrete.tapedFixedChainTrajectoriesFromCache parameter chain steps
          first.2 epochs >>= fun rest =>
        pure (first.1 :: rest.1, rest.2)) := by
  unfold Concrete.tapedFixedChainTrajectoriesFromCache
  rw [List.length_cons, OracleComp.drawList]
  simp only [bind_assoc, pure_bind,
    Concrete.fixedChainTrajectoriesFromTape_cons]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro seed
  exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _

theorem evalDist_rootTree_run_eq_fixedSeedTrajectories_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1)
    (epochs : List Epoch) (initialCache : QueryCache HashSpec) :
    evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache) =
      evalDist (Concrete.fixedSeedChainTrajectoriesFromCache
        parameter secret chain steps initialCache epochs >>= fun trajectoryResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run trajectoryResult.2) := by
  induction epochs generalizing initialCache with
  | nil =>
      simp
  | cons epoch epochs ih =>
      calc
        evalDist ((simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run initialCache) =
            evalDist ((simulateQ randomOracle
              (Concrete.chainTrajectory parameter epoch chain 0 steps
                (secret epoch chain))).run initialCache >>= fun first =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run first.2) :=
          evalDist_rootTree_run_eq_chainTrajectory_then_rootTree
            parameter secret epoch chain steps hsteps initialCache
        _ = evalDist ((simulateQ randomOracle
              (Concrete.chainTrajectory parameter epoch chain 0 steps
                (secret epoch chain))).run initialCache >>= fun first =>
              Concrete.fixedSeedChainTrajectoriesFromCache
                parameter secret chain steps first.2 epochs >>= fun rest =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run rest.2) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          exact ih first.2
        _ = evalDist (Concrete.fixedSeedChainTrajectoriesFromCache parameter
              secret chain steps initialCache (epoch :: epochs) >>=
                fun trajectoryResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run trajectoryResult.2) := by
          rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons]
          simp only [bind_assoc, pure_bind]

noncomputable def chronologicallyWarmedExtractedFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let secretView ← extractFixedChainSeeds chain allEpochs
  let secret := unflattenSecret secretView.2
  let rootResult ← (do
    let trajectoryResult ← Concrete.fixedSeedChainTrajectoriesFromCache
      parameter secret chain (chainLength - 1) ∅ allEpochs
    (simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run trajectoryResult.2)
  return {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey := (SecretKey.withoutPrecomputation parameter secret)
    cache := rootResult.2
    table := keygenChainValueTable rootResult.2 (SecretKey.withoutPrecomputation parameter secret) chain
  }

theorem evalDist_extractedFixedChainKeygen_eq_chronologicallyWarmed
    (chain : ChainIndex) :
    evalDist (extractedExplicitFixedChainKeygen chain) =
      evalDist (chronologicallyWarmedExtractedFixedChainKeygen chain) := by
  unfold extractedExplicitFixedChainKeygen
    chronologicallyWarmedExtractedFixedChainKeygen
    explicitFixedChainKeygenFromSecret
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secretView
  let secret := unflattenSecret secretView.2
  let makeView : Digest × QueryCache HashSpec →
      ProbComp ProgrammedFixedChainKeygenView := fun rootResult =>
    pure ({
      publicKey := ⟨rootResult.1, parameter⟩
      secretKey := (SecretKey.withoutPrecomputation parameter secret)
      cache := rootResult.2
      table := keygenChainValueTable rootResult.2 (SecretKey.withoutPrecomputation parameter secret) chain
    } : ProgrammedFixedChainKeygenView)
  change evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run ∅ >>= makeView) =
    evalDist ((Concrete.fixedSeedChainTrajectoriesFromCache parameter secret
      chain (chainLength - 1) ∅ allEpochs >>= fun trajectoryResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run trajectoryResult.2) >>= makeView)
  conv_lhs => rw [evalDist_bind]
  conv_rhs => rw [evalDist_bind]
  rw [evalDist_rootTree_run_eq_fixedSeedTrajectories_then_rootTree
    parameter secret chain (chainLength - 1) le_rfl allEpochs ∅]

theorem evalDist_actualFixedChainKeygen_eq_chronologicallyWarmed
    (chain : ChainIndex) :
    evalDist (actualFixedChainKeygen chain) =
      evalDist (chronologicallyWarmedExtractedFixedChainKeygen chain) :=
  (evalDist_actualFixedChainKeygen_eq_extracted chain).trans
    (evalDist_extractedFixedChainKeygen_eq_chronologicallyWarmed chain)

theorem chronologicallyWarmedExtractedFixedChainKeygen_support_table
    (chain : ChainIndex) (result : ProgrammedFixedChainKeygenView)
    (hresult : result ∈ support
      (chronologicallyWarmedExtractedFixedChainKeygen chain)) :
    ∃ trajectories : List FullChainTrajectory,
      result.table = chainValueTableOfList trajectories ∧
        trajectories.length = lifetime := by
  unfold chronologicallyWarmedExtractedFixedChainKeygen at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨parameter, _hparameter, hsecretView⟩ := hresult
  rw [mem_support_bind_iff] at hsecretView
  obtain ⟨secretView, _hsecretView, htrajectory⟩ := hsecretView
  rw [mem_support_bind_iff] at htrajectory
  obtain ⟨rootResult, hrootComputation, hpure⟩ := htrajectory
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  rw [mem_support_bind_iff] at hrootComputation
  obtain ⟨trajectoryResult, htrajectoryResult, hrootResult⟩ := hrootComputation
  refine ⟨trajectoryResult.1, ?_, ?_⟩
  · symm
    apply Concrete.fixedSeedChainTrajectoriesFromCache_table_eq_in_largerCache
      parameter (unflattenSecret secretView.2) chain trajectoryResult
        rootResult.2 htrajectoryResult
    exact Concrete.CacheReplay.randomOracle_cache_le
      (Concrete.treeNode parameter (unflattenSecret secretView.2) treeHeight
        Concrete.rootNode : OracleComp HashSpec Digest)
      trajectoryResult.2 rootResult hrootResult
  · have hinfo := Concrete.fixedSeedChainTrajectoriesFromCache_support_info
      parameter (unflattenSecret secretView.2) chain (chainLength - 1)
        allEpochs ∅ trajectoryResult htrajectoryResult
    simpa [allEpochs_length] using hinfo.2.1

def Concrete.warmFixedChainEpochs
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) : List Epoch → OracleComp HashSpec Unit
  | [] => pure ()
  | epoch :: epochs => do
      let _endpoint ← Concrete.chainWalk parameter epoch chain 0
        (chainLength - 1) (secret epoch chain)
      Concrete.warmFixedChainEpochs parameter secret chain epochs

@[simp]
theorem Concrete.warmFixedChainEpochs_nil
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) :
    Concrete.warmFixedChainEpochs parameter secret chain [] = pure () := rfl

theorem Concrete.warmFixedChainEpochs_cons
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (epoch : Epoch) (epochs : List Epoch) :
    Concrete.warmFixedChainEpochs parameter secret chain (epoch :: epochs) = (do
      let _endpoint ← Concrete.chainWalk parameter epoch chain 0
        (chainLength - 1) (secret epoch chain)
      Concrete.warmFixedChainEpochs parameter secret chain epochs) := rfl

theorem evalDist_rootTree_run_eq_warmFixedChainEpochs_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (epochs : List Epoch)
    (initialCache : QueryCache HashSpec) :
    evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache) =
      evalDist ((simulateQ randomOracle
        (Concrete.warmFixedChainEpochs parameter secret chain epochs)).run
          initialCache >>= fun warmResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run warmResult.2) := by
  induction epochs generalizing initialCache with
  | nil =>
      simp
  | cons epoch epochs ih =>
      calc
        evalDist ((simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run initialCache) =
            evalDist ((simulateQ randomOracle
              (Concrete.chainWalk parameter epoch chain 0 (chainLength - 1)
                (secret epoch chain) : OracleComp HashSpec Digest)).run
                  initialCache >>= fun chainResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run chainResult.2) :=
          evalDist_rootTree_run_eq_chainWalk_then_rootTree parameter secret
            epoch chain (chainLength - 1) le_rfl initialCache
        _ = evalDist ((simulateQ randomOracle
              (Concrete.chainWalk parameter epoch chain 0 (chainLength - 1)
                (secret epoch chain) : OracleComp HashSpec Digest)).run
                  initialCache >>= fun chainResult =>
              (simulateQ randomOracle
                (Concrete.warmFixedChainEpochs parameter secret chain epochs)).run
                  chainResult.2 >>= fun warmResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run warmResult.2) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro chainResult
          exact ih chainResult.2
        _ = evalDist ((simulateQ randomOracle
              (Concrete.warmFixedChainEpochs parameter secret chain
                (epoch :: epochs))).run initialCache >>= fun warmResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run warmResult.2) := by
          rw [Concrete.warmFixedChainEpochs_cons, simulateQ_bind,
            StateT.run_bind]
          simp only [bind_assoc]

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
  return (⟨root, parameter⟩, (SecretKey.withoutPrecomputation parameter secret))

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

end XmssSecurity
