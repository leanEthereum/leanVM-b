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

/-- The complete edge enumeration identifies an edge table with its ordered tape. -/
noncomputable def chainEdgeTableTapeEquiv :
    (ChainEdgeIndex → Digest) ≃
      (Fin allChainEdges.length → Digest) :=
  (Equiv.piCongrLeft (fun _ : ChainEdgeIndex => Digest)
    (allChainEdges_nodup.getEquivOfForallMemList allChainEdges
      mem_allChainEdges)).symm

theorem listOfFn_chainEdgeTableTapeEquiv
    (table : ChainEdgeIndex → Digest) :
    List.ofFn (chainEdgeTableTapeEquiv table) =
      allChainEdges.map table := by
  rw [← List.ofFn_get (allChainEdges.map table)]
  apply List.ext_get
  · simp
  · intro index hleft hright
    simp [chainEdgeTableTapeEquiv]

noncomputable def chainEdgeTableOfTape
    (targets : List Digest) : ChainEdgeIndex → Digest :=
  if hlength : targets.length = allChainEdges.length then
    chainEdgeTableTapeEquiv.symm fun index =>
      targets.get (Fin.cast hlength.symm index)
  else
    fun _ => 0

@[simp]
theorem chainEdgeTableOfTape_map
    (table : ChainEdgeIndex → Digest) :
    chainEdgeTableOfTape (allChainEdges.map table) = table := by
  unfold chainEdgeTableOfTape
  split
  · rename_i hlength
    apply chainEdgeTableTapeEquiv.injective
    rw [chainEdgeTableTapeEquiv.apply_symm_apply]
    funext index
    simp [chainEdgeTableTapeEquiv]
  · rename_i hlength
    exact (hlength (by simp)).elim

theorem map_chainEdgeTableOfTape
    (targets : List Digest)
    (hlength : targets.length = allChainEdges.length) :
    allChainEdges.map (chainEdgeTableOfTape targets) = targets := by
  unfold chainEdgeTableOfTape
  rw [dif_pos hlength]
  calc
    allChainEdges.map
        (chainEdgeTableTapeEquiv.symm fun index =>
          targets.get (Fin.cast hlength.symm index)) =
        List.ofFn (chainEdgeTableTapeEquiv
          (chainEdgeTableTapeEquiv.symm fun index =>
            targets.get (Fin.cast hlength.symm index))) :=
      (listOfFn_chainEdgeTableTapeEquiv _).symm
    _ = List.ofFn (fun index =>
          targets.get (Fin.cast hlength.symm index)) := by
      rw [chainEdgeTableTapeEquiv.apply_symm_apply]
    _ = List.ofFn targets.get := by
      exact (List.ofFn_congr hlength targets.get).symm
    _ = targets := List.ofFn_get targets

/-- Reading a uniform edge table in the complete edge order gives an i.i.d. uniform digest tape. -/
theorem evalDist_uniformChainEdgeTableTape_eq_drawList :
    𝒟[(fun table : ChainEdgeIndex → Digest => allChainEdges.map table) <$>
      ($ᵗ (ChainEdgeIndex → Digest))] =
    𝒟[OracleComp.drawList ($ᵗ Digest) allChainEdges.length] := by
  calc
    𝒟[(fun table : ChainEdgeIndex → Digest => allChainEdges.map table) <$>
        ($ᵗ (ChainEdgeIndex → Digest))] =
        𝒟[List.ofFn <$> (chainEdgeTableTapeEquiv <$>
          ($ᵗ (ChainEdgeIndex → Digest)))] := by
      simp only [Functor.map_map]
      congr 2
      funext table
      exact (listOfFn_chainEdgeTableTapeEquiv table).symm
    _ = 𝒟[List.ofFn <$>
          ($ᵗ (Fin allChainEdges.length → Digest))] := by
      rw [evalDist_map]
      rw [evalDist_map_bijective_uniform_cross
        (α := ChainEdgeIndex → Digest)
        (β := Fin allChainEdges.length → Digest)
        chainEdgeTableTapeEquiv chainEdgeTableTapeEquiv.bijective]
      rw [← evalDist_map]
    _ = 𝒟[OracleComp.drawList ($ᵗ Digest) allChainEdges.length] :=
      evalDist_listOfFn_uniform_eq_drawList allChainEdges.length

noncomputable def sampleHashOutputsWithDigests :
    List Digest → ProbComp (List HashOutput)
  | [] => pure []
  | target :: targets => do
      let output ← Rom.sampleHashOutputWithDigest target
      let outputs ← sampleHashOutputsWithDigests targets
      return output :: outputs

@[simp]
theorem sampleHashOutputsWithDigests_nil :
    sampleHashOutputsWithDigests [] = pure [] := rfl

theorem sampleHashOutputsWithDigests_cons
    (target : Digest) (targets : List Digest) :
    sampleHashOutputsWithDigests (target :: targets) = do
      let output ← Rom.sampleHashOutputWithDigest target
      let outputs ← sampleHashOutputsWithDigests targets
      return output :: outputs := rfl

noncomputable def batchProgrammedHashTape (count : Nat) :
    ProbComp (List Digest × List HashOutput) := do
  let targets ← OracleComp.drawList ($ᵗ Digest) count
  let outputs ← sampleHashOutputsWithDigests targets
  return (targets, outputs)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
theorem evalDist_batchProgrammedHashTape_succ (count : Nat) :
    𝒟[batchProgrammedHashTape (count + 1)] =
    𝒟[Rom.sampledHashOutputWithDigest >>= fun first =>
      batchProgrammedHashTape count >>= fun rest =>
        pure (first.1 :: rest.1, first.2 :: rest.2)] := by
  unfold batchProgrammedHashTape Rom.sampledHashOutputWithDigest
  rw [OracleComp.drawList]
  simp only [sampleHashOutputsWithDigests_cons, bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro target
  exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _

/-- Batch-sampling uniform low digests and then programming their high halves is the sequential programmed tape. -/
theorem evalDist_batchProgrammedHashTape_eq_programmedHashTape
    (count : Nat) :
    𝒟[batchProgrammedHashTape count] =
      𝒟[Rom.programmedHashTape count] := by
  induction count with
  | zero => simp [batchProgrammedHashTape, OracleComp.drawList,
      Rom.programmedHashTape]
  | succ count ih =>
      rw [evalDist_batchProgrammedHashTape_succ,
        Rom.programmedHashTape]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro first
      conv_lhs => rw [evalDist_bind]
      conv_rhs => rw [evalDist_bind]
      rw [ih]

theorem uniformHashTape_support_info :
    ∀ (count : Nat) (result : List Digest × List HashOutput),
      result ∈ support (Rom.uniformHashTape count) →
      result.1.length = count ∧ result.2.length = count ∧
        result.2.map truncateHash = result.1 := by
  intro count
  induction count with
  | zero =>
      intro result hresult
      simp only [Rom.uniformHashTape, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp
  | succ count ih =>
      intro result hresult
      rw [Rom.uniformHashTape, mem_support_bind_iff] at hresult
      obtain ⟨output, _houtput, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      obtain ⟨htargetLength, houtputLength, htargets⟩ := ih rest hrest
      exact ⟨by simp [htargetLength], by simp [houtputLength], by simp [htargets]⟩

theorem evalDist_uniformHashTape_fst_eq_drawList (count : Nat) :
    𝒟[Prod.fst <$> Rom.uniformHashTape count] =
      𝒟[OracleComp.drawList ($ᵗ Digest) count] := by
  induction count with
  | zero => simp [Rom.uniformHashTape, OracleComp.drawList]
  | succ count ih =>
      rw [Rom.uniformHashTape, OracleComp.drawList]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      calc
        𝒟[$ᵗ HashOutput >>= fun output =>
            Rom.uniformHashTape count >>= fun rest =>
              pure (truncateHash output :: rest.1)] =
            𝒟[(truncateHash <$> ($ᵗ HashOutput)) >>= fun target =>
              (Prod.fst <$> Rom.uniformHashTape count) >>= fun rest =>
                pure (target :: rest)] := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = 𝒟[$ᵗ Digest >>= fun target =>
              (Prod.fst <$> Rom.uniformHashTape count) >>= fun rest =>
                pure (target :: rest)] := by
          conv_lhs => rw [evalDist_bind]
          conv_rhs => rw [evalDist_bind]
          rw [Rom.evalDist_truncate_uniformHashOutput]
        _ = 𝒟[$ᵗ Digest >>= fun target =>
              OracleComp.drawList ($ᵗ Digest) count >>= fun rest =>
                pure (target :: rest)] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro target
          conv_lhs => rw [evalDist_bind]
          conv_rhs => rw [evalDist_bind]
          rw [ih]

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

def installChainTableEdgeOutputs
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (chain : ChainIndex) (table : ChainValueIndex → Digest) :
    List ChainEdgeIndex → List HashOutput → QueryCache HashSpec
  | [], _ => cache
  | _, [] => cache
  | edge :: edges, output :: outputs =>
      installChainTableEdgeOutputs
        (cache.cacheQuery
          (chainTableEdgeInput parameter chain table edge) output)
        parameter chain table edges outputs

@[simp]
theorem installChainTableEdgeOutputs_nil
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (chain : ChainIndex) (table : ChainValueIndex → Digest)
    (outputs : List HashOutput) :
    installChainTableEdgeOutputs cache parameter chain table [] outputs = cache := rfl

@[simp]
theorem installChainTableEdgeOutputs_cons
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (chain : ChainIndex) (table : ChainValueIndex → Digest)
    (edge : ChainEdgeIndex) (edges : List ChainEdgeIndex)
    (output : HashOutput) (outputs : List HashOutput) :
    installChainTableEdgeOutputs cache parameter chain table
      (edge :: edges) (output :: outputs) =
      installChainTableEdgeOutputs
        (cache.cacheQuery
          (chainTableEdgeInput parameter chain table edge) output)
        parameter chain table edges outputs := rfl

set_option linter.constructorNameAsVariable false in
theorem installChainTableEdgeOutputs_info
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) :
    ∀ (edges : List ChainEdgeIndex) (outputs : List HashOutput)
      (cache : QueryCache HashSpec),
      edges.Nodup →
      (∀ edge ∈ edges,
        cache (chainTableEdgeInput parameter chain table edge) = none) →
      outputs.length = edges.length →
      outputs.map truncateHash =
        edges.map (chainTableEdgeTarget table) →
      cache ≤ installChainTableEdgeOutputs cache parameter chain table
        edges outputs ∧
        List.Forall₂
          (fun edge output =>
            (installChainTableEdgeOutputs cache parameter chain table
                edges outputs)
                (chainTableEdgeInput parameter chain table edge) = some output ∧
              truncateHash output = chainTableEdgeTarget table edge)
          edges outputs := by
  intro edges
  induction edges with
  | nil =>
      intro outputs cache _hnodup _habsent hlength _htargets
      cases outputs with
      | nil => simp
      | cons output outputs => simp at hlength
  | cons edge edges ih =>
      intro outputList cache hnodup habsent hlength htargets
      cases outputList with
      | nil => simp at hlength
      | cons output outputs =>
          obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          simp only [List.map_cons, List.cons.injEq] at htargets
          have htailAbsent : ∀ target ∈ edges,
              (cache.cacheQuery
                (chainTableEdgeInput parameter chain table edge) output)
                (chainTableEdgeInput parameter chain table target) = none := by
            intro target htarget
            rw [QueryCache.cacheQuery_of_ne]
            · exact habsent target (by simp [htarget])
            · intro heq
              exact hnotMem
                ((chainTableEdgeInput_injective parameter chain table)
                  heq.symm ▸ htarget)
          obtain ⟨hcacheLe, hpairs⟩ := ih outputs
            (cache.cacheQuery
              (chainTableEdgeInput parameter chain table edge) output)
            htailNodup htailAbsent hlength htargets.2
          constructor
          · exact (QueryCache.le_cacheQuery cache
              (habsent edge (by simp))).trans hcacheLe
          · apply List.Forall₂.cons
            · exact ⟨hcacheLe (QueryCache.cacheQuery_self cache
                (chainTableEdgeInput parameter chain table edge) output),
                htargets.1⟩
            · exact hpairs

/-- The programmed trace is independent output sampling followed by deterministic cache installation. -/
theorem evalDist_programChainTableEdgesTrace_eq_install
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) :
    ∀ (edges : List ChainEdgeIndex) (cache : QueryCache HashSpec),
      𝒟[programChainTableEdgesTrace cache parameter chain table edges] =
      𝒟[(fun outputs =>
          (outputs, installChainTableEdgeOutputs cache parameter chain table
            edges outputs)) <$>
        sampleHashOutputsWithDigests
          (edges.map (chainTableEdgeTarget table))] := by
  intro edges
  induction edges with
  | nil =>
      intro cache
      simp
  | cons edge edges ih =>
      intro cache
      rw [programChainTableEdgesTrace_cons]
      simp only [List.map_cons, sampleHashOutputsWithDigests_cons,
        map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro output
      conv_lhs => rw [evalDist_bind]
      rw [ih]
      simp [map_eq_bind_pure_comp, bind_assoc]

/-- Programming fixed edge targets samples exactly the corresponding independent high-half output tape. -/
theorem evalDist_programChainTableEdgesTrace_fst
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) :
    ∀ (edges : List ChainEdgeIndex) (cache : QueryCache HashSpec),
      𝒟[Prod.fst <$>
        programChainTableEdgesTrace cache parameter chain table edges] =
      𝒟[sampleHashOutputsWithDigests
        (edges.map (chainTableEdgeTarget table))] := by
  intro edges
  induction edges with
  | nil =>
      intro cache
      simp
  | cons edge edges ih =>
      intro cache
      simp only [List.map_cons]
      rw [programChainTableEdgesTrace_cons,
        sampleHashOutputsWithDigests_cons]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro output
      change 𝒟[(fun rest => output :: rest.1) <$>
          programChainTableEdgesTrace
            (cache.cacheQuery
              (chainTableEdgeInput parameter chain table edge) output)
            parameter chain table edges] =
        𝒟[(fun outputs => output :: outputs) <$>
          sampleHashOutputsWithDigests
            (edges.map (chainTableEdgeTarget table))]
      calc
        𝒟[(fun rest => output :: rest.1) <$>
            programChainTableEdgesTrace
              (cache.cacheQuery
                (chainTableEdgeInput parameter chain table edge) output)
              parameter chain table edges] =
            𝒟[(fun outputs => output :: outputs) <$> (Prod.fst <$>
              programChainTableEdgesTrace
                (cache.cacheQuery
                  (chainTableEdgeInput parameter chain table edge) output)
                parameter chain table edges)] := by
          simp [Functor.map_map]
        _ = 𝒟[(fun outputs => output :: outputs) <$>
              sampleHashOutputsWithDigests
                (edges.map (chainTableEdgeTarget table))] := by
          rw [evalDist_map, ih, ← evalDist_map]

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

theorem chainTableEdgeTarget_materialEquiv_symm
    (seeds : Epoch → Digest) (edges : ChainEdgeIndex → Digest) :
    chainTableEdgeTarget
      (chainTableMaterialEquiv.symm (seeds, edges)) = edges := by
  have hmaterial := chainTableMaterialEquiv.apply_symm_apply (seeds, edges)
  exact congrArg Prod.snd hmaterial

theorem chainTableSeedTargets_materialEquiv_symm
    (seeds : Epoch → Digest) (edges : ChainEdgeIndex → Digest) :
    chainTableSeedTargets
      (chainTableMaterialEquiv.symm (seeds, edges)) = seeds := by
  have hmaterial := chainTableMaterialEquiv.apply_symm_apply (seeds, edges)
  exact congrArg Prod.fst hmaterial

noncomputable def programmedUniformChainEdgeTape
    (parameter : PublicParameter) (chain : ChainIndex)
    (seeds : Epoch → Digest) :
    ProbComp (List Digest × List HashOutput) := do
  let edges ← $ᵗ (ChainEdgeIndex → Digest)
  let table := chainTableMaterialEquiv.symm (seeds, edges)
  let outputs ← Prod.fst <$>
    programChainTableEdgesTrace ∅ parameter chain table allChainEdges
  return (allChainEdges.map edges, outputs)

noncomputable def sampledUniformChainEdgeTape
    (seeds : Epoch → Digest) :
    ProbComp (List Digest × List HashOutput) := do
  let edges ← $ᵗ (ChainEdgeIndex → Digest)
  let table := chainTableMaterialEquiv.symm (seeds, edges)
  let outputs ← sampleHashOutputsWithDigests
    (allChainEdges.map (chainTableEdgeTarget table))
  return (allChainEdges.map edges, outputs)

noncomputable def installedChainEdgeTapeResult
    (parameter : PublicParameter) (chain : ChainIndex)
    (seeds : Epoch → Digest)
    (tape : List Digest × List HashOutput) :
    List Digest × (List HashOutput × QueryCache HashSpec) :=
  let edges := chainEdgeTableOfTape tape.1
  let table := chainTableMaterialEquiv.symm (seeds, edges)
  (tape.1, (tape.2,
    installChainTableEdgeOutputs ∅ parameter chain table
      allChainEdges tape.2))

noncomputable def programmedUniformChainEdgeCache
    (parameter : PublicParameter) (chain : ChainIndex)
    (seeds : Epoch → Digest) :
    ProbComp (List Digest × (List HashOutput × QueryCache HashSpec)) := do
  let edges ← $ᵗ (ChainEdgeIndex → Digest)
  let table := chainTableMaterialEquiv.symm (seeds, edges)
  let trace ← programChainTableEdgesTrace ∅ parameter chain table allChainEdges
  return (allChainEdges.map edges, trace)

noncomputable def uniformInstalledChainEdgeCache
    (parameter : PublicParameter) (chain : ChainIndex)
    (seeds : Epoch → Digest) :
    ProbComp (List Digest × (List HashOutput × QueryCache HashSpec)) :=
  installedChainEdgeTapeResult parameter chain seeds <$>
    Rom.uniformHashTape allChainEdges.length

noncomputable def fixedChainMaterialRepresentation
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp ((List Digest × FlatSecret) ×
      (List Digest × (List HashOutput × QueryCache HashSpec))) := do
  let secretView ← extractFixedChainSeeds chain allEpochs
  let seeds := fun epoch => secretView.2 (epoch, chain)
  let edgeView ← uniformInstalledChainEdgeCache parameter chain seeds
  return (secretView, edgeView)

theorem evalDist_uniformInstalledChainEdgeTable_eq_uniform
    (parameter : PublicParameter) (chain : ChainIndex)
    (seeds : Epoch → Digest) :
    𝒟[(fun result : List Digest × (List HashOutput × QueryCache HashSpec) =>
        chainEdgeTableOfTape result.1) <$>
      uniformInstalledChainEdgeCache parameter chain seeds] =
      𝒟[$ᵗ (ChainEdgeIndex → Digest)] := by
  unfold uniformInstalledChainEdgeCache installedChainEdgeTapeResult
  simp only [Functor.map_map]
  calc
    𝒟[(fun tape : List Digest × List HashOutput =>
          chainEdgeTableOfTape tape.1) <$>
        Rom.uniformHashTape allChainEdges.length] =
        𝒟[chainEdgeTableOfTape <$>
          (Prod.fst <$> Rom.uniformHashTape allChainEdges.length)] := by
      simp [Functor.map_map]
    _ = 𝒟[chainEdgeTableOfTape <$>
          OracleComp.drawList ($ᵗ Digest) allChainEdges.length] := by
      rw [evalDist_map, evalDist_uniformHashTape_fst_eq_drawList, ← evalDist_map]
    _ = 𝒟[chainEdgeTableOfTape <$>
          ((fun edges : ChainEdgeIndex → Digest => allChainEdges.map edges) <$>
            ($ᵗ (ChainEdgeIndex → Digest)))] := by
      simp only [evalDist_map]
      have hdist := evalDist_uniformChainEdgeTableTape_eq_drawList.symm
      rw [evalDist_map] at hdist
      exact congrArg (Functor.map chainEdgeTableOfTape) hdist
    _ = 𝒟[$ᵗ (ChainEdgeIndex → Digest)] := by
      simp [Functor.map_map]

noncomputable def extractedFixedChainSeedTable
    (chain : ChainIndex) : ProbComp (Epoch → Digest) :=
  (fun result : List Digest × FlatSecret =>
    fun epoch => result.2 (epoch, chain)) <$>
      extractFixedChainSeeds chain allEpochs

theorem evalDist_uniformFlatSecret_fixedChain_eq_uniform
    (chain : ChainIndex) :
    𝒟[(fun table : FlatSecret => fun epoch => table (epoch, chain)) <$>
      ($ᵗ FlatSecret)] =
      𝒟[$ᵗ (Epoch → Digest)] := by
  let embed : Epoch → Epoch × ChainIndex := fun epoch => (epoch, chain)
  have hembed : Function.Injective embed := by
    intro left right heq
    exact congrArg Prod.fst heq
  rw [map_eq_bind_pure_comp]
  change 𝒟[do
    let table ← $ᵗ FlatSecret
    pure (table ∘ embed)] = 𝒟[$ᵗ (Epoch → Digest)]
  exact evalDist_uniformSample_map_comp_injective
    (R := Digest) hembed

theorem evalDist_extractedFixedChainSeedTable_eq_uniform
    (chain : ChainIndex) :
    𝒟[extractedFixedChainSeedTable chain] =
      𝒟[$ᵗ (Epoch → Digest)] := by
  unfold extractedFixedChainSeedTable
  calc
    𝒟[(fun result : List Digest × FlatSecret =>
          fun epoch => result.2 (epoch, chain)) <$>
        extractFixedChainSeeds chain allEpochs] =
        𝒟[(fun result : List Digest × FlatSecret =>
          fun epoch => result.2 (epoch, chain)) <$>
            (fixedChainSeedView chain allEpochs <$>
              ($ᵗ FlatSecret))] := by
      rw [evalDist_map,
        evalDist_extractFixedChainSeeds_eq_uniform chain allEpochs allEpochs_nodup,
        ← evalDist_map]
    _ = 𝒟[(fun table : FlatSecret => fun epoch => table (epoch, chain)) <$>
          ($ᵗ FlatSecret)] := by
      simp [Functor.map_map, fixedChainSeedView]
    _ = 𝒟[$ᵗ (Epoch → Digest)] :=
      evalDist_uniformFlatSecret_fixedChain_eq_uniform chain

noncomputable def fixedChainMaterialTable
    (chain : ChainIndex)
    (result : (List Digest × FlatSecret) ×
      (List Digest × (List HashOutput × QueryCache HashSpec))) :
    ChainValueIndex → Digest :=
  chainTableMaterialEquiv.symm
    ((fun epoch => result.1.2 (epoch, chain)),
      chainEdgeTableOfTape result.2.1)

noncomputable def fixedChainMaterialTableOnly
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (ChainValueIndex → Digest) :=
  fixedChainMaterialTable chain <$>
    fixedChainMaterialRepresentation parameter chain

theorem evalDist_fixedChainMaterialTableOnly_eq_uniform
    (parameter : PublicParameter) (chain : ChainIndex) :
    𝒟[fixedChainMaterialTableOnly parameter chain] =
      𝒟[$ᵗ (ChainValueIndex → Digest)] := by
  have hnormalize :
      𝒟[fixedChainMaterialTableOnly parameter chain] =
      𝒟[extractedFixedChainSeedTable chain >>= fun seeds =>
        ((fun result : List Digest × (List HashOutput × QueryCache HashSpec) =>
          chainEdgeTableOfTape result.1) <$>
            uniformInstalledChainEdgeCache parameter chain seeds) >>= fun edges =>
          pure (chainTableMaterialEquiv.symm (seeds, edges))] := by
    simp [fixedChainMaterialTableOnly, fixedChainMaterialRepresentation,
      fixedChainMaterialTable, extractedFixedChainSeedTable,
      map_eq_bind_pure_comp, bind_assoc]
  rw [hnormalize]
  calc
    𝒟[extractedFixedChainSeedTable chain >>= fun seeds =>
        ((fun result : List Digest × (List HashOutput × QueryCache HashSpec) =>
          chainEdgeTableOfTape result.1) <$>
            uniformInstalledChainEdgeCache parameter chain seeds) >>= fun edges =>
          pure (chainTableMaterialEquiv.symm (seeds, edges))] =
        𝒟[($ᵗ (Epoch → Digest)) >>= fun seeds =>
          ((fun result : List Digest × (List HashOutput × QueryCache HashSpec) =>
            chainEdgeTableOfTape result.1) <$>
              uniformInstalledChainEdgeCache parameter chain seeds) >>= fun edges =>
            pure (chainTableMaterialEquiv.symm (seeds, edges))] := by
      rw [evalDist_bind,
        evalDist_extractedFixedChainSeedTable_eq_uniform chain,
        ← evalDist_bind]
    _ = 𝒟[($ᵗ (Epoch → Digest)) >>= fun seeds =>
          ($ᵗ (ChainEdgeIndex → Digest)) >>= fun edges =>
            pure (chainTableMaterialEquiv.symm (seeds, edges))] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro seeds
      rw [evalDist_bind,
        evalDist_uniformInstalledChainEdgeTable_eq_uniform parameter chain seeds,
        ← evalDist_bind]
    _ = 𝒟[chainTableMaterialEquiv.symm <$>
          independentChainTableMaterial] := by
      simp [independentChainTableMaterial, monad_norm]
    _ = 𝒟[chainTableMaterialEquiv.symm <$>
          (chainTableMaterialEquiv <$>
            ($ᵗ (ChainValueIndex → Digest)))] := by
      simp only [evalDist_map]
      have hdist := evalDist_split_uniformChainTable_eq_independent
      rw [evalDist_map] at hdist
      exact congrArg (Functor.map chainTableMaterialEquiv.symm) hdist.symm
    _ = 𝒟[$ᵗ (ChainValueIndex → Digest)] := by
      simp [Functor.map_map]

theorem evalDist_programmedUniformChainEdgeTape_eq_sampled
    (parameter : PublicParameter) (chain : ChainIndex)
    (seeds : Epoch → Digest) :
    𝒟[programmedUniformChainEdgeTape parameter chain seeds] =
      𝒟[sampledUniformChainEdgeTape seeds] := by
  unfold programmedUniformChainEdgeTape sampledUniformChainEdgeTape
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro edges
  conv_lhs => rw [evalDist_bind]
  conv_rhs => rw [evalDist_bind]
  rw [evalDist_programChainTableEdgesTrace_fst]

theorem evalDist_programmedChainEdgeCache_fixedTable_eq_installed
    (parameter : PublicParameter) (chain : ChainIndex)
    (seeds : Epoch → Digest) (edges : ChainEdgeIndex → Digest) :
    let table := chainTableMaterialEquiv.symm (seeds, edges)
    𝒟[(fun trace => (allChainEdges.map edges, trace)) <$>
      programChainTableEdgesTrace ∅ parameter chain table allChainEdges] =
    𝒟[installedChainEdgeTapeResult parameter chain seeds <$>
      ((fun outputs => (allChainEdges.map edges, outputs)) <$>
        sampleHashOutputsWithDigests
          (allChainEdges.map (chainTableEdgeTarget table)))] := by
  dsimp only
  rw [evalDist_map, evalDist_programChainTableEdgesTrace_eq_install,
    ← evalDist_map]
  simp [Functor.map_map, installedChainEdgeTapeResult,
    chainEdgeTableOfTape_map]

/-- A uniform edge table programmed into the oracle has exactly the ordinary uniform output-tape distribution. -/
theorem evalDist_programmedUniformChainEdgeTape_eq_uniformHashTape
    (parameter : PublicParameter) (chain : ChainIndex)
    (seeds : Epoch → Digest) :
    𝒟[programmedUniformChainEdgeTape parameter chain seeds] =
      𝒟[Rom.uniformHashTape allChainEdges.length] := by
  calc
    𝒟[programmedUniformChainEdgeTape parameter chain seeds] =
        𝒟[sampledUniformChainEdgeTape seeds] :=
      evalDist_programmedUniformChainEdgeTape_eq_sampled parameter chain seeds
    _ = 𝒟[$ᵗ (ChainEdgeIndex → Digest) >>= fun edges =>
          sampleHashOutputsWithDigests (allChainEdges.map edges) >>= fun outputs =>
            pure (allChainEdges.map edges, outputs)] := by
      unfold sampledUniformChainEdgeTape
      simp only [chainTableEdgeTarget_materialEquiv_symm]
    _ = 𝒟[((fun edges : ChainEdgeIndex → Digest =>
          allChainEdges.map edges) <$> ($ᵗ (ChainEdgeIndex → Digest))) >>= fun targets =>
          sampleHashOutputsWithDigests targets >>= fun outputs =>
            pure (targets, outputs)] := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = 𝒟[OracleComp.drawList ($ᵗ Digest) allChainEdges.length >>= fun targets =>
          sampleHashOutputsWithDigests targets >>= fun outputs =>
            pure (targets, outputs)] := by
      rw [evalDist_bind, evalDist_uniformChainEdgeTableTape_eq_drawList,
        ← evalDist_bind]
    _ = 𝒟[batchProgrammedHashTape allChainEdges.length] := by
      rfl
    _ = 𝒟[Rom.programmedHashTape allChainEdges.length] :=
      evalDist_batchProgrammedHashTape_eq_programmedHashTape
        allChainEdges.length
    _ = 𝒟[Rom.uniformHashTape allChainEdges.length] :=
      Rom.evalDist_programmedHashTape_eq_uniformHashTape allChainEdges.length

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
/-- The full programmed cache, not only its output tape, is a deterministic installation of an ordinary uniform tape. -/
theorem evalDist_programmedUniformChainEdgeCache_eq_uniformInstalled
    (parameter : PublicParameter) (chain : ChainIndex)
    (seeds : Epoch → Digest) :
    𝒟[programmedUniformChainEdgeCache parameter chain seeds] =
      𝒟[uniformInstalledChainEdgeCache parameter chain seeds] := by
  calc
    𝒟[programmedUniformChainEdgeCache parameter chain seeds] =
        𝒟[installedChainEdgeTapeResult parameter chain seeds <$>
          sampledUniformChainEdgeTape seeds] := by
      unfold programmedUniformChainEdgeCache sampledUniformChainEdgeTape
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro edges
      simpa [map_eq_bind_pure_comp, bind_assoc] using
        (evalDist_programmedChainEdgeCache_fixedTable_eq_installed
          parameter chain seeds edges)
    _ = 𝒟[installedChainEdgeTapeResult parameter chain seeds <$>
          programmedUniformChainEdgeTape parameter chain seeds] := by
      conv_lhs => rw [evalDist_map]
      conv_rhs => rw [evalDist_map]
      rw [← evalDist_programmedUniformChainEdgeTape_eq_sampled]
    _ = 𝒟[installedChainEdgeTapeResult parameter chain seeds <$>
          Rom.uniformHashTape allChainEdges.length] := by
      rw [evalDist_map,
        evalDist_programmedUniformChainEdgeTape_eq_uniformHashTape,
        ← evalDist_map]
    _ = 𝒟[uniformInstalledChainEdgeCache parameter chain seeds] := by
      rfl

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

/-- Installing a complete matching output tape realizes every edge of the candidate table. -/
theorem installAllChainTableEdgeOutputs_edgesMatch
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) (outputs : List HashOutput)
    (hlength : outputs.length = allChainEdges.length)
    (htargets : outputs.map truncateHash =
      allChainEdges.map (chainTableEdgeTarget table)) :
    ChainTableEdgesMatch
      (installChainTableEdgeOutputs ∅ parameter chain table
        allChainEdges outputs)
      parameter chain table := by
  have hinfo := installChainTableEdgeOutputs_info parameter chain table
    allChainEdges outputs ∅ allChainEdges_nodup (by simp) hlength htargets
  intro edge
  obtain ⟨output, hcache, htruncate⟩ :=
    exists_right_of_forall₂ hinfo.2 edge (mem_allChainEdges edge)
  exact ⟨output, hcache, htruncate⟩

/-- Every installed uniform tape realizes the table reconstructed from its low digests. -/
theorem uniformInstalledChainEdgeCache_edgesMatch
    (parameter : PublicParameter) (chain : ChainIndex)
    (seeds : Epoch → Digest)
    (result : List Digest × (List HashOutput × QueryCache HashSpec))
    (hresult : result ∈ support
      (uniformInstalledChainEdgeCache parameter chain seeds)) :
    ChainTableEdgesMatch result.2.2 parameter chain
      (chainTableMaterialEquiv.symm
        (seeds, chainEdgeTableOfTape result.1)) := by
  unfold uniformInstalledChainEdgeCache at hresult
  rw [support_map] at hresult
  obtain ⟨tape, htape, heq⟩ := hresult
  subst result
  have hinfo := uniformHashTape_support_info allChainEdges.length tape htape
  let edges := chainEdgeTableOfTape tape.1
  let table := chainTableMaterialEquiv.symm (seeds, edges)
  change ChainTableEdgesMatch
    (installChainTableEdgeOutputs ∅ parameter chain table
      allChainEdges tape.2) parameter chain table
  apply installAllChainTableEdgeOutputs_edgesMatch
  · exact hinfo.2.1
  · calc
      tape.2.map truncateHash = tape.1 := hinfo.2.2
      _ = allChainEdges.map edges :=
        (map_chainEdgeTableOfTape tape.1 hinfo.1).symm
      _ = allChainEdges.map (chainTableEdgeTarget table) := by
        rw [chainTableEdgeTarget_materialEquiv_symm]

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

/-- With the fixed-chain seeds inserted into an otherwise arbitrary secret, replaying the installed cache gives exactly the reconstructed uniform table. -/
theorem uniformInstalledChainEdgeCache_keygenChainValueTable_eq
    (parameter : PublicParameter) (chain : ChainIndex)
    (seeds : Epoch → Digest)
    (other : Epoch → ChainIndex → Digest)
    (result : List Digest × (List HashOutput × QueryCache HashSpec))
    (hresult : result ∈ support
      (uniformInstalledChainEdgeCache parameter chain seeds)) :
    let secret := secretWithFixedChainSeeds other chain seeds
    let table := chainTableMaterialEquiv.symm
      (seeds, chainEdgeTableOfTape result.1)
    keygenChainValueTable result.2.2 ⟨parameter, secret⟩ chain = table := by
  dsimp only
  apply keygenChainValueTable_eq_of_matches
  · intro epoch
    change secretWithFixedChainSeeds other chain seeds epoch chain = _
    rw [secretWithFixedChainSeeds_fixedChain]
    have hseeds := congrFun
      (chainTableSeedTargets_materialEquiv_symm seeds
        (chainEdgeTableOfTape result.1)) epoch
    simpa [chainTableSeedTargets] using hseeds.symm
  · exact uniformInstalledChainEdgeCache_edgesMatch
      parameter chain seeds result hresult

/-- The combined ideal material experiment exposes the seed tape and realizes one uniform hidden WOTS table in the replay cache. -/
theorem fixedChainMaterialRepresentation_support_info
    (parameter : PublicParameter) (chain : ChainIndex)
    (result : (List Digest × FlatSecret) ×
      (List Digest × (List HashOutput × QueryCache HashSpec)))
    (hresult : result ∈ support
      (fixedChainMaterialRepresentation parameter chain)) :
    List.Forall₂
        (fun epoch value => result.1.2 (epoch, chain) = value)
        allEpochs result.1.1 ∧
      keygenChainValueTable result.2.2.2
        ⟨parameter, unflattenSecret result.1.2⟩ chain =
        chainTableMaterialEquiv.symm
          ((fun epoch => result.1.2 (epoch, chain)),
            chainEdgeTableOfTape result.2.1) := by
  unfold fixedChainMaterialRepresentation at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨secretView, hsecretView, hedgeView⟩ := hresult
  rw [mem_support_bind_iff] at hedgeView
  obtain ⟨edgeView, hedgeView, hpure⟩ := hedgeView
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  constructor
  · exact (extractFixedChainSeeds_support_info chain allEpochs
      allEpochs_nodup secretView hsecretView).2
  · have htable := uniformInstalledChainEdgeCache_keygenChainValueTable_eq
      parameter chain (fun epoch => secretView.2 (epoch, chain))
      (unflattenSecret secretView.2) edgeView hedgeView
    rw [secretWithOwnFixedChainSeeds] at htable
    exact htable

theorem fixedChainMaterialRepresentation_keygenTable_eq_materialTable
    (parameter : PublicParameter) (chain : ChainIndex)
    (result : (List Digest × FlatSecret) ×
      (List Digest × (List HashOutput × QueryCache HashSpec)))
    (hresult : result ∈ support
      (fixedChainMaterialRepresentation parameter chain)) :
    keygenChainValueTable result.2.2.2
        ⟨parameter, unflattenSecret result.1.2⟩ chain =
      fixedChainMaterialTable chain result := by
  exact (fixedChainMaterialRepresentation_support_info
    parameter chain result hresult).2

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
