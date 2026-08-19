import XmssSecurity.Proof.CacheCardinality
import XmssSecurity.Proof.ConcreteExecution
import XmssSecurity.Proof.EncodingTargetMap
import XmssSecurity.Proof.AdaptiveEpochCollision
import XmssSecurity.Proof.SigningRandomnessUniformity
import XmssSecurity.Proof.AdaptiveFreshTarget
import XmssSecurity.Proof.QueryPresence
import Mathlib.Data.Set.Card.Arithmetic
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

/-- Every successful fixed-randomness signing attempt returns the randomness supplied to that attempt. -/
theorem Concrete.signAttempt_support_randomness
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (initialCache finalCache : QueryCache HashSpec)
    (signature : Signature)
    (hmem : (some signature, finalCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.signAttempt secretKey epoch message randomness :
          OracleComp HashSpec (Option Signature))).run initialCache)) :
    signature.randomness = randomness := by
  have heval := Concrete.CacheReplay.eval_answerFn_finalCache_eq_of_mem_support
    (Concrete.signAttempt secretKey epoch message randomness :
      OracleComp HashSpec (Option Signature)) initialCache finalCache
      (some signature) hmem
  rw [Concrete.CacheReplay.eval_signAttempt] at heval
  unfold Concrete.CacheReplay.signAttempt at heval
  split at heval
  · simp at heval
  · rename_i _ encoding hdecode
    simp only [Option.some.injEq] at heval
    simpa only [Concrete.CacheReplay.signWithEncoding] using
      congrArg Signature.randomness heval.symm

/-- Truncated outputs already cached at encoding inputs for one epoch. The conditional definition is empty on artificial infinite caches; every cache reachable by a bounded game is finite. -/
noncomputable def cachedEncodingDigests (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch) : Finset Digest := by
  classical
  exact if hfinite : cache.toSet.Finite then
    (hfinite.toFinset.filter fun entry =>
      encodingInputEpoch? parameter entry.1 = some epoch).image fun entry =>
        truncateHash entry.2
  else
    ∅

/-- Cache entries whose serialized input belongs to one encoding epoch. -/
noncomputable def cachedEncodingEntries (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch) :
    Finset ((t : HashSpec.Domain) × HashSpec.Range t) := by
  classical
  exact if hfinite : cache.toSet.Finite then
    hfinite.toFinset.filter fun entry =>
      encodingInputEpoch? parameter entry.1 = some epoch
  else
    ∅

noncomputable def cachedEncodingEntryCount (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch) : ℝ≥0∞ :=
  (({entry ∈ cache.toSet |
    encodingInputEpoch? parameter entry.1 = some epoch}.encard : ENat) : ℝ≥0∞)

def cachedEncodingInputSet (cache : QueryCache HashSpec)
    (parameter : PublicParameter) :
    Set ((t : HashSpec.Domain) × HashSpec.Range t) :=
  {entry ∈ cache.toSet | (encodingInputEpoch? parameter entry.1).isSome}

noncomputable def cachedEncodingInputCount (cache : QueryCache HashSpec)
    (parameter : PublicParameter) : ℝ≥0∞ :=
  ((cachedEncodingInputSet cache parameter).encard : ENat)

theorem ENat_toENNReal_fintype_sum (value : Epoch → ENat) :
    (((∑ epoch : Epoch, value epoch) : ENat) : ℝ≥0∞) =
      ∑ epoch : Epoch, ((value epoch : ENat) : ℝ≥0∞) := by
  classical
  have haux : ∀ entries : Finset Epoch,
      (((∑ epoch ∈ entries, value epoch) : ENat) : ℝ≥0∞) =
        ∑ epoch ∈ entries, ((value epoch : ENat) : ℝ≥0∞) := by
    intro entries
    induction entries using Finset.induction_on with
    | empty => simp
    | insert epoch entries hnotMem ih =>
        simp [hnotMem, ih, ENat.toENNReal_add]
  simpa using haux Finset.univ

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem sum_cachedEncodingEntryCount_univ_eq_cachedEncodingInputCount
    (cache : QueryCache HashSpec) (parameter : PublicParameter) :
    (∑ epoch : Epoch, cachedEncodingEntryCount cache parameter epoch) =
      cachedEncodingInputCount cache parameter := by
  classical
  let fiber := fun epoch : Epoch =>
    {entry ∈ cache.toSet |
      encodingInputEpoch? parameter entry.1 = some epoch}
  have hdisjoint : Pairwise fun left right => Disjoint (fiber left) (fiber right) := by
    intro left right hne
    rw [Set.disjoint_left]
    intro entry hleft hright
    have heq : (some left : Option Epoch) = some right :=
      hleft.2.symm.trans hright.2
    exact hne (Option.some.inj heq)
  have hunion : (⋃ epoch, fiber epoch) = cachedEncodingInputSet cache parameter := by
    ext entry
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, fiber, cachedEncodingInputSet]
    constructor
    · rintro ⟨epoch, hcache, hepoch⟩
      exact ⟨hcache, by simp [hepoch]⟩
    · rintro ⟨hcache, hsome⟩
      obtain ⟨epoch, hepoch⟩ := Option.isSome_iff_exists.mp hsome
      exact ⟨epoch, hcache, hepoch⟩
  have hcard := Set.encard_iUnion_of_finite hdisjoint
  rw [hunion, finsum_eq_sum_of_fintype] at hcard
  unfold cachedEncodingEntryCount cachedEncodingInputCount
  have hcast := congrArg ENat.toENNReal hcard.symm
  rw [ENat_toENNReal_fintype_sum] at hcast
  exact hcast

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem cachedEncodingInputSet_cacheQuery_subset
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (input : HashInput) (output : HashOutput) :
    cachedEncodingInputSet (cache.cacheQuery input output) parameter ⊆
      if (encodingInputEpoch? parameter input).isSome then
        insert ⟨input, output⟩ (cachedEncodingInputSet cache parameter)
      else
        cachedEncodingInputSet cache parameter := by
  intro entry hentry
  have hinsert := QueryCache.toSet_cacheQuery_subset_insert cache input output hentry.1
  rw [Set.mem_insert_iff] at hinsert
  cases hepoch : encodingInputEpoch? parameter input with
  | some epoch =>
    simp only [Option.isSome_some, if_true, Set.mem_insert_iff]
    rcases hinsert with heq | hold
    · exact Or.inl heq
    · exact Or.inr ⟨hold, hentry.2⟩
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, if_false]
    rcases hinsert with heq | hold
    · subst entry
      have hisSome := hentry.2
      change (encodingInputEpoch? parameter input).isSome = true at hisSome
      rw [hepoch] at hisSome
      exact Bool.noConfusion hisSome
    · exact ⟨hold, hentry.2⟩

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem cachedEncodingInputCount_cacheQuery_le
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (input : HashInput) (output : HashOutput) :
    cachedEncodingInputCount (cache.cacheQuery input output) parameter ≤
      cachedEncodingInputCount cache parameter +
        if (encodingInputEpoch? parameter input).isSome then 1 else 0 := by
  unfold cachedEncodingInputCount
  let newEntry : (t : HashSpec.Domain) × HashSpec.Range t := ⟨input, output⟩
  have hsubset :=
    cachedEncodingInputSet_cacheQuery_subset cache parameter input output
  cases hepoch : encodingInputEpoch? parameter input with
  | some epoch =>
    have hsubset' :
        cachedEncodingInputSet (cache.cacheQuery input output) parameter ⊆
          insert newEntry (cachedEncodingInputSet cache parameter) := by
      simpa [hepoch, newEntry] using hsubset
    have hmono := Set.encard_mono hsubset'
    have hinsert := Set.encard_insert_le
      (cachedEncodingInputSet cache parameter) newEntry
    have hencard :
        (cachedEncodingInputSet (cache.cacheQuery input output) parameter).encard ≤
          (cachedEncodingInputSet cache parameter).encard + 1 := hmono.trans hinsert
    have hcast := ENat.toENNReal_mono hencard
    simpa [hepoch, ENat.toENNReal_add] using hcast
  | none =>
    have hsubset' :
        cachedEncodingInputSet (cache.cacheQuery input output) parameter ⊆
          cachedEncodingInputSet cache parameter := by
      simpa [hepoch] using hsubset
    have hencard :
        (cachedEncodingInputSet (cache.cacheQuery input output) parameter).encard ≤
          (cachedEncodingInputSet cache parameter).encard :=
      Set.encard_mono hsubset'
    have hcast := ENat.toENNReal_mono hencard
    simpa [hepoch] using hcast

theorem cachedEncodingEntryCount_eq_card_of_finite
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (epoch : Epoch)
    (hfinite : cache.toSet.Finite) :
    cachedEncodingEntryCount cache parameter epoch =
      (cachedEncodingEntries cache parameter epoch).card := by
  classical
  let fiber := {entry ∈ cache.toSet |
    encodingInputEpoch? parameter entry.1 = some epoch}
  have hfiber : fiber.Finite := hfinite.subset (by
    intro entry hentry
    exact hentry.1)
  unfold cachedEncodingEntryCount cachedEncodingEntries
  rw [dif_pos hfinite]
  change ((fiber.encard : ENat) : ℝ≥0∞) = _
  rw [hfiber.encard_eq_coe_toFinset_card, ENat.toENNReal_coe]
  norm_cast
  apply congrArg Finset.card
  ext entry
  simp [fiber]

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
theorem uniform_signingRandomness_encodingInput_cacheHit_le_cachedEncodingEntries
    (parameter : PublicParameter) (epoch : Epoch) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : cache.toSet.Finite) :
    Pr[fun randomness : Randomness => ∃ output,
      cache (Concrete.CacheView.encodingInput parameter epoch (message, randomness)) =
        some output |
      $ᵗ Randomness] ≤
      ((cachedEncodingEntries cache parameter epoch).card : ℝ≥0∞) *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  let entries := cachedEncodingEntries cache parameter epoch
  let targets := entries.image fun entry => entry.1
  calc
    _ ≤ Pr[fun randomness : Randomness => ∃ input ∈ targets,
        Concrete.CacheView.encodingInput parameter epoch (message, randomness) = input |
        $ᵗ Randomness] := by
      apply probEvent_mono
      intro randomness _hrandomness
      rintro ⟨output, hcache⟩
      let input := Concrete.CacheView.encodingInput parameter epoch (message, randomness)
      have hentry : (⟨input, output⟩ : (t : HashSpec.Domain) × HashSpec.Range t) ∈
          entries := by
        unfold entries cachedEncodingEntries
        rw [dif_pos hfinite, Finset.mem_filter]
        exact ⟨by simpa [input] using hcache, by simp [input]⟩
      exact ⟨input, Finset.mem_image.mpr ⟨⟨input, output⟩, hentry, rfl⟩, rfl⟩
    _ ≤ (targets.card : ℝ≥0∞) *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ :=
      uniform_signingRandomness_encodingInput_hits_finset_le
        parameter epoch message targets
    _ ≤ (entries.card : ℝ≥0∞) *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
      gcongr
      exact_mod_cast Finset.card_image_le

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem uniform_signingRandomness_encodingInput_cacheHit_le_cachedEncodingEntryCount
    (parameter : PublicParameter) (epoch : Epoch) (message : Message)
    (cache : QueryCache HashSpec) :
    Pr[fun randomness : Randomness => ∃ output,
      cache (Concrete.CacheView.encodingInput parameter epoch (message, randomness)) =
        some output |
      $ᵗ Randomness] ≤
      cachedEncodingEntryCount cache parameter epoch *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  let hit : Randomness → Prop := fun randomness => ∃ output,
    cache (Concrete.CacheView.encodingInput parameter epoch (message, randomness)) =
      some output
  let targets : Finset Randomness := Finset.univ.filter hit
  let fiber := {entry ∈ cache.toSet |
    encodingInputEpoch? parameter entry.1 = some epoch}
  have hcard : (targets.card : ℝ≥0∞) ≤ cachedEncodingEntryCount cache parameter epoch := by
    let embedding : (targets : Set Randomness) ↪ fiber :=
      ⟨fun randomness =>
          ⟨⟨Concrete.CacheView.encodingInput parameter epoch
                (message, randomness.1),
              Classical.choose (Finset.mem_filter.mp randomness.2).2⟩,
            ⟨Classical.choose_spec (Finset.mem_filter.mp randomness.2).2, by simp⟩⟩,
        fun left right heq => Subtype.ext <| congrArg Prod.snd <|
          Concrete.CacheView.encodingInput_injective parameter epoch <|
            congrArg (fun entry : fiber => entry.1.1) heq⟩
    simpa only [cachedEncodingEntryCount, fiber,
      Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe] using
      ENat.toENNReal_mono embedding.encard_le
  rw [probEvent_uniformSample, card_randomness, div_eq_mul_inv]
  change (targets.card : ℝ≥0∞) *
      ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ ≤ _
  exact mul_le_mul' hcard le_rfl

theorem sum_cachedEncodingEntries_card_le_enncard
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epochs : Finset Epoch) :
    ((∑ epoch ∈ epochs,
        (cachedEncodingEntries cache parameter epoch).card : Nat) : ℝ≥0∞) ≤
      QueryCache.enncard cache := by
  classical
  unfold cachedEncodingEntries
  split <;> rename_i hfinite
  · let entries := hfinite.toFinset
    let taggedEpochs := epochs.image some
    have hsum := Finset.sum_card_fiberwise_eq_card_filter entries taggedEpochs
      (fun entry => encodingInputEpoch? parameter entry.1)
    have himage :
        (∑ epoch ∈ epochs,
            (entries.filter fun entry =>
              encodingInputEpoch? parameter entry.1 = some epoch).card) =
          ∑ tag ∈ taggedEpochs,
            (entries.filter fun entry =>
              encodingInputEpoch? parameter entry.1 = tag).card := by
      rw [Finset.sum_image]
      intro left _ right _ heq
      exact Option.some.inj heq
    rw [himage, hsum]
    calc
      (((entries.filter fun entry =>
          encodingInputEpoch? parameter entry.1 ∈ taggedEpochs).card : Nat) : ℝ≥0∞) ≤
          (entries.card : ℝ≥0∞) := by
        exact_mod_cast Finset.card_filter_le entries _
      _ = QueryCache.enncard cache := by
        simp only [entries, QueryCache.enncard,
          hfinite.encard_eq_coe_toFinset_card, ENat.toENNReal_coe]
  · simp

theorem sum_cachedEncodingEntryCount_le_enncard
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epochs : Finset Epoch) :
    (∑ epoch ∈ epochs, cachedEncodingEntryCount cache parameter epoch) ≤
      QueryCache.enncard cache := by
  classical
  by_cases hfinite : cache.toSet.Finite
  · simp_rw [cachedEncodingEntryCount_eq_card_of_finite cache parameter _ hfinite]
    simpa [Nat.cast_sum] using
      sum_cachedEncodingEntries_card_le_enncard cache parameter epochs
  · have hinfinite : cache.toSet.Infinite := Set.not_finite.mp hfinite
    rw [show QueryCache.enncard cache = ⊤ by
      simp [QueryCache.enncard, Set.encard_eq_top hinfinite]]
    exact le_top

theorem cachedEncodingDigests_card_le_cachedEncodingEntries_card
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (epoch : Epoch) :
    (cachedEncodingDigests cache parameter epoch).card ≤
      (cachedEncodingEntries cache parameter epoch).card := by
  classical
  unfold cachedEncodingDigests cachedEncodingEntries
  split <;> rename_i hfinite
  · exact Finset.card_image_le
  · simp

theorem cachedEncodingEntries_card_mono
    (initialCache finalCache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch)
    (hle : initialCache ≤ finalCache) (hfinite : finalCache.toSet.Finite) :
    (cachedEncodingEntries initialCache parameter epoch).card ≤
      (cachedEncodingEntries finalCache parameter epoch).card := by
  classical
  have hsubset : initialCache.toSet ⊆ finalCache.toSet := by
    intro entry hentry
    exact hle hentry
  have hinitialFinite : initialCache.toSet.Finite := hfinite.subset hsubset
  unfold cachedEncodingEntries
  rw [dif_pos hinitialFinite, dif_pos hfinite]
  apply Finset.card_le_card
  intro entry hentry
  rw [Finset.mem_filter] at hentry ⊢
  have hinitialSet : entry ∈ initialCache.toSet := by
    simpa using hentry.1
  have hcache : initialCache entry.1 = some entry.2 :=
    QueryCache.mem_toSet.mp hinitialSet
  have hfinalSet : entry ∈ finalCache.toSet :=
    QueryCache.mem_toSet.mpr (hle hcache)
  exact ⟨by simpa using hfinalSet, hentry.2⟩

theorem cachedEncodingEntryCount_mono
    (initialCache finalCache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch)
    (hle : initialCache ≤ finalCache) :
    cachedEncodingEntryCount initialCache parameter epoch ≤
      cachedEncodingEntryCount finalCache parameter epoch := by
  unfold cachedEncodingEntryCount
  exact_mod_cast Set.encard_mono (by
    intro entry hentry
    exact ⟨hle hentry.1, hentry.2⟩)

theorem QueryCache.enncard_mono
    {initialCache finalCache : QueryCache HashSpec}
    (hle : initialCache ≤ finalCache) :
    QueryCache.enncard initialCache ≤ QueryCache.enncard finalCache := by
  unfold QueryCache.enncard
  exact_mod_cast Set.encard_mono (QueryCache.toSet_mono hle)

theorem cachedEncodingDigests_card_le_enncard (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch) :
    ((cachedEncodingDigests cache parameter epoch).card : ℝ≥0∞) ≤
      QueryCache.enncard cache := by
  classical
  unfold cachedEncodingDigests
  split <;> rename_i hfinite
  · calc
      (((hfinite.toFinset.filter fun entry =>
          encodingInputEpoch? parameter entry.1 = some epoch).image fun entry =>
            truncateHash entry.2).card : ℝ≥0∞) ≤
          ((hfinite.toFinset.filter fun entry =>
            encodingInputEpoch? parameter entry.1 = some epoch).card : ℝ≥0∞) := by
        exact_mod_cast Finset.card_image_le
      _ ≤ (hfinite.toFinset.card : ℝ≥0∞) := by
        exact_mod_cast Finset.card_filter_le _ _
      _ = QueryCache.enncard cache := by
        simp only [QueryCache.enncard, hfinite.encard_eq_coe_toFinset_card,
          ENat.toENNReal_coe]
  · simp

set_option maxRecDepth 10000 in
theorem truncate_mem_cachedEncodingDigests_of_cache_eq_some
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (epoch : Epoch)
    (input : Message × Randomness) (output : HashOutput)
    (hfinite : cache.toSet.Finite)
    (hcache : cache (Concrete.CacheView.encodingInput parameter epoch input) =
      some output) :
    truncateHash output ∈ cachedEncodingDigests cache parameter epoch := by
  classical
  unfold cachedEncodingDigests
  rw [dif_pos hfinite, Finset.mem_image]
  refine ⟨⟨Concrete.CacheView.encodingInput parameter epoch input, output⟩, ?_, rfl⟩
  rw [Finset.mem_filter]
  exact ⟨by simpa using hcache, by simp⟩

/-- A fresh encoding query hits one of the truncated encoding outputs already cached at its epoch with probability at most the cache size divided by `2^128`. -/
theorem Concrete.encodingHash_fresh_hits_cachedDigests_le
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (epoch : Epoch)
    (message : Message) (randomness : Randomness)
    (hfresh : cache (Concrete.CacheView.encodingInput parameter epoch
      (message, randomness)) = none) :
    Pr[fun result : Digest × QueryCache HashSpec =>
      result.1 ∈ cachedEncodingDigests cache parameter epoch |
      (simulateQ randomOracle
        (Concrete.encodingHash parameter epoch message randomness :
          OracleComp HashSpec Digest)).run cache] ≤
      ((cachedEncodingEntries cache parameter epoch).card : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold Concrete.encodingHash Concrete.tweakableHash
  rw [simulateQ_bind, StateT.run_bind]
  let input := Concrete.CacheView.encodingInput parameter epoch (message, randomness)
  change cache input = none at hfresh
  have hsimulate :
      simulateQ randomOracle
          (Concrete.oracleHash input : OracleComp HashSpec HashOutput) =
        randomOracle input := by
    simp [Concrete.oracleHash]
  have hinput : tweakableHashInput parameter (.encoding epoch)
      (Concrete.encodingPayload message randomness) = input := rfl
  rw [hinput, hsimulate, QueryImpl.withCaching_run_none _ hfresh]
  simp only [map_eq_bind_pure_comp, bind_assoc, simulateQ_pure,
    StateT.run_pure]
  simp only [uniformSampleImpl, bind_pure_comp, LawfulApplicative.map_pure,
    Function.comp_apply]
  rw [probEvent_map]
  let targets := cachedEncodingDigests cache parameter epoch
  change Pr[fun output : HashOutput => truncateHash output ∈ targets |
    $ᵗ HashOutput] ≤ _
  have hevent :
      (fun output : HashOutput => truncateHash output ∈ targets) =
      (fun output : HashOutput => ∃ target ∈ targets,
        truncateHash output = target) := by
    funext output
    apply propext
    constructor
    · intro hmem
      exact ⟨truncateHash output, hmem, rfl⟩
    · rintro ⟨target, hmem, heq⟩
      exact heq ▸ hmem
  rw [hevent]
  calc
    Pr[fun output : HashOutput => ∃ target ∈ targets,
          truncateHash output = target |
        $ᵗ HashOutput] ≤
      ∑ target ∈ targets,
        Pr[fun output : HashOutput => truncateHash output = target |
          $ᵗ HashOutput] :=
      probEvent_exists_finset_le_sum targets ($ᵗ HashOutput)
        (fun target output => truncateHash output = target)
    _ = ∑ _target ∈ targets,
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_congr rfl
      intro target _
      exact Rom.uniform_truncate_probability target
    _ = (targets.card : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((cachedEncodingEntries cache parameter epoch).card : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      gcongr
      exact_mod_cast cachedEncodingDigests_card_le_cachedEncodingEntries_card
        cache parameter epoch

/-- For fixed fresh signing randomness, the signing attempt's encoding output collides with a pre-existing same-epoch encoding output with probability at most the cache-size loss. -/
theorem Concrete.signAttempt_freshEncoding_collision_le
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec)
    (hfresh : cache (Concrete.CacheView.encodingInput secretKey.parameter epoch
      (message, randomness)) = none) :
    Pr[fun result : Option Signature × QueryCache HashSpec =>
      ∃ output,
        result.2 (Concrete.CacheView.encodingInput secretKey.parameter epoch
          (message, randomness)) = some output ∧
        truncateHash output ∈
          cachedEncodingDigests cache secretKey.parameter epoch |
      (simulateQ randomOracle
        (Concrete.signAttempt secretKey epoch message randomness :
          OracleComp HashSpec (Option Signature))).run cache] ≤
      ((cachedEncodingEntries cache secretKey.parameter epoch).card : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold Concrete.signAttempt
  rw [simulateQ_bind, StateT.run_bind]
  refine (probEvent_bind_le_probEvent (p := fun prefixResult : Digest × QueryCache HashSpec =>
    prefixResult.1 ∈ cachedEncodingDigests cache secretKey.parameter epoch) ?_).trans ?_
  · intro prefixResult hprefix hmiss
    apply probEvent_eq_zero
    intro result hresult
    rintro ⟨finalOutput, hfinal, htarget⟩
    obtain ⟨prefixOutput, hprefixCached, hdigest⟩ :=
      Concrete.CacheReplay.tweakableHash_query_cached secretKey.parameter
        (.encoding epoch) (Concrete.encodingPayload message randomness)
        cache prefixResult.2 prefixResult.1 hprefix
    have hcacheLe : prefixResult.2 ≤ result.2 := by
      apply Concrete.CacheReplay.randomOracle_cache_le
        (match TargetSum.decodeDigest prefixResult.1 with
          | none => pure none
          | some encoding => some <$>
            Concrete.signWithEncoding secretKey epoch randomness encoding)
        prefixResult.2 result hresult
    have hprefixFinal := hcacheLe hprefixCached
    have houtput : prefixOutput = finalOutput := by
      change result.2 (Concrete.CacheView.encodingInput secretKey.parameter epoch
        (message, randomness)) = some prefixOutput at hprefixFinal
      rw [hfinal] at hprefixFinal
      exact Option.some.inj hprefixFinal.symm
    apply hmiss
    rw [hdigest, houtput]
    exact htarget
  · exact Concrete.encodingHash_fresh_hits_cachedDigests_le cache secretKey.parameter
      epoch message randomness hfresh

/-- Running one signing query samples its 192-bit randomness first, without changing the random-oracle cache, and then performs the fixed-randomness signing attempt. -/
theorem Concrete.sign_run_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) (cache : QueryCache HashSpec) :
    (simulateQ xmssRomImpl
      (Concrete.sign publicKey secretKey epoch message)).run cache =
      (($ᵗ Randomness) >>= fun randomness =>
        (simulateQ randomOracle
          (Concrete.signAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))).run cache) := by
  rw [Concrete.sign_eq, simulateQ_bind, StateT.run_bind]
  have hsampleRun :
      (simulateQ xmssRomImpl
        (liftM Concrete.signingRandomness)).run cache =
        (fun randomness => (randomness, cache)) <$>
          Concrete.signingRandomness := by
    change (simulateQ (unifFwdImpl HashSpec +
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp)))
      (liftM Concrete.signingRandomness)).run cache = _
    exact roSim.run_liftM
      (hashSpec := HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      Concrete.signingRandomness cache
  rw [hsampleRun]
  rw [Concrete.signingRandomness_eq]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr
  intro randomness
  have hroute :
      simulateQ xmssRomImpl
          (liftM (Concrete.signAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))) =
        simulateQ randomOracle
          (Concrete.signAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature)) := by
    change simulateQ (unifFwdImpl HashSpec + randomOracle)
        (liftM (Concrete.signAttempt secretKey epoch message randomness :
          OracleComp HashSpec (Option Signature))) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.signAttempt secretKey epoch message randomness :
        OracleComp HashSpec (Option Signature))
  rw [hroute]

set_option linter.constructorNameAsVariable false in
/-- For one signing query, the chance that its freshly randomized encoding input was already cached before signing is at most the cache size divided by `2^192`. -/
theorem Concrete.sign_encodingInput_initialCache_hit_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) (cache : QueryCache HashSpec) :
    Pr[fun result : Option Signature × QueryCache HashSpec =>
      ∃ signature, result.1 = some signature ∧ ∃ output,
        cache (Concrete.CacheView.encodingInput secretKey.parameter epoch
          (message, signature.randomness)) = some output |
      (simulateQ xmssRomImpl
        (Concrete.sign publicKey secretKey epoch message)).run cache] ≤
      QueryCache.enncard cache *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [Concrete.sign_run_eq]
  refine (probEvent_bind_le_probEvent (p := fun randomness : Randomness =>
    ∃ output, cache (Concrete.CacheView.encodingInput secretKey.parameter epoch
      (message, randomness)) = some output) ?_).trans ?_
  · intro randomness _hrandomness hmiss
    apply probEvent_eq_zero
    intro result hresult
    rintro ⟨signature, hsignature, output, hhit⟩
    have hresult' : (some signature, result.2) ∈ support
        ((simulateQ randomOracle
          (Concrete.signAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))).run cache) := by
      have heq : result = (some signature, result.2) := Prod.ext hsignature rfl
      rw [← heq]
      exact hresult
    have hrandomness := Concrete.signAttempt_support_randomness secretKey epoch message
      randomness cache result.2 signature hresult'
    apply hmiss
    rw [hrandomness] at hhit
    exact ⟨output, hhit⟩
  · exact uniform_signingRandomness_encodingInput_cacheHit_le
      secretKey.parameter epoch message cache

set_option linter.constructorNameAsVariable false in
theorem Concrete.sign_encodingInput_initialCache_hit_bounded_digest_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hcard : QueryCache.enncard cache ≤ (q : ℝ≥0∞)) :
    Pr[fun result : Option Signature × QueryCache HashSpec =>
      ∃ signature, result.1 = some signature ∧ ∃ output,
        cache (Concrete.CacheView.encodingInput secretKey.parameter epoch
          (message, signature.randomness)) = some output |
      (simulateQ xmssRomImpl
        (Concrete.sign publicKey secretKey epoch message)).run cache] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  refine (Concrete.sign_encodingInput_initialCache_hit_le
    publicKey secretKey epoch message cache).trans ?_
  rw [div_eq_mul_inv]
  have hpow : ((2 ^ digestBits : Nat) : ℝ≥0∞) ≤
      ((2 ^ randomnessBits : Nat) : ℝ≥0∞) := by
    exact_mod_cast (by
      norm_num [digestBits, randomnessBits] : 2 ^ digestBits ≤ 2 ^ randomnessBits)
  gcongr

set_option linter.constructorNameAsVariable false in
/-- Excluding a pre-hit on the randomized signing input, one signing query collides with an earlier same-epoch encoding output with only the 128-bit digest loss. -/
theorem Concrete.sign_freshEncoding_collision_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) (cache : QueryCache HashSpec)
    (hfinite : cache.toSet.Finite) :
    Pr[fun result : Option Signature × QueryCache HashSpec =>
      ∃ signature signedOutput oldInput oldOutput,
        result.1 = some signature ∧
        cache (Concrete.CacheView.encodingInput secretKey.parameter epoch
          (message, signature.randomness)) = none ∧
        result.2 (Concrete.CacheView.encodingInput secretKey.parameter epoch
          (message, signature.randomness)) = some signedOutput ∧
        cache (Concrete.CacheView.encodingInput secretKey.parameter epoch oldInput) =
          some oldOutput ∧
        oldInput ≠ (message, signature.randomness) ∧
        truncateHash signedOutput = truncateHash oldOutput |
      (simulateQ xmssRomImpl
        (Concrete.sign publicKey secretKey epoch message)).run cache] ≤
      ((cachedEncodingEntries cache secretKey.parameter epoch).card : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [Concrete.sign_run_eq]
  refine probEvent_bind_le_of_forall_le fun randomness _hrandomness => ?_
  by_cases hfresh : cache (Concrete.CacheView.encodingInput secretKey.parameter epoch
      (message, randomness)) = none
  · refine (probEvent_mono ?_).trans
      (Concrete.signAttempt_freshEncoding_collision_le secretKey epoch message
        randomness cache hfresh)
    intro result hresult hevent
    obtain ⟨signature, signedOutput, oldInput, oldOutput, hsignature,
      _hsignedFresh, hsigned, hold, _hne, hdigest⟩ := hevent
    have hresult' : (some signature, result.2) ∈ support
        ((simulateQ randomOracle
          (Concrete.signAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))).run cache) := by
      have heq : result = (some signature, result.2) := Prod.ext hsignature rfl
      rw [← heq]
      exact hresult
    have hrandomness := Concrete.signAttempt_support_randomness secretKey epoch message
      randomness cache result.2 signature hresult'
    refine ⟨signedOutput, ?_, ?_⟩
    · rw [hrandomness] at hsigned
      exact hsigned
    · rw [hdigest]
      exact truncate_mem_cachedEncodingDigests_of_cache_eq_some cache
        secretKey.parameter epoch oldInput oldOutput hfinite hold
  · refine le_of_eq_of_le ?_ zero_le
    apply probEvent_eq_zero
    intro result hresult hevent
    obtain ⟨signature, _signedOutput, _oldInput, _oldOutput, hsignature,
      hsignedFresh, _hsigned, _hold, _hne, _hdigest⟩ := hevent
    have hresult' : (some signature, result.2) ∈ support
        ((simulateQ randomOracle
          (Concrete.signAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))).run cache) := by
      have heq : result = (some signature, result.2) := Prod.ext hsignature rfl
      rw [← heq]
      exact hresult
    have hrandomness := Concrete.signAttempt_support_randomness secretKey epoch message
      randomness cache result.2 signature hresult'
    apply hfresh
    rw [← hrandomness]
    exact hsignedFresh

set_option linter.constructorNameAsVariable false in
/-- One signing query either reuses an encoding input guessed before its 192-bit randomness was sampled, or its fresh 128-bit encoding output collides with an earlier same-epoch encoding output. -/
theorem Concrete.sign_preexistingEncoding_collision_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) (cache : QueryCache HashSpec)
    (hfinite : cache.toSet.Finite) :
    Pr[fun result : Option Signature × QueryCache HashSpec =>
      ∃ signature signedOutput oldInput oldOutput,
        result.1 = some signature ∧
        result.2 (Concrete.CacheView.encodingInput secretKey.parameter epoch
          (message, signature.randomness)) = some signedOutput ∧
        cache (Concrete.CacheView.encodingInput secretKey.parameter epoch oldInput) =
          some oldOutput ∧
        oldInput ≠ (message, signature.randomness) ∧
        truncateHash signedOutput = truncateHash oldOutput |
      (simulateQ xmssRomImpl
        (Concrete.sign publicKey secretKey epoch message)).run cache] ≤
      QueryCache.enncard cache *
          ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ +
        ((cachedEncodingEntries cache secretKey.parameter epoch).card : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [Concrete.sign_run_eq]
  refine (probEvent_bind_le_probEvent_add
    (ε := ((cachedEncodingEntries cache secretKey.parameter epoch).card : ℝ≥0∞) *
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
    (p := fun randomness : Randomness =>
      ∃ output, cache (Concrete.CacheView.encodingInput secretKey.parameter epoch
        (message, randomness)) = some output) ?_).trans ?_
  · intro randomness _hrandomness hmiss
    have hfresh : cache (Concrete.CacheView.encodingInput secretKey.parameter epoch
        (message, randomness)) = none := by
      apply Option.eq_none_iff_forall_ne_some.mpr
      intro output houtput
      exact hmiss ⟨output, houtput⟩
    refine (probEvent_mono ?_).trans
      (Concrete.signAttempt_freshEncoding_collision_le secretKey epoch message
        randomness cache hfresh)
    intro result hresult hevent
    obtain ⟨signature, signedOutput, oldInput, oldOutput, hsignature,
      hsigned, hold, _hne, hdigest⟩ := hevent
    have hresult' : (some signature, result.2) ∈ support
        ((simulateQ randomOracle
          (Concrete.signAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))).run cache) := by
      have heq : result = (some signature, result.2) := Prod.ext hsignature rfl
      rw [← heq]
      exact hresult
    have hrandomness := Concrete.signAttempt_support_randomness secretKey epoch message
      randomness cache result.2 signature hresult'
    refine ⟨signedOutput, ?_, ?_⟩
    · rw [hrandomness] at hsigned
      exact hsigned
    · rw [hdigest]
      exact truncate_mem_cachedEncodingDigests_of_cache_eq_some cache
        secretKey.parameter epoch oldInput oldOutput hfinite hold
  · gcongr
    exact uniform_signingRandomness_encodingInput_cacheHit_le
      secretKey.parameter epoch message cache

end XmssSecurity
