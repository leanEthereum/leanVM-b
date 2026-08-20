import XmssSecurity.Proof.EncodingTargetMap
import XmssSecurity.Proof.SigningRandomnessUniformity
import Mathlib.Data.Set.Card.Arithmetic

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

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

/-- Running one signing query samples its 192-bit randomness first, without changing the random-oracle cache, and then performs the fixed-randomness signing attempt. -/
theorem Concrete.sign_run_eq
    (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) (cache : QueryCache HashSpec) :
    (simulateQ romImpl
      (Concrete.sign secretKey epoch message)).run cache =
      (($ᵗ Randomness) >>= fun randomness =>
        (simulateQ randomOracle
          (Concrete.signAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))).run cache) := by
  rw [Concrete.sign_eq, simulateQ_bind, StateT.run_bind]
  have hsampleRun :
      (simulateQ romImpl
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
      simulateQ romImpl
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

end XmssSecurity
