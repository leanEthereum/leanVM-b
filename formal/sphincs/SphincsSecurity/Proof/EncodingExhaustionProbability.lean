import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.EncodingSelectionCache

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 1000
set_option exponentiation.threshold 512

noncomputable def encodingInvalidProbability : ℝ≥0∞ :=
  Pr[fun output : HashOutput => ¬TargetSum.ValidDigest (truncateHash output) | ($ᵗ HashOutput : ProbComp HashOutput)]

noncomputable def encodingExhaustionWeight (cache : QueryCache HashSpec) (input : HashInput) : ℝ≥0∞ :=
  match cache input with
  | none => encodingInvalidProbability
  | some output => if TargetSum.ValidDigest (truncateHash output) then 0 else 1

noncomputable def encodingExhaustionPotential (inputs : Finset HashInput) (cache : QueryCache HashSpec) : ℝ≥0∞ :=
  ∏ input ∈ inputs, encodingExhaustionWeight cache input

def EncodingInputsExhausted (inputs : Finset HashInput) (cache : QueryCache HashSpec) : Prop :=
  ∀ input ∈ inputs, ∃ output, cache input = some output ∧ ¬TargetSum.ValidDigest (truncateHash output)

theorem encodingExhaustionPotential_empty_cache (inputs : Finset HashInput) :
    encodingExhaustionPotential inputs ∅ = encodingInvalidProbability ^ inputs.card := by
  simp [encodingExhaustionPotential, encodingExhaustionWeight]

theorem encodingExhaustionPotential_eq_one_of_exhausted
    (inputs : Finset HashInput) (cache : QueryCache HashSpec) (hexhausted : EncodingInputsExhausted inputs cache) :
    encodingExhaustionPotential inputs cache = 1 := by
  apply Finset.prod_eq_one
  intro input hinput
  obtain ⟨output, houtput, hinvalid⟩ := hexhausted input hinput
  simp [encodingExhaustionWeight, houtput, hinvalid]

theorem encodingExhaustionPotential_cacheQuery_of_not_mem
    (inputs : Finset HashInput) (cache : QueryCache HashSpec) (input : HashInput) (output : HashOutput)
    (hnot : input ∉ inputs) :
    encodingExhaustionPotential inputs (cache.cacheQuery input output) = encodingExhaustionPotential inputs cache := by
  apply Finset.prod_congr rfl
  intro other hother
  have hne : other ≠ input := fun heq => hnot (heq ▸ hother)
  simp [encodingExhaustionWeight, QueryCache.cacheQuery_of_ne _ _ hne]

theorem encodingExhaustionPotential_cacheQuery_of_mem
    (inputs : Finset HashInput) (cache : QueryCache HashSpec) (input : HashInput) (output : HashOutput)
    (hmem : input ∈ inputs) :
    encodingExhaustionPotential inputs (cache.cacheQuery input output) =
      (if TargetSum.ValidDigest (truncateHash output) then 0 else 1) *
        encodingExhaustionPotential (inputs.erase input) cache := by
  rw [encodingExhaustionPotential, ← Finset.mul_prod_erase inputs _ hmem]
  change encodingExhaustionWeight (cache.cacheQuery input output) input *
      encodingExhaustionPotential (inputs.erase input) (cache.cacheQuery input output) = _
  rw [encodingExhaustionPotential_cacheQuery_of_not_mem _ cache input output (by simp)]
  simp [encodingExhaustionWeight]

theorem expected_encodingExhaustionPotential_fresh
    (inputs : Finset HashInput) (cache : QueryCache HashSpec) (input : HashInput)
    (hfresh : cache input = none) :
    (∑' output : HashOutput, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      encodingExhaustionPotential inputs (cache.cacheQuery input output)) = encodingExhaustionPotential inputs cache := by
  by_cases hmem : input ∈ inputs
  · simp_rw [encodingExhaustionPotential_cacheQuery_of_mem inputs cache input _ hmem, ← mul_assoc]
    rw [ENNReal.tsum_mul_right]
    have hprob : (∑' output : HashOutput, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if TargetSum.ValidDigest (truncateHash output) then 0 else 1)) = encodingInvalidProbability := by
      rw [encodingInvalidProbability, probEvent_eq_tsum_ite]
      apply tsum_congr
      intro output
      by_cases hvalid : TargetSum.ValidDigest (truncateHash output) <;> simp [hvalid]
    rw [hprob]
    change encodingInvalidProbability * (∏ other ∈ inputs.erase input, encodingExhaustionWeight cache other) =
      ∏ other ∈ inputs, encodingExhaustionWeight cache other
    rw [← Finset.mul_prod_erase inputs _ hmem]
    simp only [encodingExhaustionWeight, hfresh]
  · simp_rw [encodingExhaustionPotential_cacheQuery_of_not_mem inputs cache input _ hmem]
    rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

theorem expected_encodingExhaustionPotential_query
    (inputs : Finset HashInput) (cache : QueryCache HashSpec) (query : OracleWorld.Domain) :
    (∑' result, Pr[= result | (romImpl query).run cache] * encodingExhaustionPotential inputs result.2) =
      encodingExhaustionPotential inputs cache := by
  cases query with
  | inl n =>
      have hquery : (romImpl (.inl n)).run cache =
          (fun answer => (answer, cache)) <$> (liftM (unifSpec.query n) : ProbComp _) := rfl
      rw [hquery]
      change (∑' result : Fin (n + 1) × QueryCache HashSpec,
        Pr[= result | (fun answer : Fin (n + 1) => (answer, cache)) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))] * encodingExhaustionPotential inputs result.2) = _
      rw [tsum_probOutput_map_mul]
      dsimp only
      rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
  | inr input =>
      change (∑' result, Pr[= result | (randomOracle input).run cache] * encodingExhaustionPotential inputs result.2) = _
      by_cases hfresh : cache input = none
      · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
        exact expected_encodingExhaustionPotential_fresh inputs cache input hfresh
      · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hfresh
        rw [randomOracle, QueryImpl.withCaching_run_some _ houtput]
        simp

theorem expected_encodingExhaustionPotential_run
    (inputs : Finset HashInput) (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run cache] * encodingExhaustionPotential inputs result.2) =
      encodingExhaustionPotential inputs cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
      simp_rw [ih]
      exact expected_encodingExhaustionPotential_query inputs cache query

theorem probEvent_encodingInputsExhausted_le
    (inputs : Finset HashInput) (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    Pr[fun result => EncodingInputsExhausted inputs result.2 | (simulateQ romImpl computation).run cache] ≤
      encodingExhaustionPotential inputs cache := by
  rw [← expected_encodingExhaustionPotential_run inputs computation cache, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hexhausted : EncodingInputsExhausted inputs result.2
  · simp [hexhausted, encodingExhaustionPotential_eq_one_of_exhausted inputs result.2 hexhausted]
  · simp [hexhausted]

theorem probEvent_encodingInputsExhausted_empty_le_pow
    (inputs : Finset HashInput) (computation : OracleComp OracleWorld α) :
    Pr[fun result => EncodingInputsExhausted inputs result.2 | (simulateQ romImpl computation).run ∅] ≤
      (1 - (TargetSum.validDigests.card : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞)) ^ inputs.card := by
  have hbound := probEvent_encodingInputsExhausted_le inputs computation ∅
  rw [encodingExhaustionPotential_empty_cache, encodingInvalidProbability, probEvent_uniform_encoding_invalid] at hbound
  exact hbound

noncomputable def encodingRetryInputs (parameter : PublicParameter) (position : EncodingPosition) (message : Digest) :
    Finset HashInput :=
  Finset.univ.image fun counter : Fin encodingAttemptLimit => encodingRetryInput parameter position message counter.val

theorem encodingRetryInputs_card (parameter : PublicParameter) (position : EncodingPosition) (message : Digest) :
    (encodingRetryInputs parameter position message).card = encodingAttemptLimit := by
  have hinjective : Function.Injective (fun counter : Fin encodingAttemptLimit =>
      encodingRetryInput parameter position message counter.val) := by
    intro left right heq
    exact Fin.ext (encodingRetryInput_injective_of_lt left.isLt right.isLt heq)
  rw [encodingRetryInputs, Finset.card_image_of_injective _ hinjective, Finset.card_univ, Fintype.card_fin]

def AnyEncodingInputsExhausted (cache : QueryCache HashSpec) : Prop :=
  ∃ parameter position message, EncodingInputsExhausted (encodingRetryInputs parameter position message) cache

theorem probEvent_anyEncodingInputsExhausted_le
    (computation : OracleComp OracleWorld α) :
    Pr[fun result => AnyEncodingInputsExhausted result.2 | (simulateQ romImpl computation).run ∅] ≤
      ((3 * 2 ^ 294 : Nat) : ℝ≥0∞) *
        (1 - (TargetSum.validDigests.card : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞)) ^ encodingAttemptLimit := by
  let family := PublicParameter × EncodingPosition × Digest
  let run := (simulateQ romImpl computation).run ∅
  let event := fun choice : family => fun result : α × QueryCache HashSpec =>
    EncodingInputsExhausted (encodingRetryInputs choice.1 choice.2.1 choice.2.2) result.2
  have hunion := probEvent_exists_finset_le_sum (Finset.univ : Finset family) run event
  have hleft : (fun result : α × QueryCache HashSpec => ∃ choice ∈ (Finset.univ : Finset family), event choice result) =
      (fun result => AnyEncodingInputsExhausted result.2) := by
    funext result
    apply propext
    simp only [Finset.mem_univ, true_and, event, AnyEncodingInputsExhausted]
    constructor
    · rintro ⟨choice, hchoice⟩
      exact ⟨choice.1, choice.2.1, choice.2.2, hchoice⟩
    · rintro ⟨parameter, position, message, hchoice⟩
      exact ⟨(parameter, position, message), hchoice⟩
  rw [hleft] at hunion
  apply hunion.trans
  calc
    _ ≤ ∑ _choice : family,
        (1 - (TargetSum.validDigests.card : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞)) ^ encodingAttemptLimit := by
      apply Finset.sum_le_sum
      intro choice _
      have hbound := probEvent_encodingInputsExhausted_empty_le_pow
        (encodingRetryInputs choice.1 choice.2.1 choice.2.2) computation
      rw [encodingRetryInputs_card] at hbound
      exact hbound
    _ = _ := by
      have hcard : Fintype.card family = 3 * 2 ^ 294 := by
        have hposition : Fintype.card EncodingPosition = Fintype.card (Layer × TreeIndex × LeafIndex) :=
          Fintype.card_congr
            { toFun := fun position => (position.lay, position.tree, position.leafIdx)
              invFun := fun fields => ⟨fields.1, fields.2.1, fields.2.2⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
        change Fintype.card (PublicParameter × EncodingPosition × Digest) = _
        rw [Fintype.card_prod, Fintype.card_prod, hposition]
        norm_num [publicParameterBits, digestBits, numLayers, totalHeight, maxLayerHeight]
      rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]

theorem otsSignFrom_none_cached_invalid
    (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) (attempts counter : Nat)
    (hagrees : cache.AgreesWithFn f)
    (hrun : CachedRun cache f (otsSignFrom parameter lay tree leafIdx secret message attempts counter))
    (hfailed : evalWithAnswerFn f (otsSignFrom parameter lay tree leafIdx secret message attempts counter) = none)
    (candidate : Nat) (hlower : counter ≤ candidate) (hupper : candidate < counter + attempts) :
    ∃ output, cache (encodingRetryInput parameter ⟨lay, tree, leafIdx⟩ message candidate) = some output ∧
      ¬TargetSum.ValidDigest (truncateHash output) := by
  induction attempts generalizing counter with
  | zero => omega
  | succ attempts ih =>
      rw [otsSignFrom, evalWithAnswerFn_bind] at hfailed
      rw [otsSignFrom] at hrun
      cases hencode : evalWithAnswerFn f (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter)) with
      | some encoding =>
          simp [hencode] at hfailed
      | none =>
          simp only [hencode] at hfailed
          by_cases heq : candidate = counter
          · subst candidate
            obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (CachedRun.encode_cached hrun.bind_left)
            refine ⟨output, houtput, ?_⟩
            intro hvalid
            have hvalid' : TargetSum.ValidDigest (truncateHash (f (tweakableHashInput parameter
                (.encoding lay tree leafIdx) (digestBytes message ++ counterBytes (BitVec.ofNat counterBits counter))))) := by
              rw [hagrees houtput]
              exact hvalid
            exact ((eval_encode_ne_none_iff_validDigest f parameter lay tree leafIdx message
              (BitVec.ofNat counterBits counter)).mpr hvalid') hencode
          · apply ih (counter + 1) _ hfailed (by omega) (by omega)
            have htail := hrun.bind_right
            simpa only [hencode] using htail

theorem encodingInputsExhausted_of_otsSign_none
    (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest)
    (hagrees : cache.AgreesWithFn f)
    (hrun : CachedRun cache f (otsSign parameter lay tree leafIdx secret message))
    (hfailed : evalWithAnswerFn f (otsSign parameter lay tree leafIdx secret message) = none) :
    EncodingInputsExhausted (encodingRetryInputs parameter ⟨lay, tree, leafIdx⟩ message) cache := by
  intro input hinput
  obtain ⟨candidate, _hmem, rfl⟩ := Finset.mem_image.mp hinput
  exact otsSignFrom_none_cached_invalid f cache parameter lay tree leafIdx secret message encodingAttemptLimit 0
    hagrees hrun hfailed candidate.val (Nat.zero_le _) (by simp)

def CachedOtsEncodingFailure (cache : QueryCache HashSpec) : Prop :=
  ∃ (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (position : EncodingPosition)
    (secret : ChainIndex → Digest) (message : Digest),
    cache.AgreesWithFn f ∧ CachedRun cache f (otsSign parameter position.lay position.tree position.leafIdx secret message) ∧
      evalWithAnswerFn f (otsSign parameter position.lay position.tree position.leafIdx secret message) = none

theorem anyEncodingInputsExhausted_of_cachedOtsEncodingFailure
    (cache : QueryCache HashSpec) (hfailed : CachedOtsEncodingFailure cache) : AnyEncodingInputsExhausted cache := by
  obtain ⟨f, parameter, position, secret, message, hagrees, hrun, hfailed⟩ := hfailed
  exact ⟨parameter, position, message, encodingInputsExhausted_of_otsSign_none f cache parameter position.lay position.tree
    position.leafIdx secret message hagrees hrun hfailed⟩

theorem EncodingInputsExhausted.mono
    {inputs : Finset HashInput} {before after : QueryCache HashSpec}
    (hexhausted : EncodingInputsExhausted inputs before) (hle : before ≤ after) :
    EncodingInputsExhausted inputs after := by
  intro input hinput
  obtain ⟨output, houtput, hinvalid⟩ := hexhausted input hinput
  exact ⟨output, hle houtput, hinvalid⟩

theorem AnyEncodingInputsExhausted.mono
    {before after : QueryCache HashSpec} (hexhausted : AnyEncodingInputsExhausted before) (hle : before ≤ after) :
    AnyEncodingInputsExhausted after := by
  obtain ⟨parameter, position, message, hexhausted⟩ := hexhausted
  exact ⟨parameter, position, message, hexhausted.mono hle⟩

end SphincsSecurity.Concrete
