import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.EncodingTarget

/-!
# Amortized charge for encoding collisions

The cache-local encoding target at one one-time position is unique. Inputs cached at that encoding
tweak before the target is pinned pay one unit each for the answer that pins it. Once pinned, a
fresh encoding query has only that one target.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

structure EncodingPosition where
  lay : Layer
  tree : TreeIndex
  leafIdx : LeafIndex
  deriving DecidableEq, Fintype

def EncodingPosition.domain (position : EncodingPosition) : HashDomain :=
  .encoding position.lay position.tree position.leafIdx

def AtEncodingPosition (parameter : PublicParameter) (input : HashInput)
    (position : EncodingPosition) : Prop :=
  ∃ payload, input = tweakableHashInput parameter position.domain payload

theorem atEncodingPosition_unique {parameter : PublicParameter} {input : HashInput}
    {left right : EncodingPosition} (hleft : AtEncodingPosition parameter input left)
    (hright : AtEncodingPosition parameter input right) : left = right := by
  obtain ⟨leftPayload, hleft⟩ := hleft
  obtain ⟨rightPayload, hright⟩ := hright
  have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial)
    (hleft.symm.trans hright)).1
  obtain ⟨leftLay, leftTree, leftLeaf⟩ := left
  obtain ⟨rightLay, rightTree, rightLeaf⟩ := right
  simp only [EncodingPosition.domain, HashDomain.encoding.injEq] at hdomain
  obtain ⟨rfl, rfl, rfl⟩ := hdomain
  rfl

theorem AtEncodingPosition.not_atPosition {parameter : PublicParameter} {input : HashInput}
    {encodingPosition : EncodingPosition} (hencoding : AtEncodingPosition parameter input encodingPosition)
    (position : Position) : ¬ AtPosition parameter input position := by
  rintro ⟨structuralPayload, hstructural⟩
  obtain ⟨encodingPayload, hencodingInput⟩ := hencoding
  have hdomain := (tweakableHashInput_injective parameter (by trivial)
    position.domain_inRange (hencodingInput.symm.trans hstructural)).1
  cases position <;> simp [EncodingPosition.domain, Position.domain] at hdomain

def encodingCachedAt (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (position : EncodingPosition) : Set HashInput :=
  {input | cache input ≠ none ∧ AtEncodingPosition parameter input position}

@[simp] theorem slotDigest_zero_encodingInput (parameter : PublicParameter)
    (position : EncodingPosition) (message : Digest) (counter : Counter) :
    slotDigest 0 (tweakableHashInput parameter position.domain
      (digestBytes message ++ counterBytes counter)) = message := by
  rw [slotDigest, payloadOf_tweakableHashInput]
  simp only [Nat.mul_zero, List.drop_zero]
  rw [← digestBytes_length message, List.take_left, digestOfBytes_digestBytes]

theorem encodingCachedAt_finite {parameter : PublicParameter} {cache : QueryCache HashSpec}
    (hfinite : Finite cache) (position : EncodingPosition) :
    (encodingCachedAt parameter cache position).Finite :=
  hfinite.subset fun _ hinput => hinput.1

noncomputable def encodingMessageTargets (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (position : EncodingPosition) : Finset Digest :=
  open Classical in
  (encodingCachedAt_finite (parameter := parameter) (cache := cache) hfinite position).toFinset.image
    (slotDigest 0)

theorem slotDigest_mem_encodingMessageTargets {parameter : PublicParameter}
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {position : EncodingPosition}
    {input : HashInput} (hcached : cache input ≠ none)
    (hposition : AtEncodingPosition parameter input position) :
    slotDigest 0 input ∈ encodingMessageTargets parameter cache hfinite position := by
  rw [encodingMessageTargets, Finset.mem_image]
  refine ⟨input, ?_, rfl⟩
  rw [Set.Finite.mem_toFinset]
  exact ⟨hcached, hposition⟩

theorem encodingMessageTargets_card_le {parameter : PublicParameter}
    {cache : QueryCache HashSpec} (hfinite : Finite cache) (position : EncodingPosition) :
    (encodingMessageTargets parameter cache hfinite position).card ≤
      (encodingCachedAt parameter cache position).ncard := by
  rw [encodingMessageTargets, Set.ncard_eq_toFinset_card _
    (encodingCachedAt_finite (parameter := parameter) (cache := cache) hfinite position)]
  exact Finset.card_image_le

noncomputable def encodingAnswerTargets (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (position : EncodingPosition) : Finset Digest :=
  open Classical in
  (encodingCachedAt_finite (parameter := parameter) (cache := cache) hfinite position).toFinset.image
    fun input => truncateHash (fromCache cache input)

theorem cachedAnswer_mem_encodingAnswerTargets {parameter : PublicParameter}
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {position : EncodingPosition}
    {input : HashInput} {answer : HashOutput} (hcached : cache input = some answer)
    (hposition : AtEncodingPosition parameter input position) :
    truncateHash answer ∈ encodingAnswerTargets parameter cache hfinite position := by
  rw [encodingAnswerTargets, Finset.mem_image]
  refine ⟨input, ?_, ?_⟩
  · rw [Set.Finite.mem_toFinset]
    exact ⟨by simp [hcached], hposition⟩
  · simp [fromCache, hcached]

noncomputable def encodingValidAnswerTargets (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (position : EncodingPosition) : Finset Digest :=
  (encodingAnswerTargets parameter cache hfinite position).filter TargetSum.ValidDigest

theorem cachedValidAnswer_mem_encodingValidAnswerTargets {parameter : PublicParameter}
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {position : EncodingPosition}
    {input : HashInput} {answer : HashOutput} (hcached : cache input = some answer)
    (hposition : AtEncodingPosition parameter input position)
    (hvalid : TargetSum.ValidDigest (truncateHash answer)) :
    truncateHash answer ∈ encodingValidAnswerTargets parameter cache hfinite position := by
  rw [encodingValidAnswerTargets, Finset.mem_filter]
  exact ⟨cachedAnswer_mem_encodingAnswerTargets hfinite hcached hposition, hvalid⟩

def HasEncodingTarget (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (position : EncodingPosition) : Prop :=
  ∃ payload, CachedSignedEncodingPayloadAt cache secretKey position.lay position.tree
    position.leafIdx payload

theorem HasEncodingTarget.mono {cache cache' : QueryCache HashSpec} {secretKey : SecretKey}
    {position : EncodingPosition} (hle : cache ≤ cache')
    (htarget : HasEncodingTarget cache secretKey position) :
    HasEncodingTarget cache' secretKey position := by
  obtain ⟨payload, hpayload⟩ := htarget
  exact ⟨payload, hpayload.mono hle⟩

theorem encodingCachedAt_cacheQuery_of_not_atPosition
    {parameter : PublicParameter} {cache : QueryCache HashSpec} {input : HashInput}
    {answer : HashOutput} {position : EncodingPosition}
    (hposition : ¬ AtEncodingPosition parameter input position) :
    encodingCachedAt parameter (cache.cacheQuery input answer) position =
      encodingCachedAt parameter cache position := by
  ext candidate
  by_cases heq : candidate = input
  · subst candidate
    simp only [encodingCachedAt, Set.mem_setOf_eq, QueryCache.cacheQuery_self]
    exact ⟨fun h => absurd h.2 hposition, fun h => absurd h.2 hposition⟩
  · simp only [encodingCachedAt, Set.mem_setOf_eq,
      QueryCache.cacheQuery_of_ne _ _ heq]

theorem encodingCachedAt_cacheQuery_self {parameter : PublicParameter}
    {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition} (hposition : AtEncodingPosition parameter input position) :
    encodingCachedAt parameter (cache.cacheQuery input answer) position =
      insert input (encodingCachedAt parameter cache position) := by
  ext candidate
  by_cases heq : candidate = input
  · subst candidate
    simp only [encodingCachedAt, Set.mem_setOf_eq, QueryCache.cacheQuery_self,
      Set.mem_insert_iff, true_or, ne_eq, reduceCtorEq, not_false_eq_true, hposition, and_self]
  · simp only [encodingCachedAt, Set.mem_setOf_eq,
      QueryCache.cacheQuery_of_ne _ _ heq, Set.mem_insert_iff, heq, false_or]

end SphincsSecurity.Concrete
