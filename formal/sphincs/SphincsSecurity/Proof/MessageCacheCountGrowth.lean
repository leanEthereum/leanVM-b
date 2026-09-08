import SphincsSecurity.Proof.MessageInputMiss

namespace SphincsSecurity

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

private theorem filtered_cacheQuery_count (cache : QueryCache HashSpec) (input : HashInput) (output : HashOutput)
    (hfresh : cache input = none) (P : Sigma HashSpec.Range → Prop) :
    (({entry ∈ (cache.cacheQuery input output).toSet | P entry}.encard : ENat) : ENNReal) =
      (({entry ∈ cache.toSet | P entry}.encard : ENat) : ENNReal) + if P ⟨input, output⟩ then 1 else 0 := by
  have hset : (cache.cacheQuery input output).toSet = insert ⟨input, output⟩ cache.toSet := by
    apply Set.Subset.antisymm (QueryCache.toSet_cacheQuery_subset_insert cache input output)
    rintro entry (heq | hold)
    · subst entry
      exact QueryCache.cacheQuery_self _ _ _
    · exact QueryCache.toSet_mono (QueryCache.le_cacheQuery cache hfresh) hold
  change ((((cache.cacheQuery input output).toSet ∩ {entry | P entry}).encard : ENat) : ENNReal) = _
  rw [hset]
  by_cases hp : P ⟨input, output⟩
  · rw [Set.insert_inter_of_mem (s := cache.toSet) (t := {entry | P entry}) hp, if_pos hp, Set.encard_insert_of_notMem (by
      intro h
      have hc := h.1
      change cache input = some output at hc
      simp only [hfresh, reduceCtorEq] at hc)]
    simp only [ENat.toENNReal_add, ENat.toENNReal_one]
    rfl
  · rw [Set.insert_inter_of_notMem (s := cache.toSet) (t := {entry | P entry}) hp, if_neg hp, add_zero]
    rfl

theorem cachedMessageEntryCount_cacheQuery_eq (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (input : HashInput) (output : HashOutput) (hfresh : cache input = none) :
    cachedMessageEntryCount (cache.cacheQuery input output) parameter root message =
      cachedMessageEntryCount cache parameter root message +
        if ∃ randomness, input = tweakableHashInput parameter .message (Concrete.messageDigestPayload root message randomness) then 1 else 0 := by
  have h := filtered_cacheQuery_count cache input output hfresh (fun entry =>
    ∃ randomness, entry.1 = tweakableHashInput parameter .message (Concrete.messageDigestPayload root message randomness))
  dsimp only at h
  unfold cachedMessageEntryCount cachedMessageInputSet
  convert h using 1
  split_ifs <;> rfl

theorem cachedMessageEntryCountWhere_cacheQuery_eq (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (input : HashInput) (output : HashOutput) (hfresh : cache input = none)
    (P : Concrete.FewTimeView → Prop) :
    cachedMessageEntryCountWhere (cache.cacheQuery input output) parameter root message P =
      cachedMessageEntryCountWhere cache parameter root message P +
        if (∃ randomness, input = tweakableHashInput parameter .message (Concrete.messageDigestPayload root message randomness)) ∧
          Concrete.signAttemptResultOfOutput output ≠ none ∧ P (Concrete.hashOutputFewTimeView output) then 1 else 0 := by
  have h := filtered_cacheQuery_count cache input output hfresh (fun entry =>
      (∃ randomness, entry.1 = tweakableHashInput parameter .message (Concrete.messageDigestPayload root message randomness)) ∧
        Concrete.signAttemptResultOfOutput entry.2 ≠ none ∧ P (Concrete.hashOutputFewTimeView entry.2))
  have hset (current : QueryCache HashSpec) : cachedMessageInputSetWhere current parameter root message P =
      {entry ∈ current.toSet | (∃ randomness, entry.1 = tweakableHashInput parameter .message
        (Concrete.messageDigestPayload root message randomness)) ∧
          Concrete.signAttemptResultOfOutput entry.2 ≠ none ∧ P (Concrete.hashOutputFewTimeView entry.2)} := by
    ext entry
    simp only [cachedMessageInputSetWhere, cachedMessageInputSet, Set.mem_setOf_eq, and_assoc]
  unfold cachedMessageEntryCountWhere
  rw [hset, hset]
  dsimp only at h
  convert h using 1
  split_ifs <;> rfl

theorem cachedMessageEntryCount_mono (parameter : PublicParameter) (root : Digest) (message : Message)
    {before after : QueryCache HashSpec} (hcache : before ≤ after) :
    cachedMessageEntryCount before parameter root message ≤ cachedMessageEntryCount after parameter root message := by
  apply ENat.toENNReal_mono (Set.encard_le_encard ?_)
  intro entry hentry
  exact ⟨QueryCache.toSet_mono hcache hentry.1, hentry.2⟩

theorem cachedMessageEntryCount_cacheQuery_le (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (input : HashInput) (output : HashOutput) :
    cachedMessageEntryCount (cache.cacheQuery input output) parameter root message ≤
      cachedMessageEntryCount cache parameter root message + 1 := by
  have hsubset : cachedMessageInputSet (cache.cacheQuery input output) parameter root message ⊆
      insert ⟨input, output⟩ (cachedMessageInputSet cache parameter root message) := by
    intro entry hentry
    rcases QueryCache.toSet_cacheQuery_subset_insert cache input output hentry.1 with heq | hold
    · exact Or.inl heq
    · exact Or.inr ⟨hold, hentry.2⟩
  exact (ENat.toENNReal_mono (Set.encard_le_encard hsubset)).trans
    (by simpa only [cachedMessageEntryCount, ENat.toENNReal_add, ENat.toENNReal_one] using
      ENat.toENNReal_mono (Set.encard_insert_le (cachedMessageInputSet cache parameter root message) ⟨input, output⟩))

theorem randomOracle_cachedMessageEntryCount_le (parameter : PublicParameter) (root : Digest) (message : Message)
    (input : HashInput) (cache : QueryCache HashSpec) (result : HashOutput × QueryCache HashSpec)
    (hr : result ∈ support ((randomOracle input).run cache)) :
    cachedMessageEntryCount result.2 parameter root message ≤ cachedMessageEntryCount cache parameter root message + 1 := by
  cases hc : cache input with
  | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hc, support_map] at hr
      obtain ⟨output, _, rfl⟩ := hr
      exact cachedMessageEntryCount_cacheQuery_le parameter root message cache input output
  | some output =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff] at hr
      subst result
      exact le_self_add

namespace Concrete

theorem signAttempt_cachedMessageEntryCount_le (key : SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec) (result : Option (Index × (DigestTree → FtsLeaf)) × QueryCache HashSpec)
    (hr : result ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _) (signAttempt key message randomness)).run cache)) :
    cachedMessageEntryCount result.2 key.parameter key.root message ≤ cachedMessageEntryCount cache key.parameter key.root message + 1 := by
  rw [simulateQ_signAttempt_run_eq, mem_support_bind_iff] at hr
  obtain ⟨oracleResult, horacle, hpure⟩ := hr
  simp only [mem_support_pure_iff] at hpure
  subst result
  exact randomOracle_cachedMessageEntryCount_le key.parameter key.root message
    (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) cache oracleResult horacle

end Concrete
end SphincsSecurity
