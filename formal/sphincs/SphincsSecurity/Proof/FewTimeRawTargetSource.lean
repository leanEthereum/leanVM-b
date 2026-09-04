import SphincsSecurity.Proof.FewTimeRawTargetExtraction

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem rawTargetCandidateViews_length_le_directIntervalCount
    (intervals : List AdversaryCacheEntry) :
    (rawTargetCandidateViews intervals).length ≤ directIntervalCount intervals := by
  induction intervals with
  | nil => exact le_rfl
  | cons entry rest ih =>
      rcases entry with ⟨input, output, before, after⟩
      cases input with
      | inl worldInput =>
          cases worldInput with
          | inl uniformInput =>
              simpa [rawTargetCandidateViews, rawTargetCandidateView?, directIntervalCount,
                isDirectHashQuery] using ih
          | inr hashInput =>
              by_cases hfresh : before hashInput = none <;>
                simpa [rawTargetCandidateViews, rawTargetCandidateView?, directIntervalCount,
                  isDirectHashQuery, hfresh] using (show (rawTargetCandidateViews rest).length +
                    (if before hashInput = none then 1 else 0) ≤ directIntervalCount rest + 1 by
                      split_ifs; omega)
      | inr request =>
          simpa [rawTargetCandidateViews, rawTargetCandidateView?, directIntervalCount,
            isDirectHashQuery] using ih

theorem directIntervalCount_eq_directHashQueries_length (intervals : List AdversaryCacheEntry) :
    directIntervalCount intervals =
      (directHashQueries (intervals.map AdversaryCacheEntry.queryEntry)).length := by
  induction intervals with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨input, output, before, after⟩
      cases input with
      | inl worldInput =>
          cases worldInput <;>
            simpa [directIntervalCount, directHashQueries, AdversaryCacheEntry.queryEntry,
              isDirectHashQuery] using ih
      | inr request =>
          simpa [directIntervalCount, directHashQueries, AdversaryCacheEntry.queryEntry,
            isDirectHashQuery] using ih

theorem FullAdversaryTrace.directIntervalCount_eq_hashQueries_length
    (trace : FullAdversaryTrace) (hconsistent : trace.Consistent) :
    directIntervalCount trace.intervals = trace.hashQueries.length := by
  rw [directIntervalCount_eq_directHashQueries_length, hconsistent.1]
  rfl

theorem rawTargetCandidateOrdinal_lt_bound
    (intervals : List AdversaryCacheEntry) (source : Fin intervals.length)
    (input : HashInput) (output : HashOutput) (before after : QueryCache HashSpec)
    (hentry : intervals.get source = ⟨.inl (.inr input), output, before, after⟩)
    (hfresh : before input = none) (q : Nat) (hq : directIntervalCount intervals ≤ q) :
    (rawTargetCandidateViews (intervals.take source.val)).length < q := by
  have hsplit := trace_take_get_drop intervals source
  rw [hentry] at hsplit
  apply lt_of_lt_of_le _ ((rawTargetCandidateViews_length_le_directIntervalCount intervals).trans hq)
  conv_rhs => rw [hsplit, rawTargetCandidateViews_append]
  simp [rawTargetCandidateViews, rawTargetCandidateView?, hfresh]

theorem gameAfterSecretsWithViewTrace_directIntervalCount_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret)) :
    directIntervalCount result.2.trace.intervals ≤ q := by
  have hbase : (result.1, result.2.base) ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
    rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
      support_map]
    exact ⟨result, hresult, rfl⟩
  have hintervals := gameAfterSecretsWithFullTrace_support_interval_invariants adversary
    parameter otsSecret ftsSecret (result.1, result.2.base) hbase
  rw [FullAdversaryTrace.directIntervalCount_eq_hashQueries_length result.2.trace
    (show result.2.trace.Consistent from hintervals.1)]
  exact gameAfterSecretsWithFullTrace_hashQueries_length_le adversary q hq parameter hparameter
    otsSecret hots ftsSecret hfts (result.1, result.2.base) hbase

theorem AdversaryCacheEntry.exists_direct_fields (entry : AdversaryCacheEntry)
    (input : HashInput) (hinput : entry.input = .inl (.inr input)) :
    ∃ output before after, entry = ⟨.inl (.inr input), output, before, after⟩ := by
  rcases entry with ⟨entryInput, output, before, after⟩
  rcases entryInput with worldInput | request
  · rcases worldInput with uniformInput | hashInput
    · simp at hinput
    · simp only [Sum.inl.injEq, Sum.inr.injEq] at hinput
      subst hashInput
      exact ⟨output, before, after, rfl⟩
  · simp at hinput

theorem gameAfterSecretsWithViewTrace_fullyHonest_target_source_entry
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.cache.AgreesWithFn f)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest parameter result.1.1 result.1.2.1.message
        result.1.2.1.signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hproper : ProperFewTimeLeak f result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.trace.signing.toSigningLog (digestIndex digest) (digestLeaves digest))
    (hfull : FullyHonestOpening f result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      (digestIndex digest) (digestLeaves digest) result.1.2.1.signature)
    (source : Fin result.2.trace.intervals.length)
    (hbefore : (result.2.trace.intervals.get source).initialCache
      (tweakableHashInput parameter .message
        (messageDigestPayload result.1.1 result.1.2.1.message
          result.1.2.1.signature.randomness)) = none)
    (hafter : (result.2.trace.intervals.get source).finalCache
      (tweakableHashInput parameter .message
        (messageDigestPayload result.1.1 result.1.2.1.message
          result.1.2.1.signature.randomness)) ≠ none)
    (hkind : (result.2.trace.intervals.get source).input = .inl (.inr
        (tweakableHashInput parameter .message
          (messageDigestPayload result.1.1 result.1.2.1.message
            result.1.2.1.signature.randomness))) ∨
      ∃ request, (result.2.trace.intervals.get source).input = .inr request) :
    ∃ output before after,
      result.2.trace.intervals.get source =
        ⟨.inl (.inr (tweakableHashInput parameter .message
          (messageDigestPayload result.1.1 result.1.2.1.message
            result.1.2.1.signature.randomness))), output, before, after⟩ ∧
      before (tweakableHashInput parameter .message
        (messageDigestPayload result.1.1 result.1.2.1.message
          result.1.2.1.signature.randomness)) = none ∧
      signAttemptResultOfOutput output = some (digestIndex digest, digestLeaves digest) := by
  have hdirect := gameAfterSecretsWithViewTrace_fullyHonest_target_source_direct adversary
    parameter otsSecret ftsSecret result hresult f hf digest hdigest hadmissible hproper hfull
    source hbefore hafter hkind
  obtain ⟨output, _, _, houtput, hattempt⟩ :=
    gameAfterSecretsWithViewTrace_target_source_candidate adversary parameter otsSecret
      ftsSecret result hresult f hf digest hdigest hadmissible source hbefore hafter hkind
  obtain ⟨entryOutput, before, after, hentry⟩ :=
    AdversaryCacheEntry.exists_direct_fields (result.2.trace.intervals.get source) _ hdirect
  have hbase : (result.1, result.2.base) ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
    rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
      support_map]
    exact ⟨result, hresult, rfl⟩
  have hvalid := gameAfterSecretsWithFullTrace_support_validIntervals adversary parameter
    otsSecret ftsSecret (result.1, result.2.base) hbase
  have hcached := result.2.trace.directHashInterval_cached hvalid _ entryOutput before after
    (by rw [← hentry]; exact List.get_mem _ source)
  rw [hentry] at hbefore houtput
  have heq : entryOutput = output := Option.some.inj (hcached.symm.trans houtput)
  subst entryOutput
  exact ⟨output, before, after, hentry, hbefore, hattempt⟩

end SphincsSecurity.Concrete
