import SphincsSecurity.Proof.FewTimeRawTargetSource

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem gameAfterSecretsWithViewTrace_honestLeak_target_classified_at_adversary_state
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
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
    (hle : result.2.trace.signing.toSigningLog.length ≤ signatureLimit)
    (rootCache : QueryCache HashSpec) (state : ViewedFullTraceState)
    (htrace : result.2.trace = state.trace)
    (hstateCache : state.cache ≤ result.2.cache) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    VerifierFreshTarget parameter result ∨
      ∃ (distinct : Nat) (_ : distinct ∈ Finset.Icc 1 14)
          (pattern : FewTimePattern signatureLimit distinct)
          (configuration : OriginConfiguration pattern q) (candidate : Fin q),
        FixedRawTargetViewedTerminal secretKey
          (adversary.main ⟨result.1.1, parameter⟩) rootCache q
            configuration candidate.val (result.1.2.1, state) := by
  classical
  let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
  let targetPayload := messageDigestPayload result.1.1 result.1.2.1.message
    result.1.2.1.signature.randomness
  let targetInput := tweakableHashInput parameter .message targetPayload
  obtain ⟨sourceRootCache, adversaryCache, digestCache, output, hrootNone, hchain, hquery,
      hdigestLe,
      htargetView, horigin, _⟩ :=
    gameAfterSecretsWithViewTrace_target_source_kind adversary parameter otsSecret
      ftsSecret result hresult
  rcases horigin with hverifier | ⟨source, hsourceInitial, hsourceFinal, hkind⟩
  · exact Or.inl ⟨sourceRootCache, adversaryCache, digestCache, output,
      hrootNone, hchain, by simpa only [targetInput, targetPayload] using hverifier,
      by simpa only [targetInput, targetPayload] using hquery, hdigestLe, htargetView⟩
  · obtain ⟨sourceOutput, before, after, hentry, hfresh, hattempt⟩ :=
      gameAfterSecretsWithViewTrace_fullyHonest_target_source_entry adversary parameter
        otsSecret ftsSecret result hresult f hf digest hdigest hadmissible hproper hfull source
        (by simpa only [targetInput, targetPayload] using hsourceInitial)
        (by simpa only [targetInput, targetPayload] using hsourceFinal)
        (by simpa only [targetInput, targetPayload] using hkind)
    have hbase : (result.1, result.2.base) ∈ support
        (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
      rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
        support_map]
      exact ⟨result, hresult, rfl⟩
    obtain ⟨configuration, hrealized⟩ :=
      hproper.1.cover.exists_paddedRealized_originConfiguration_of_queryBudget
        adversary q hq parameter hparameter otsSecret hots ftsSecret hfts
        (result.1, result.2.base) hbase f hf (digestIndex digest) (digestLeaves digest)
        signatureLimit hle
    let targetOrdinal := (rawTargetCandidateViews
      (result.2.trace.intervals.take source.val)).length
    have hordinalLt : targetOrdinal < q :=
      rawTargetCandidateOrdinal_lt_bound result.2.trace.intervals source _ sourceOutput
        before after hentry hfresh q
        (gameAfterSecretsWithViewTrace_directIntervalCount_le adversary q hq parameter
          hparameter otsSecret hots ftsSecret hfts result hresult)
    let candidate : Fin q := ⟨targetOrdinal, hordinalLt⟩
    have hfinalCache : QueryCache.enncard result.2.cache ≤ q :=
      gameAfterSecretsWithFullTrace_support_enncard_le adversary q hq parameter hparameter
        otsSecret hots ftsSecret hfts (result.1, result.2.base) hbase
    have hviewedCache : QueryCache.enncard state.cache ≤ q :=
      (QueryCache.enncard_mono hstateCache).trans hfinalCache
    refine Or.inr ⟨hproper.1.cover.entries.card,
      Finset.mem_Icc.2 ⟨hproper.1.cover.entries_card_pos,
        hproper.1.cover.entries_card_le_trees⟩,
      hproper.1.cover.pattern.pad hle, configuration, candidate, hviewedCache, ?_⟩
    intro monitored hmonitored heq
    have hstateEq : monitored.2.origin.viewed = state := congrArg Prod.snd heq
    have htrace' : result.2.trace = monitored.2.origin.viewed.trace := by
      rw [hstateEq]
      exact htrace
    exact configuration.raw_target_monitored_complete_of_projection adversary parameter
      otsSecret ftsSecret result hresult f hf digest hdigest hproper hle hrealized source
      sourceOutput before after hentry hfresh hattempt
      (adversary.main ⟨result.1.1, parameter⟩) rootCache monitored hmonitored htrace'

end SphincsSecurity.Concrete
