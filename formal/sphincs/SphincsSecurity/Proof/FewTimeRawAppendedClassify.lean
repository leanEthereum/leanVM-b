import SphincsSecurity.Proof.FewTimeRawTargetSource
import SphincsSecurity.Proof.FewTimeRawPriorTarget
import SphincsSecurity.Proof.FewTimeUsedPatterns

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem gameAfterSecretsWithViewTrace_nonfresh_honestLeak_target_at_appended_state
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
    (hadversary : (result.1.2.1, state) ∈ support
      ((simulateQ (viewedFullTracedMappedAdversaryImpl
        ⟨parameter, result.1.1, otsSecret, ftsSecret⟩)
        (adversary.main ⟨result.1.1, parameter⟩)).run
          ⟨rootCache, ⟨[], [], []⟩, [], none⟩))
    (output : HashOutput) (digestCache : QueryCache HashSpec)
    (hquery : (output, digestCache) ∈ support
      ((randomOracle (tweakableHashInput parameter .message
        (messageDigestPayload result.1.1 result.1.2.1.message
          result.1.2.1.signature.randomness))).run state.cache))
    (hcache : QueryCache.enncard digestCache ≤ q)
    (hnotFresh : ¬VerifierFreshTarget parameter result) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    ∃ (distinct : Nat) (_ : distinct ∈ Finset.Icc 1 14)
          (pattern : UsedFewTimePattern signatureLimit distinct)
          (configuration : OriginConfiguration pattern.1 q) (candidate : Fin (q + 1)),
        FixedRawTargetViewedTerminal secretKey
          (adversaryWithTargetQuery adversary ⟨result.1.1, parameter⟩) rootCache q
            configuration candidate.val ((result.1.2.1, output),
              appendDirectTargetViewedState
                (tweakableHashInput parameter .message
                  (messageDigestPayload result.1.1 result.1.2.1.message
                    result.1.2.1.signature.randomness))
                state.cache output digestCache state) := by
  classical
  let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
  let targetPayload := messageDigestPayload result.1.1 result.1.2.1.message
    result.1.2.1.signature.randomness
  let targetInput := tweakableHashInput parameter .message targetPayload
  obtain ⟨sourceRootCache, adversaryCache, otherDigestCache, otherOutput, hrootNone, hchain, hsourceQuery,
      hdigestLe,
      htargetView, horigin, _⟩ :=
    gameAfterSecretsWithViewTrace_target_source_kind adversary parameter otsSecret
      ftsSecret result hresult
  rcases horigin with hverifier | ⟨source, hsourceInitial, hsourceFinal, hkind⟩
  · exact False.elim (hnotFresh ⟨sourceRootCache, adversaryCache, otherDigestCache, otherOutput,
      hrootNone, hchain, by simpa only [targetInput, targetPayload] using hverifier,
      by simpa only [targetInput, targetPayload] using hsourceQuery, hdigestLe, htargetView⟩)
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
    let candidate : Fin (q + 1) := ⟨targetOrdinal, by omega⟩
    refine ⟨hproper.1.cover.entries.card,
      Finset.mem_Icc.2 ⟨hproper.1.cover.entries_card_pos,
        hproper.1.cover.entries_card_le_trees⟩,
      ⟨hproper.1.cover.pattern.pad hle,
        hproper.1.cover.pattern.pad_assignment_surjective hle
          hproper.1.cover.pattern_assignment_surjective⟩,
      configuration, candidate, ?_⟩
    exact configuration.raw_priorTarget_fixedTerminal adversary parameter otsSecret ftsSecret
      result hresult f hf digest hdigest hproper hle hrealized source sourceOutput before after
      hentry hfresh hattempt rootCache state hadversary htrace
      targetInput output digestCache rfl hquery q hcache

end SphincsSecurity.Concrete
