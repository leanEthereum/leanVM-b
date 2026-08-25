import SphincsSecurity.Proof.FullTrace
import SphincsSecurity.Proof.FewTimeTrace
import SphincsSecurity.Proof.FewTimeLoop
import SphincsSecurity.Proof.SignerDigestSource

/-!
# Sources of previously cached selected digests

If a selected signer digest was already cached when that signer began, the full adversary trace
locates the earlier interval that first inserted it. Key generation is not a possible source.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem traverseOption_some {alpha : Type} {count : Nat}
    (values : Fin count → alpha) :
    traverseOption (fun position => some (values position)) = some values := by
  induction count with
  | zero =>
      rw [traverseOption]
      congr
      funext position
      exact Fin.elim0 position
  | succ count ih =>
      rw [traverseOption, ih]
      change some (Fin.cases (values 0) (fun position => values position.succ)) = some values
      rw [Option.some.injEq]
      funext position
      cases position using Fin.cases <;> rfl

theorem SuccessfulSignRun.eval_signAfterDigest {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hrun : SuccessfulSignRun f cache secretKey message signature) :
    ∃ (index : Index) (leaves : DigestTree → FtsLeaf),
      SuccessfulDigestRun f cache secretKey message signature.randomness index leaves
        ∧ evalWithAnswerFn f
          (signAfterDigest secretKey signature.randomness index leaves) = some signature := by
  obtain ⟨index, leaves, parts, hdigest, hftsSecret, hftsPath, hcounter, hchainValue,
      hauthPath, _, hlayers, _⟩ := hrun
  refine ⟨index, leaves, hdigest, ?_⟩
  have hlayers' :
      (fun lay => evalWithAnswerFn f (signLayer secretKey index lay)) =
        (fun lay => some (parts lay)) := by
    funext lay
    exact hlayers lay
  simp only [signAfterDigest, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
    hlayers', traverseOption_some, evalWithAnswerFn_pure, Option.some.injEq]
  cases signature
  simp_all

theorem SuccessfulSignRun.cached_digest_source {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hrun : SuccessfulSignRun f cache secretKey message signature)
    (hf : cache.AgreesWithFn f) {output : HashOutput}
    (hcached : cache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message signature.randomness)) = some output) :
    ∃ (index : Index) (leaves : DigestTree → FtsLeaf),
      signAttemptResultOfOutput output = some (index, leaves)
        ∧ evalWithAnswerFn f
          (signAfterDigest secretKey signature.randomness index leaves) = some signature := by
  obtain ⟨index, leaves, hdigest, hafter⟩ := hrun.eval_signAfterDigest
  obtain ⟨_, digest, heval, hadmissible, hindex, hleaves, _⟩ := hdigest.extract
  have hfinput : f (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message signature.randomness)) = output :=
    hf hcached
  have hdigest : digest = truncateMessageDigest output := by
    rw [← heval]
    simp only [messageDigest, oracleHash, evalWithAnswerFn_bind, evalWithAnswerFn_query,
      hfinput, evalWithAnswerFn_pure]
  refine ⟨index, leaves, ?_, hafter⟩
  simp only [signAttemptResultOfOutput, ← hdigest, if_pos hadmissible]
  rw [hindex, hleaves]

theorem FewTimeCover.precached_entry_has_earlier_source
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hresult : result ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (index : Index) (targetLeaves : DigestTree → FtsLeaf)
    (cover : FewTimeCover f result.2.1
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.2.signing.toSigningLog index targetLeaves)
    (entry : cover.entries)
    (hprecached : cover.EntryDigestPrecached result.2.2.signing rfl entry) :
    ∃ (source selected : Fin result.2.2.intervals.length),
      source.val < selected.val
        ∧ AdversaryCacheEntry.signingEntry? (result.2.2.intervals.get selected) =
          some (cover.cacheEntry result.2.2.signing rfl entry)
        ∧ (result.2.2.intervals.get source).initialCache
            (cover.entryDigestInput entry) = none
        ∧ (result.2.2.intervals.get source).finalCache
            (cover.entryDigestInput entry) ≠ none
        ∧ ((result.2.2.intervals.get source).input =
              .inl (.inr (cover.entryDigestInput entry))
          ∨ ∃ request, (result.2.2.intervals.get source).input = .inr request) := by
  have hintervals := gameAfterSecretsWithFullTrace_support_interval_invariants
    adversary parameter otsSecret ftsSecret result hresult
  have hvalid := gameAfterSecretsWithFullTrace_support_validIntervals
    adversary parameter otsSecret ftsSecret result hresult
  obtain ⟨rootCache, adversaryCache, hrootNone, hchain, _⟩ :=
    gameAfterSecretsWithFullTrace_support_cacheChain
      adversary parameter otsSecret ftsSecret result hresult
  have hstart : rootCache (cover.entryDigestInput entry) = none := by
    simpa only [FewTimeCover.entryDigestInput] using hrootNone
      (messageDigestPayload result.1.1
        (cover.select (cover.representativeTree entry)).entry.1
        (cover.select (cover.representativeTree entry)).signature.randomness)
  obtain ⟨source, selected, hlt, hselected, hmiss, hhit⟩ :=
    hchain.source_before_signingEntry hintervals.1
      (cover.cacheEntry result.2.2.signing rfl entry)
      (cover.cacheEntry_mem result.2.2.signing rfl entry)
      (cover.entryDigestInput entry) hstart hprecached
  have hkind := FullAdversaryTrace.transition_source_kind hvalid
    (result.2.2.intervals.get source) (List.get_mem _ source)
    (cover.entryDigestInput entry) hmiss hhit
  exact ⟨source, selected, hlt, hselected, hmiss, hhit, hkind⟩

theorem FewTimeCover.precached_entry_has_earlier_exact_source
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hresult : result ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (index : Index) (targetLeaves : DigestTree → FtsLeaf)
    (cover : FewTimeCover f result.2.1
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.2.signing.toSigningLog index targetLeaves)
    (entry : cover.entries)
    (hprecached : cover.EntryDigestPrecached result.2.2.signing rfl entry) :
    ∃ (source selected : Fin result.2.2.intervals.length),
      source.val < selected.val
        ∧ AdversaryCacheEntry.signingEntry? (result.2.2.intervals.get selected) =
          some (cover.cacheEntry result.2.2.signing rfl entry)
        ∧ (result.2.2.intervals.get source).initialCache
            (cover.entryDigestInput entry) = none
        ∧ (result.2.2.intervals.get source).finalCache
            (cover.entryDigestInput entry) ≠ none
        ∧ ((result.2.2.intervals.get source).input =
              .inl (.inr (cover.entryDigestInput entry))
          ∨ ∃ earlier : Fin result.2.2.signing.length,
              earlier.val < (cover.logIndex entry).val
                ∧ AdversaryCacheEntry.signingEntry? (result.2.2.intervals.get source) =
                  some (result.2.2.signing.get earlier)) := by
  have hintervals := gameAfterSecretsWithFullTrace_support_interval_invariants
    adversary parameter otsSecret ftsSecret result hresult
  have hvalid := gameAfterSecretsWithFullTrace_support_validIntervals
    adversary parameter otsSecret ftsSecret result hresult
  obtain ⟨rootCache, adversaryCache, hrootNone, hchain, _⟩ :=
    gameAfterSecretsWithFullTrace_support_cacheChain
      adversary parameter otsSecret ftsSecret result hresult
  let selectedSigning : Fin result.2.2.signing.length :=
    ⟨(cover.logIndex entry).val, by
      simpa only [SigningCacheTrace.toSigningLog, List.length_map] using
        (cover.logIndex entry).isLt⟩
  have hselectedSigning : result.2.2.signing.get selectedSigning =
      cover.cacheEntry result.2.2.signing rfl entry := by
    rfl
  obtain ⟨selected, hselected, hearlier⟩ :=
    result.2.2.signingIndex_interval hintervals.1 selectedSigning
  have hselected' : AdversaryCacheEntry.signingEntry?
      (result.2.2.intervals.get selected) =
        some (cover.cacheEntry result.2.2.signing rfl entry) := by
    simpa only [hselectedSigning] using hselected
  have hstart : rootCache (cover.entryDigestInput entry) = none := by
    simpa only [FewTimeCover.entryDigestInput] using hrootNone
      (messageDigestPayload result.1.1
        (cover.select (cover.representativeTree entry)).entry.1
        (cover.select (cover.representativeTree entry)).signature.randomness)
  have hselectedCache : (result.2.2.intervals.get selected).initialCache
      (cover.entryDigestInput entry) ≠ none := by
    rw [(result.2.2.intervals.get selected).initialCache_eq_of_signingEntry?_eq_some
      hselected']
    exact hprecached
  obtain ⟨source, hlt, hmiss, hhit⟩ :=
    hchain.transition_before (cover.entryDigestInput entry) selected hstart hselectedCache
  have hkind := FullAdversaryTrace.transition_source_kind hvalid
    (result.2.2.intervals.get source) (List.get_mem _ source)
    (cover.entryDigestInput entry) hmiss hhit
  refine ⟨source, selected, hlt, hselected', hmiss, hhit, ?_⟩
  rcases hkind with hdirect | ⟨request, hrequest⟩
  · exact Or.inl hdirect
  · right
    have hsourceEntry : ∃ sourceEntry : SigningCacheEntry,
        AdversaryCacheEntry.signingEntry? (result.2.2.intervals.get source) =
          some sourceEntry := by
      generalize hsourceInterval : result.2.2.intervals.get source = sourceInterval
      rcases sourceInterval with ⟨input, output, initialCache, finalCache⟩
      rw [hsourceInterval] at hrequest
      cases input with
      | inl worldInput => simp at hrequest
      | inr actualRequest =>
          have hrequest' : actualRequest = request := Sum.inr.inj hrequest
          subst request
          exact ⟨⟨actualRequest, output, initialCache, finalCache⟩, rfl⟩
    obtain ⟨sourceEntry, hsourceEntry⟩ := hsourceEntry
    obtain ⟨earlier, hearlierLt, hearlierEntry⟩ :=
      hearlier source hlt sourceEntry hsourceEntry
    exact ⟨earlier, by simpa only [selectedSigning] using hearlierLt,
      hsourceEntry.trans (congrArg some hearlierEntry.symm)⟩

theorem FewTimeCover.precached_entry_has_earlier_direct_source
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hresult : result ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.1.AgreesWithFn f)
    (index : Index) (targetLeaves : DigestTree → FtsLeaf)
    (cover : FewTimeCover f result.2.1
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.2.signing.toSigningLog index targetLeaves)
    (entry : cover.entries)
    (hprecached : cover.EntryDigestPrecached result.2.2.signing rfl entry) :
    ∃ source : Fin result.2.2.intervals.length,
      (result.2.2.intervals.get source).input =
        .inl (.inr (cover.entryDigestInput entry)) := by
  obtain ⟨source, _, _, _, hsourceMiss, hsourceHit, hkind⟩ :=
    cover.precached_entry_has_earlier_exact_source adversary parameter otsSecret ftsSecret
      result hresult f index targetLeaves entry hprecached
  rcases hkind with hdirect | ⟨earlier, hearlier, hsourceEntry⟩
  · exact ⟨source, hdirect⟩
  · exfalso
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    let earlierEntry := result.2.2.signing.get earlier
    let selected := cover.select (cover.representativeTree entry)
    let targetPayload := messageDigestPayload result.1.1 selected.entry.1
      selected.signature.randomness
    have hinvariants := gameAfterSecretsWithFullTrace_support_invariants adversary parameter
      otsSecret ftsSecret result hresult
    have hvalid : earlierEntry.ValidRun secretKey :=
      hinvariants.1 earlierEntry (List.get_mem _ earlier)
    have hcaches := hinvariants.2.1
    have hearlierLe : earlierEntry.finalCache ≤ result.2.1 :=
      (hcaches earlierEntry (List.get_mem _ earlier)).2
    have hbefore : earlierEntry.initialCache
        (tweakableHashInput parameter .message targetPayload) = none := by
      have hcacheEq := AdversaryCacheEntry.initialCache_eq_of_signingEntry?_eq_some
        (interval := result.2.2.intervals.get source) hsourceEntry
      rw [← hcacheEq]
      simpa only [FewTimeCover.entryDigestInput, selected, targetPayload] using hsourceMiss
    have hafter : earlierEntry.finalCache
        (tweakableHashInput parameter .message targetPayload) ≠ none := by
      have hcacheEq := AdversaryCacheEntry.finalCache_eq_of_signingEntry?_eq_some
        (interval := result.2.2.intervals.get source) hsourceEntry
      rw [← hcacheEq]
      simpa only [FewTimeCover.entryDigestInput, selected, targetPayload] using hsourceHit
    obtain ⟨output, houtputEarlier⟩ := Option.ne_none_iff_exists'.mp hafter
    have houtputFinal : result.2.1
        (tweakableHashInput parameter .message targetPayload) = some output :=
      hearlierLe houtputEarlier
    have hselectedRun := cover.cacheEntry_successfulSignRun result.2.2.signing rfl
      hinvariants.1 hcaches hf entry
    obtain ⟨actualIndex, actualLeaves, hattemptOutput, htailEval⟩ :=
      hselectedRun.cached_digest_source hf (by
        simpa only [FewTimeCover.entryDigestInput, selected, targetPayload] using houtputFinal)
    change (earlierEntry.signature, earlierEntry.finalCache) ∈ support
      ((simulateQ romImpl (sign secretKey earlierEntry.request)).run
        earlierEntry.initialCache) at hvalid
    rw [sign_eq_digestLoop_afterDigest, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff] at hvalid
    obtain ⟨⟨loopResult, loopCache⟩, hloop, hrest⟩ := hvalid
    have hloopHit : loopCache
        (tweakableHashInput parameter .message targetPayload) ≠ none := by
      intro hloopNone
      cases loopResult with
      | none =>
          have hpure : (earlierEntry.signature, earlierEntry.finalCache) =
              (none, loopCache) := by
            simpa using hrest
          have hcache : earlierEntry.finalCache = loopCache := congrArg Prod.snd hpure
          rw [hcache, hloopNone] at hafter
          exact hafter rfl
      | some data =>
          rcases data with ⟨randomness, sourceIndex, sourceLeaves⟩
          have hrest' : (earlierEntry.signature, earlierEntry.finalCache) ∈ support
              ((simulateQ (randomOracle : QueryImpl HashSpec _)
                (signAfterDigest secretKey randomness sourceIndex sourceLeaves)).run loopCache) := by
            simpa only [simulateQ_romImpl_liftM] using hrest
          have hnone := signAfterDigest_cache_message_none secretKey randomness sourceIndex
            sourceLeaves loopCache earlierEntry.finalCache earlierEntry.signature hrest'
            targetPayload hloopNone
          exact hafter hnone
    obtain ⟨loopOutput, hloopOutput⟩ := Option.ne_none_iff_exists'.mp hloopHit
    have hloopLe : loopCache ≤ earlierEntry.finalCache := by
      cases loopResult with
      | none =>
          have hpure : (earlierEntry.signature, earlierEntry.finalCache) =
              (none, loopCache) := by
            simpa using hrest
          have hcache : earlierEntry.finalCache = loopCache := congrArg Prod.snd hpure
          rw [hcache]
      | some data =>
          rcases data with ⟨randomness, sourceIndex, sourceLeaves⟩
          exact simulateQ_romImpl_cache_le
            (liftM (signAfterDigest secretKey randomness sourceIndex sourceLeaves) :
              OracleComp OracleWorld (Option Signature)) loopCache
            (earlierEntry.signature, earlierEntry.finalCache) hrest
    have hloopOutputEq : loopOutput = output := by
      have := hloopLe hloopOutput
      rw [houtputEarlier] at this
      exact Option.some.inj this.symm
    have hattemptOutput' : signAttemptResultOfOutput loopOutput =
        some (actualIndex, actualLeaves) := by
      rw [hloopOutputEq]
      exact hattemptOutput
    obtain ⟨_, sourceRandomness, _, hpayload, hloopResult⟩ :=
      signDigestLoop_successful_source_is_selected digestAttemptLimit secretKey
        earlierEntry.request earlierEntry.initialCache loopCache loopResult hloop targetPayload
        loopOutput actualIndex actualLeaves hbefore hloopOutput hattemptOutput'
    have hpayloadFields := messageDigestPayload_injective result.1.1 hpayload.symm
    have hmessage : earlierEntry.request = selected.entry.1 := hpayloadFields.1
    have hrandomness : sourceRandomness = selected.signature.randomness := hpayloadFields.2
    have hrest' : (earlierEntry.signature, earlierEntry.finalCache) ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (signAfterDigest secretKey sourceRandomness actualIndex actualLeaves)).run loopCache) := by
      rw [hloopResult] at hrest
      simpa only [simulateQ_romImpl_liftM] using hrest
    have hearlierEval := (replay_of_mem_support_of_le
      (signAfterDigest secretKey sourceRandomness actualIndex actualLeaves) loopCache
      earlierEntry.signature earlierEntry.finalCache result.2.1 hrest' hearlierLe f hf).1
    have hresponse : earlierEntry.signature = some selected.signature := by
      rw [hrandomness] at hearlierEval
      exact hearlierEval.symm.trans htailEval
    have hne := cover.earlier_successful_digest_input_ne result.2.2.signing rfl
      hinvariants.1 hcaches hf entry earlier hearlier selected.signature hresponse
    apply hne
    rw [hmessage]
    rfl

theorem FewTimeCover.precached_entry_has_earlier_sample_source
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hresult : result ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (index : Index) (targetLeaves : DigestTree → FtsLeaf)
    (cover : FewTimeCover f result.2.1
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.2.signing.toSigningLog index targetLeaves)
    (entry : cover.entries)
    (hprecached : cover.EntryDigestPrecached result.2.2.signing rfl entry) :
    (∃ source : Fin result.2.2.intervals.length,
        (result.2.2.intervals.get source).input =
          .inl (.inr (cover.entryDigestInput entry)))
      ∨ ∃ (earlier : Fin result.2.2.signing.length) (attemptIndex : Nat)
          (randomness : Randomness),
          earlier.val < (cover.logIndex entry).val
            ∧ attemptIndex < digestAttemptLimit
            ∧ randomness ∈ support sampleRandomness
            ∧ cover.entryDigestInput entry =
              tweakableHashInput parameter .message
                (messageDigestPayload result.1.1
                  (result.2.2.signing.get earlier).request randomness) := by
  obtain ⟨source, selected, hlt, hselected, hmiss, hhit, hkind⟩ :=
    cover.precached_entry_has_earlier_exact_source adversary parameter otsSecret ftsSecret
      result hresult f index targetLeaves entry hprecached
  rcases hkind with hdirect | ⟨earlier, hearlier, hsourceEntry⟩
  · exact Or.inl ⟨source, hdirect⟩
  · right
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    let sourceSigningEntry := result.2.2.signing.get earlier
    have hinvariants := gameAfterSecretsWithFullTrace_support_invariants
      adversary parameter otsSecret ftsSecret result hresult
    have hvalid : sourceSigningEntry.ValidRun secretKey :=
      hinvariants.1 sourceSigningEntry (List.get_mem _ earlier)
    let targetPayload := messageDigestPayload result.1.1
      (cover.select (cover.representativeTree entry)).entry.1
      (cover.select (cover.representativeTree entry)).signature.randomness
    have htarget : cover.entryDigestInput entry =
        tweakableHashInput parameter .message targetPayload := by
      rfl
    have hbefore : sourceSigningEntry.initialCache
        (tweakableHashInput parameter .message targetPayload) = none := by
      have hcacheEq := AdversaryCacheEntry.initialCache_eq_of_signingEntry?_eq_some
        (interval := result.2.2.intervals.get source) hsourceEntry
      rw [← htarget, ← hcacheEq]
      exact hmiss
    have hafter : sourceSigningEntry.finalCache
        (tweakableHashInput parameter .message targetPayload) ≠ none := by
      have hcacheEq := AdversaryCacheEntry.finalCache_eq_of_signingEntry?_eq_some
        (interval := result.2.2.intervals.get source) hsourceEntry
      rw [← htarget, ← hcacheEq]
      exact hhit
    obtain ⟨attemptIndex, randomness, hattemptIndex, hrandomness, hpayload⟩ :=
      sign_message_source secretKey sourceSigningEntry.request sourceSigningEntry.initialCache
        sourceSigningEntry.finalCache sourceSigningEntry.signature hvalid targetPayload hbefore hafter
    exact ⟨earlier, attemptIndex, randomness, hearlier, hattemptIndex, hrandomness,
      by rw [htarget, hpayload]⟩

end SphincsSecurity.Concrete
