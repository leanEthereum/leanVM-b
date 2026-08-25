import SphincsSecurity.Proof.FullTrace
import SphincsSecurity.Proof.FewTimeTrace
import SphincsSecurity.Proof.SignerDigestSource

/-!
# Sources of previously cached selected digests

If a selected signer digest was already cached when that signer began, the full adversary trace
locates the earlier interval that first inserted it. Key generation is not a possible source.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

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
