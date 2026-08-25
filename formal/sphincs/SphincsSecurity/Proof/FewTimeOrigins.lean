import SphincsSecurity.Proof.FewTimeRace

/-!
# Origins of selected few-time views

A selected cover entry always occupies its signer position. If its digest input was already cached,
it additionally has an earlier fresh direct-query source. This module packages those two disjoint
kinds of positions into one injective origin map.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

noncomputable def mixedOriginEmbedding {Entry Signer Source : Type}
    (prehit : Entry → Prop) (signer : Entry ↪ Signer)
    (source : {entry : Entry // prehit entry} ↪ Source) :
    Entry ↪ Signer ⊕ Source := by
  classical
  refine ⟨fun entry => if h : prehit entry then .inr (source ⟨entry, h⟩)
    else .inl (signer entry), ?_⟩
  intro left right heq
  by_cases hleft : prehit left <;> by_cases hright : prehit right
  · simp only [hleft, hright, ↓reduceDIte, Sum.inr.injEq] at heq
    exact congrArg Subtype.val (source.injective heq)
  · simp only [hleft, hright, ↓reduceDIte, Sum.inr_ne_inl] at heq
  · simp only [hleft, hright, ↓reduceDIte, Sum.inl_ne_inr] at heq
  · simp only [hleft, hright, ↓reduceDIte, Sum.inl.injEq] at heq
    exact signer.injective heq

theorem mixedOriginEmbedding_apply_prehit {Entry Signer Source : Type}
    (prehit : Entry → Prop) (signer : Entry ↪ Signer)
    (source : {entry : Entry // prehit entry} ↪ Source)
    (entry : Entry) (hprehit : prehit entry) :
    mixedOriginEmbedding prehit signer source entry = .inr (source ⟨entry, hprehit⟩) := by
  classical
  simp [mixedOriginEmbedding, hprehit]

theorem mixedOriginEmbedding_apply_fresh {Entry Signer Source : Type}
    (prehit : Entry → Prop) (signer : Entry ↪ Signer)
    (source : {entry : Entry // prehit entry} ↪ Source)
    (entry : Entry) (hfresh : ¬ prehit entry) :
    mixedOriginEmbedding prehit signer source entry = .inl (signer entry) := by
  classical
  simp [mixedOriginEmbedding, hfresh]

namespace Concrete

noncomputable def FewTimeCover.logIndexEmbedding {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    cover.entries ↪ Fin signingLog.length :=
  ⟨cover.logIndex, cover.logIndex_injective⟩

noncomputable def FewTimeCover.entriesEquivPatternSelected {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves) :
    cover.entries ≃ cover.pattern.selected := by
  classical
  let toSelected : cover.entries → cover.pattern.selected := fun entry =>
    ⟨cover.logIndex entry, by
      exact Finset.mem_image.2 ⟨entry, Finset.mem_univ _, rfl⟩⟩
  refine Equiv.ofBijective toSelected ⟨?_, ?_⟩
  · intro left right heq
    exact cover.logIndex_injective (congrArg Subtype.val heq)
  · intro selected
    obtain ⟨entry, _, hentry⟩ := Finset.mem_image.1 selected.2
    refine ⟨entry, Subtype.ext ?_⟩
    exact hentry

noncomputable def FewTimeCover.originEmbedding {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    {intervals : List AdversaryCacheEntry}
    (source : cover.PrecachedEntries trace hlog ↪ Fin intervals.length) :
    cover.entries ↪ Fin signingLog.length ⊕ Fin intervals.length :=
  mixedOriginEmbedding (cover.EntryDigestPrecached trace hlog)
    cover.logIndexEmbedding source

theorem FewTimeCover.originEmbedding_apply_prehit {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    {intervals : List AdversaryCacheEntry}
    (source : cover.PrecachedEntries trace hlog ↪ Fin intervals.length)
    (entry : cover.entries)
    (hprehit : cover.EntryDigestPrecached trace hlog entry) :
    cover.originEmbedding trace hlog source entry = .inr (source ⟨entry, hprehit⟩) := by
  exact mixedOriginEmbedding_apply_prehit _ _ _ entry hprehit

theorem FewTimeCover.originEmbedding_apply_fresh {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    {intervals : List AdversaryCacheEntry}
    (source : cover.PrecachedEntries trace hlog ↪ Fin intervals.length)
    (entry : cover.entries)
    (hfresh : ¬ cover.EntryDigestPrecached trace hlog entry) :
    cover.originEmbedding trace hlog source entry = .inl (cover.logIndex entry) := by
  exact mixedOriginEmbedding_apply_fresh _ _ _ entry hfresh

theorem FewTimeCover.selected_entries_have_injective_origins
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
      result.2.2.signing.toSigningLog index targetLeaves) :
    ∃ (origin : cover.entries ↪
          Fin result.2.2.signing.toSigningLog.length ⊕ Fin result.2.2.intervals.length)
        (source : cover.PrecachedEntries result.2.2.signing rfl →
          Fin result.2.2.intervals.length)
        (output : cover.PrecachedEntries result.2.2.signing rfl → HashOutput),
      Function.Injective source
        ∧ (∀ entry (hprehit : cover.EntryDigestPrecached result.2.2.signing rfl entry),
          origin entry = .inr (source ⟨entry, hprehit⟩))
        ∧ (∀ entry, ¬ cover.EntryDigestPrecached result.2.2.signing rfl entry →
          origin entry = .inl (cover.logIndex entry))
        ∧ ∀ entry,
          (result.2.2.intervals.get (source entry)).input =
              .inl (.inr (cover.entryDigestInput entry.1))
            ∧ (result.2.2.intervals.get (source entry)).initialCache
              (cover.entryDigestInput entry.1) = none
            ∧ (output entry, (result.2.2.intervals.get (source entry)).finalCache) ∈ support
              ((randomOracle (cover.entryDigestInput entry.1)).run
                (result.2.2.intervals.get (source entry)).initialCache)
            ∧ signAttemptResultOfOutput (output entry) ≠ none
            ∧ hashOutputFewTimeView (output entry) = cover.entryView entry.1 := by
  classical
  obtain ⟨source, output, hsourceInjective, hsource⟩ :=
    cover.precached_entries_have_injective_fresh_direct_view_sources adversary parameter
      otsSecret ftsSecret result hresult f hf index targetLeaves
  let sourceEmbedding : cover.PrecachedEntries result.2.2.signing rfl ↪
      Fin result.2.2.intervals.length := ⟨source, hsourceInjective⟩
  let origin := cover.originEmbedding result.2.2.signing rfl sourceEmbedding
  refine ⟨origin, source, output, hsourceInjective, ?_, ?_, hsource⟩
  · intro entry hprehit
    exact cover.originEmbedding_apply_prehit result.2.2.signing rfl sourceEmbedding
      entry hprehit
  · intro entry hfresh
    exact cover.originEmbedding_apply_fresh result.2.2.signing rfl sourceEmbedding entry hfresh

end Concrete

end SphincsSecurity
