import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeOriginSampler
import SphincsSecurity.Proof.FewTimeOrigins
import SphincsSecurity.Proof.FewTimeSource

/-!
# Numbering direct few-time sources

The full trace numbers every adversary interval, including signing calls and sampling queries. This
module gives selected prehits a separate injective numbering in the direct hash-query list, which is
the source index space used by the weighted sampler.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

noncomputable def FewTimeCover.precachedPatternSelected {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog) :
    Finset cover.pattern.selected :=
  (cover.precachedEntryFinset trace hlog).map cover.entriesEquivPatternSelected.toEmbedding

noncomputable def FewTimeCover.precachedOfPatternSelected {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (selected : ↑(cover.precachedPatternSelected trace hlog)) :
    cover.PrecachedEntries trace hlog := by
  classical
  let equivalence := cover.entriesEquivPatternSelected
  let entry := equivalence.symm selected.1
  refine ⟨entry, ?_⟩
  have hmem : entry ∈ cover.precachedEntryFinset trace hlog := by
    obtain ⟨original, horiginal, heq⟩ := Finset.mem_map.1 selected.2
    have horiginalEq : original = entry := by
      apply equivalence.injective
      rw [equivalence.apply_symm_apply]
      exact heq
    rw [← horiginalEq]
    exact horiginal
  exact (Finset.mem_filter.mp hmem).2

theorem FewTimeCover.precachedOfPatternSelected_entry {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (selected : ↑(cover.precachedPatternSelected trace hlog)) :
    (cover.precachedOfPatternSelected trace hlog selected).1 =
      cover.entriesEquivPatternSelected.symm selected.1 := rfl

theorem FewTimeCover.mem_precachedPatternSelected_iff {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (selected : cover.pattern.selected) :
    selected ∈ cover.precachedPatternSelected trace hlog ↔
      cover.EntryDigestPrecached trace hlog
        (cover.entriesEquivPatternSelected.symm selected) := by
  classical
  rw [FewTimeCover.precachedPatternSelected, Finset.mem_map]
  constructor
  · rintro ⟨entry, hentry, heq⟩
    have hentryEq : entry = cover.entriesEquivPatternSelected.symm selected := by
      apply cover.entriesEquivPatternSelected.injective
      rw [cover.entriesEquivPatternSelected.apply_symm_apply]
      exact heq
    rw [← hentryEq]
    exact (Finset.mem_filter.mp hentry).2
  · intro hprehit
    refine ⟨cover.entriesEquivPatternSelected.symm selected, ?_, ?_⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hprehit⟩
    · exact cover.entriesEquivPatternSelected.apply_symm_apply selected

noncomputable def FewTimeCover.originConfiguration {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (sources : Nat)
    (source : cover.PrecachedEntries trace hlog → Fin sources)
    (hsource : Function.Injective source) : OriginConfiguration cover.pattern sources := by
  classical
  let selectedPrehits := cover.precachedPatternSelected trace hlog
  refine ⟨selectedPrehits,
    ⟨fun selected => source (cover.precachedOfPatternSelected trace hlog selected), ?_⟩⟩
  intro left right heq
  have hasPrecached : cover.precachedOfPatternSelected trace hlog left =
      cover.precachedOfPatternSelected trace hlog right := hsource heq
  apply Subtype.ext
  have hentries := congrArg (fun entry : cover.PrecachedEntries trace hlog => entry.1)
    hasPrecached
  exact cover.entriesEquivPatternSelected.symm.injective hentries

theorem FewTimeCover.originConfiguration_source_apply {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (sources : Nat) (source : cover.PrecachedEntries trace hlog → Fin sources)
    (hsource : Function.Injective source)
    (selected : ↑(cover.originConfiguration trace hlog sources source hsource).prehit) :
    (cover.originConfiguration trace hlog sources source hsource).source.1 selected =
      source (cover.precachedOfPatternSelected trace hlog selected) := rfl

theorem FewTimeCover.precached_entries_have_injective_numbered_sources
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
    ∃ (source : cover.PrecachedEntries result.2.2.signing rfl →
          Fin result.2.2.hashQueries.length)
        (intervalSource : cover.PrecachedEntries result.2.2.signing rfl →
          Fin result.2.2.intervals.length)
        (selectedInterval : cover.PrecachedEntries result.2.2.signing rfl →
          Fin result.2.2.intervals.length)
        (output : cover.PrecachedEntries result.2.2.signing rfl → HashOutput),
      Function.Injective source
        ∧ Function.Injective intervalSource
        ∧ ∀ entry, ∃ hdirect : isDirectHashQuery
            (result.2.2.intervals.get (intervalSource entry)).input,
          (source entry).val =
              (Fin.encodeSubtype (fun position =>
                isDirectHashQuery (result.2.2.intervals.get position).input)
                ⟨intervalSource entry, hdirect⟩).val
            ∧ (intervalSource entry).val < (selectedInterval entry).val
            ∧ AdversaryCacheEntry.signingEntry?
              (result.2.2.intervals.get (selectedInterval entry)) =
                some (cover.cacheEntry result.2.2.signing rfl entry.1)
            ∧ ((result.2.2.intervals.take (selectedInterval entry).val).filterMap
              AdversaryCacheEntry.signingEntry?).length = (cover.logIndex entry.1).val
            ∧ (result.2.2.intervals.get (intervalSource entry)).input =
              .inl (.inr (cover.entryDigestInput entry.1))
            ∧ (result.2.2.intervals.get (intervalSource entry)).initialCache
              (cover.entryDigestInput entry.1) = none
            ∧ (output entry,
                (result.2.2.intervals.get (intervalSource entry)).finalCache) ∈ support
              ((randomOracle (cover.entryDigestInput entry.1)).run
                (result.2.2.intervals.get (intervalSource entry)).initialCache)
            ∧ signAttemptResultOfOutput (output entry) ≠ none
            ∧ hashOutputFewTimeView (output entry) = cover.entryView entry.1 := by
  classical
  obtain ⟨intervalSource, selectedInterval, output, hintervalInjective, hinterval⟩ :=
    cover.precached_entries_have_injective_fresh_direct_view_sources adversary parameter
      otsSecret ftsSecret result hresult f hf index targetLeaves
  let directSource : cover.PrecachedEntries result.2.2.signing rfl →
      {position : Fin result.2.2.intervals.length //
        isDirectHashQuery (result.2.2.intervals.get position).input} :=
    fun entry => ⟨intervalSource entry, by rw [(hinterval entry).2.2.2.1]; trivial⟩
  have hdirectInjective : Function.Injective directSource := by
    intro left right heq
    exact hintervalInjective (congrArg Subtype.val heq)
  let encodedSource : cover.PrecachedEntries result.2.2.signing rfl →
      Fin (Fin.countP fun position =>
        isDirectHashQuery (result.2.2.intervals.get position).input) :=
    fun entry => Fin.encodeSubtype _ (directSource entry)
  have hencodedInjective : Function.Injective encodedSource := by
    exact Function.Injective.comp
      (Function.LeftInverse.injective (Fin.decodeSubtype_encodeSubtype _)) hdirectInjective
  have hconsistent :=
    (gameAfterSecretsWithFullTrace_support_interval_invariants adversary parameter otsSecret
      ftsSecret result hresult).1
  have hcount : Fin.countP (fun position =>
      isDirectHashQuery (result.2.2.intervals.get position).input) =
      result.2.2.hashQueries.length := by
    rw [FullAdversaryTrace.hashQueries, ← hconsistent.1]
    exact adversaryIntervals_directHashCount result.2.2.intervals
  let source : cover.PrecachedEntries result.2.2.signing rfl →
      Fin result.2.2.hashQueries.length := fun entry => Fin.cast hcount (encodedSource entry)
  have hsourceInjective : Function.Injective source := by
    exact Function.Injective.comp (Fin.cast_injective hcount) hencodedInjective
  refine ⟨source, intervalSource, selectedInterval, output, hsourceInjective,
    hintervalInjective, ?_⟩
  intro entry
  refine ⟨(directSource entry).2, rfl, hinterval entry⟩

end SphincsSecurity.Concrete
