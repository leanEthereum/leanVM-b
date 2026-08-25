import SphincsSecurity.Proof.FewTimeOriginSampler
import SphincsSecurity.Proof.DirectQueryBudget

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

theorem FewTimeCover.originConfiguration_prehit_card {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (sources : Nat)
    (source : cover.PrecachedEntries trace hlog → Fin sources)
    (hsource : Function.Injective source) :
    (cover.originConfiguration trace hlog sources source hsource).prehit.card =
      (cover.precachedEntryFinset trace hlog).card := by
  classical
  simp [FewTimeCover.originConfiguration, FewTimeCover.precachedPatternSelected]

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
    fun entry => ⟨intervalSource entry, by rw [(hinterval entry).2.2.1]; trivial⟩
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

private theorem AdversaryCacheEntry.queryEntry_eq_of_direct_hash_runs
    (secretKey : SecretKey) (entry : AdversaryCacheEntry) (target : HashInput)
    (output : HashOutput) (hinput : entry.input = .inl (.inr target))
    (hvalid : (entry.output, entry.finalCache) ∈ support
      ((unloggedMappedAdversaryImpl secretKey entry.input).run entry.initialCache))
    (hrun : (output, entry.finalCache) ∈ support
      ((randomOracle target).run entry.initialCache)) :
    entry.queryEntry =
      (⟨.inl (.inr target), output⟩ :
        (query : (OracleWorld + SigningSpec).Domain) ×
          (OracleWorld + SigningSpec).Range query) := by
  rcases entry with ⟨input, entryOutput, initialCache, finalCache⟩
  cases input with
  | inr request => simp at hinput
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput => simp at hinput
      | inr hashInput =>
          simp only [Sum.inl.injEq, Sum.inr.injEq] at hinput
          subst hashInput
          change (entryOutput, finalCache) ∈ support
            ((randomOracle target).run initialCache) at hvalid
          have hcachedEntry := randomOracle_run_output_cached target initialCache finalCache
            entryOutput hvalid
          have hcachedOutput := randomOracle_run_output_cached target initialCache finalCache
            output hrun
          have heq : entryOutput = output :=
            Option.some.inj (hcachedEntry.symm.trans hcachedOutput)
          subst output
          rfl

theorem FewTimeCover.precached_entries_have_numbered_source_entries
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
        (output : cover.PrecachedEntries result.2.2.signing rfl → HashOutput),
      Function.Injective source
        ∧ Function.Injective intervalSource
        ∧ ∀ entry,
          result.2.2.hashQueries.get (source entry) =
              (cover.entryDigestInput entry.1, output entry)
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
  obtain ⟨_numberedSource, intervalSource, _selectedInterval, output, _hnumberedInjective,
      hintervalInjective, hnumbered⟩ :=
    cover.precached_entries_have_injective_numbered_sources adversary parameter otsSecret
      ftsSecret result hresult f hf index targetLeaves
  have hinterval : ∀ entry,
      (result.2.2.intervals.get (intervalSource entry)).input =
          .inl (.inr (cover.entryDigestInput entry.1))
        ∧ (result.2.2.intervals.get (intervalSource entry)).initialCache
          (cover.entryDigestInput entry.1) = none
        ∧ (output entry,
            (result.2.2.intervals.get (intervalSource entry)).finalCache) ∈ support
          ((randomOracle (cover.entryDigestInput entry.1)).run
            (result.2.2.intervals.get (intervalSource entry)).initialCache)
        ∧ signAttemptResultOfOutput (output entry) ≠ none
        ∧ hashOutputFewTimeView (output entry) = cover.entryView entry.1 := by
    intro entry
    exact (hnumbered entry).choose_spec.2.2.2
  have hvalid := gameAfterSecretsWithFullTrace_support_validIntervals adversary parameter
    otsSecret ftsSecret result hresult
  have hconsistent := (gameAfterSecretsWithFullTrace_support_interval_invariants adversary
    parameter otsSecret ftsSecret result hresult).1
  let pair : cover.PrecachedEntries result.2.2.signing rfl → HashInput × HashOutput :=
    fun entry => (cover.entryDigestInput entry.1, output entry)
  have hpairMem : ∀ entry, pair entry ∈ result.2.2.hashQueries := by
    intro entry
    let interval := result.2.2.intervals.get (intervalSource entry)
    have hqueryEntry := AdversaryCacheEntry.queryEntry_eq_of_direct_hash_runs
      (⟨parameter, result.1.1, otsSecret, ftsSecret⟩ : SecretKey) interval
      (cover.entryDigestInput entry.1) (output entry) (hinterval entry).1
      (hvalid interval (List.get_mem _ _)) (hinterval entry).2.2.1
    rw [FullAdversaryTrace.hashQueries, mem_directHashQueries_iff]
    rw [← hconsistent.1]
    apply List.mem_map.2
    exact ⟨interval, List.get_mem _ _, hqueryEntry⟩
  let source : cover.PrecachedEntries result.2.2.signing rfl →
      Fin result.2.2.hashQueries.length := fun entry =>
    ⟨result.2.2.hashQueries.idxOf (pair entry),
      List.idxOf_lt_length_of_mem (hpairMem entry)⟩
  have hsourceGet : ∀ entry,
      result.2.2.hashQueries.get (source entry) = pair entry := by
    intro entry
    exact List.idxOf_get _
  have hsourceInjective : Function.Injective source := by
    intro left right heq
    apply Subtype.ext
    apply cover.entryDigestInput_injective
    have hpairs : pair left = pair right := by
      rw [← hsourceGet left, heq, hsourceGet right]
    exact congrArg Prod.fst hpairs
  exact ⟨source, intervalSource, output, hsourceInjective, hintervalInjective,
    fun entry => ⟨hsourceGet entry, hinterval entry⟩⟩

theorem FewTimeCover.has_originConfiguration_of_hashQueries_length_le
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
    (q : Nat) (hqueries : result.2.2.hashQueries.length ≤ q) :
    ∃ configuration : OriginConfiguration cover.pattern q,
      configuration.prehit.card =
        (cover.precachedEntryFinset result.2.2.signing rfl).card := by
  classical
  obtain ⟨numberedSource, _intervalSource, _selectedInterval, _output,
      hnumberedInjective, _, _⟩ :=
    cover.precached_entries_have_injective_numbered_sources adversary parameter otsSecret
      ftsSecret result hresult f hf index targetLeaves
  let source : cover.PrecachedEntries result.2.2.signing rfl → Fin q :=
    fun entry => Fin.castLE hqueries (numberedSource entry)
  have hsourceInjective : Function.Injective source := by
    exact Function.Injective.comp (finCastLEEmbedding hqueries).injective hnumberedInjective
  let configuration := cover.originConfiguration result.2.2.signing rfl q source
    hsourceInjective
  exact ⟨configuration,
    cover.originConfiguration_prehit_card result.2.2.signing rfl q source hsourceInjective⟩

theorem FewTimeCover.has_originConfiguration_of_queryBudget
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (result : (Digest × Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hresult : result ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.1.AgreesWithFn f)
    (index : Index) (targetLeaves : DigestTree → FtsLeaf)
    (cover : FewTimeCover f result.2.1
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.2.signing.toSigningLog index targetLeaves) :
    ∃ configuration : OriginConfiguration cover.pattern q,
      configuration.prehit.card =
        (cover.precachedEntryFinset result.2.2.signing rfl).card := by
  exact cover.has_originConfiguration_of_hashQueries_length_le adversary parameter otsSecret
    ftsSecret result hresult f hf index targetLeaves q
    (gameAfterSecretsWithFullTrace_hashQueries_length_le adversary q hq parameter hparameter
      otsSecret hots ftsSecret hfts result hresult)

end SphincsSecurity.Concrete
