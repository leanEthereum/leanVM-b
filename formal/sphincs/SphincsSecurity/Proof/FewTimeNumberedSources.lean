import SphincsSecurity.Proof.FewTimeOriginSampler

/-!
# Numbering direct few-time sources

The full trace numbers every adversary interval, including signing calls and sampling queries. This
module gives selected prehits a separate injective numbering in the direct hash-query list, which is
the source index space used by the weighted sampler.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

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
  let equivalence := cover.entriesEquivPatternSelected
  let precached := cover.precachedEntryFinset trace hlog
  let selectedPrehits : Finset cover.pattern.selected :=
    precached.map equivalence.toEmbedding
  let asPrecached : ↑selectedPrehits → cover.PrecachedEntries trace hlog :=
    fun selected =>
      let entry := equivalence.symm selected.1
      ⟨entry, by
        have hmem : entry ∈ precached := by
          obtain ⟨original, horiginal, heq⟩ := Finset.mem_map.1 selected.2
          have horiginalEq : original = entry := by
            apply equivalence.injective
            rw [equivalence.apply_symm_apply]
            exact heq
          rw [← horiginalEq]
          exact horiginal
        exact (Finset.mem_filter.mp hmem).2⟩
  refine ⟨selectedPrehits, ⟨fun selected => source (asPrecached selected), ?_⟩⟩
  intro left right heq
  have hasPrecached : asPrecached left = asPrecached right := hsource heq
  apply Subtype.ext
  have hentries := congrArg (fun entry : cover.PrecachedEntries trace hlog => entry.1)
    hasPrecached
  exact equivalence.symm.injective hentries

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
  simp [FewTimeCover.originConfiguration]

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
        (output : cover.PrecachedEntries result.2.2.signing rfl → HashOutput),
      Function.Injective source
        ∧ Function.Injective intervalSource
        ∧ ∀ entry,
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
  classical
  obtain ⟨intervalSource, output, hintervalInjective, hinterval⟩ :=
    cover.precached_entries_have_injective_fresh_direct_view_sources adversary parameter
      otsSecret ftsSecret result hresult f hf index targetLeaves
  let directSource : cover.PrecachedEntries result.2.2.signing rfl →
      {position : Fin result.2.2.intervals.length //
        isDirectHashQuery (result.2.2.intervals.get position).input} :=
    fun entry => ⟨intervalSource entry, by rw [(hinterval entry).1]; trivial⟩
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
  exact ⟨source, intervalSource, output, hsourceInjective, hintervalInjective, hinterval⟩

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
  obtain ⟨numberedSource, _intervalSource, _output, hnumberedInjective, _, _⟩ :=
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

end SphincsSecurity.Concrete
