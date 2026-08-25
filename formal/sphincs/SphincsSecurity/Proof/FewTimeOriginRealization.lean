import SphincsSecurity.Proof.FewTimeNumberedSources

/-!
# Concrete realization of an origin configuration

A realized configuration identifies each selected prehit with its exact direct hash-query slot and
with the fresh full-trace interval that produced the cached answer.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def OriginConfiguration.RealizedBy {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    {q : Nat} (configuration : OriginConfiguration cover.pattern q)
    (trace : FullAdversaryTrace) (hlog : trace.signing.toSigningLog = signingLog) : Prop :=
  (∀ selected : cover.pattern.selected,
      selected ∈ configuration.prehit ↔
        cover.EntryDigestPrecached trace.signing hlog
          (cover.entriesEquivPatternSelected.symm selected))
    ∧ ∀ entry : cover.PrecachedEntries trace.signing hlog,
      ∀ hselected : cover.entriesEquivPatternSelected entry.1 ∈ configuration.prehit,
      ∃ (output : HashOutput)
          (sourcePosition : Fin trace.hashQueries.length)
          (intervalPosition : Fin trace.intervals.length)
          (selectedIntervalPosition : Fin trace.intervals.length)
          (hdirect : isDirectHashQuery (trace.intervals.get intervalPosition).input),
        sourcePosition.val =
            (configuration.source.1
              ⟨cover.entriesEquivPatternSelected entry.1, hselected⟩).val
          ∧ sourcePosition.val =
            (Fin.encodeSubtype (fun position =>
              isDirectHashQuery (trace.intervals.get position).input)
              ⟨intervalPosition, hdirect⟩).val
          ∧ intervalPosition.val < selectedIntervalPosition.val
          ∧ AdversaryCacheEntry.signingEntry?
            (trace.intervals.get selectedIntervalPosition) =
              some (cover.cacheEntry trace.signing hlog entry.1)
          ∧ ((trace.intervals.take selectedIntervalPosition.val).filterMap
            AdversaryCacheEntry.signingEntry?).length = (cover.logIndex entry.1).val
          ∧ (trace.intervals.get intervalPosition).input =
            .inl (.inr (cover.entryDigestInput entry.1))
          ∧ (trace.intervals.get intervalPosition).initialCache
            (cover.entryDigestInput entry.1) = none
          ∧ (output, (trace.intervals.get intervalPosition).finalCache) ∈ support
            ((randomOracle (cover.entryDigestInput entry.1)).run
              (trace.intervals.get intervalPosition).initialCache)
          ∧ signAttemptResultOfOutput output ≠ none
          ∧ hashOutputFewTimeView output = cover.entryView entry.1

theorem FewTimeCover.exists_realized_originConfiguration_of_hashQueries_length_le
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
      OriginConfiguration.RealizedBy cover configuration result.2.2 rfl := by
  classical
  obtain ⟨source, intervalSource, selectedInterval, output, hsourceInjective,
      _hintervalInjective, hsource⟩ :=
    cover.precached_entries_have_injective_numbered_sources adversary parameter
    otsSecret ftsSecret result hresult f hf index targetLeaves
  let budgetSource : cover.PrecachedEntries result.2.2.signing rfl → Fin q :=
    fun entry => Fin.castLE hqueries (source entry)
  have hbudgetSourceInjective : Function.Injective budgetSource :=
    Function.Injective.comp (finCastLEEmbedding hqueries).injective hsourceInjective
  let configuration := cover.originConfiguration result.2.2.signing rfl q budgetSource
    hbudgetSourceInjective
  refine ⟨configuration, ?_, ?_⟩
  · intro selected
    exact cover.mem_precachedPatternSelected_iff result.2.2.signing rfl selected
  · intro entry hselected
    let selected : ↑configuration.prehit :=
      ⟨cover.entriesEquivPatternSelected entry.1, hselected⟩
    have hentry : cover.precachedOfPatternSelected result.2.2.signing rfl selected = entry := by
      apply Subtype.ext
      rw [cover.precachedOfPatternSelected_entry result.2.2.signing rfl selected]
      exact cover.entriesEquivPatternSelected.symm_apply_apply entry.1
    have hconfigurationSource : configuration.source.1 selected = budgetSource entry := by
      rw [cover.originConfiguration_source_apply result.2.2.signing rfl q budgetSource
        hbudgetSourceInjective selected, hentry]
    obtain ⟨hdirect, hordinal, hinterval⟩ := hsource entry
    refine ⟨output entry, source entry, intervalSource entry, selectedInterval entry,
      hdirect, ?_, hordinal, hinterval⟩
    · exact congrArg Fin.val hconfigurationSource |>.symm

theorem FewTimeCover.exists_realized_originConfiguration_of_queryBudget
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
      OriginConfiguration.RealizedBy cover configuration result.2.2 rfl := by
  exact cover.exists_realized_originConfiguration_of_hashQueries_length_le adversary parameter
    otsSecret ftsSecret result hresult f hf index targetLeaves q
    (gameAfterSecretsWithFullTrace_hashQueries_length_le adversary q hq parameter hparameter
      otsSecret hots ftsSecret hfts result hresult)

end SphincsSecurity.Concrete
