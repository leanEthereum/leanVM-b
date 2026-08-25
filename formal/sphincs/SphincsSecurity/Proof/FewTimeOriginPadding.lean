import SphincsSecurity.Proof.FewTimeOriginProbability

/-!
# Padding few-time origin configurations

The viewed game pads signer views to `signatureLimit`. Origin configurations use the same embedding
on selected signer positions, while retaining the direct-query source assigned to every prehit.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

noncomputable def FewTimePattern.padSelectedEquiv {small large distinct : Nat}
    (pattern : FewTimePattern small distinct) (hle : small ≤ large) :
    pattern.selected ≃ (pattern.pad hle).selected := by
  classical
  let toPadded : pattern.selected → (pattern.pad hle).selected := fun selected =>
    ⟨finCastLEEmbedding hle selected.1,
      Finset.mem_map.2 ⟨selected.1, selected.2, rfl⟩⟩
  refine Equiv.ofBijective toPadded ⟨?_, ?_⟩
  · intro left right heq
    apply Subtype.ext
    exact (finCastLEEmbedding hle).injective (congrArg Subtype.val heq)
  · intro selected
    obtain ⟨position, hposition, heq⟩ := Finset.mem_map.1 selected.2
    refine ⟨⟨position, hposition⟩, Subtype.ext ?_⟩
    exact heq

theorem FewTimePattern.padSelectedEquiv_apply {small large distinct : Nat}
    (pattern : FewTimePattern small distinct) (hle : small ≤ large)
    (selected : pattern.selected) :
    (pattern.padSelectedEquiv hle selected).1 = finCastLEEmbedding hle selected.1 := rfl

noncomputable def OriginConfiguration.pad {small large distinct sources : Nat}
    {pattern : FewTimePattern small distinct} (configuration : OriginConfiguration pattern sources)
    (hle : small ≤ large) : OriginConfiguration (pattern.pad hle) sources := by
  classical
  let selectedEquiv := pattern.padSelectedEquiv hle
  let paddedPrehit := configuration.prehit.map selectedEquiv.toEmbedding
  let oldSelected : ↑paddedPrehit → ↑configuration.prehit := fun selected => by
    let old := selectedEquiv.symm selected.1
    have hold : old ∈ configuration.prehit := by
      obtain ⟨candidate, hcandidate, heq⟩ := Finset.mem_map.1 selected.2
      have hcandEq : candidate = old := by
        apply selectedEquiv.injective
        rw [selectedEquiv.apply_symm_apply]
        exact heq
      rwa [← hcandEq]
    exact ⟨old, hold⟩
  have holdInjective : Function.Injective oldSelected := by
    intro left right heq
    apply Subtype.ext
    apply selectedEquiv.symm.injective
    exact congrArg (fun selected : ↑configuration.prehit => selected.1) heq
  refine ⟨paddedPrehit, ⟨fun selected => configuration.source.1 (oldSelected selected), ?_⟩⟩
  exact Function.Injective.comp configuration.source.2 holdInjective

theorem OriginConfiguration.mem_pad_prehit_iff {small large distinct sources : Nat}
    {pattern : FewTimePattern small distinct} (configuration : OriginConfiguration pattern sources)
    (hle : small ≤ large) (selected : pattern.selected) :
    pattern.padSelectedEquiv hle selected ∈ (configuration.pad hle).prehit ↔
      selected ∈ configuration.prehit := by
  classical
  simp [OriginConfiguration.pad]

theorem OriginConfiguration.pad_prehit_card {small large distinct sources : Nat}
    {pattern : FewTimePattern small distinct} (configuration : OriginConfiguration pattern sources)
    (hle : small ≤ large) :
    (configuration.pad hle).prehit.card = configuration.prehit.card := by
  classical
  simp [OriginConfiguration.pad]

theorem OriginConfiguration.pad_source_apply {small large distinct sources : Nat}
    {pattern : FewTimePattern small distinct} (configuration : OriginConfiguration pattern sources)
    (hle : small ≤ large) (selected : pattern.selected)
    (hselected : selected ∈ configuration.prehit) :
    (configuration.pad hle).source.1
        ⟨pattern.padSelectedEquiv hle selected,
          (configuration.mem_pad_prehit_iff hle selected).2 hselected⟩ =
      configuration.source.1 ⟨selected, hselected⟩ := by
  classical
  simp only [OriginConfiguration.pad]
  apply congrArg configuration.source.1
  apply Subtype.ext
  exact (pattern.padSelectedEquiv hle).symm_apply_apply selected

def OriginConfiguration.PaddedRealizedBy {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    {q limit : Nat} (hle : signingLog.length ≤ limit)
    (configuration : OriginConfiguration (cover.pattern.pad hle) q)
    (trace : FullAdversaryTrace) (hlog : trace.signing.toSigningLog = signingLog) : Prop :=
  (∀ selected : cover.pattern.selected,
      cover.pattern.padSelectedEquiv hle selected ∈ configuration.prehit ↔
        cover.EntryDigestPrecached trace.signing hlog
          (cover.entriesEquivPatternSelected.symm selected))
    ∧ ∀ entry : cover.PrecachedEntries trace.signing hlog,
      ∀ hselected : cover.pattern.padSelectedEquiv hle
          (cover.entriesEquivPatternSelected entry.1) ∈ configuration.prehit,
      ∃ (output : HashOutput)
          (sourcePosition : Fin trace.hashQueries.length)
          (intervalPosition : Fin trace.intervals.length)
          (selectedIntervalPosition : Fin trace.intervals.length)
          (hdirect : isDirectHashQuery (trace.intervals.get intervalPosition).input),
        sourcePosition.val =
            (configuration.source.1
              ⟨cover.pattern.padSelectedEquiv hle
                (cover.entriesEquivPatternSelected entry.1), hselected⟩).val
          ∧ sourcePosition.val =
            (Fin.encodeSubtype (fun position =>
              isDirectHashQuery (trace.intervals.get position).input)
              ⟨intervalPosition, hdirect⟩).val
          ∧ intervalPosition.val < selectedIntervalPosition.val
          ∧ AdversaryCacheEntry.signingEntry?
            (trace.intervals.get selectedIntervalPosition) =
              some (cover.cacheEntry trace.signing hlog entry.1)
          ∧ (trace.intervals.get intervalPosition).input =
            .inl (.inr (cover.entryDigestInput entry.1))
          ∧ (trace.intervals.get intervalPosition).initialCache
            (cover.entryDigestInput entry.1) = none
          ∧ (output, (trace.intervals.get intervalPosition).finalCache) ∈ support
            ((randomOracle (cover.entryDigestInput entry.1)).run
              (trace.intervals.get intervalPosition).initialCache)
          ∧ signAttemptResultOfOutput output ≠ none
          ∧ hashOutputFewTimeView output = cover.entryView entry.1

theorem OriginConfiguration.RealizedBy.pad {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    {cover : FewTimeCover f cache secretKey signingLog index targetLeaves}
    {q limit : Nat} {configuration : OriginConfiguration cover.pattern q}
    {trace : FullAdversaryTrace} {hlog : trace.signing.toSigningLog = signingLog}
    (hrealized : configuration.RealizedBy cover trace hlog)
    (hle : signingLog.length ≤ limit) :
    (configuration.pad hle).PaddedRealizedBy cover hle trace hlog := by
  constructor
  · intro selected
    rw [configuration.mem_pad_prehit_iff]
    exact hrealized.1 selected
  · intro entry hselected
    let selected := cover.entriesEquivPatternSelected entry.1
    have hold : selected ∈ configuration.prehit :=
      (configuration.mem_pad_prehit_iff hle selected).1 hselected
    obtain ⟨output, sourcePosition, intervalPosition, selectedIntervalPosition, hdirect,
      hsource, hordinal, hrest⟩ :=
      hrealized.2 entry hold
    refine ⟨output, sourcePosition, intervalPosition, selectedIntervalPosition, hdirect,
      ?_, hordinal, hrest⟩
    have hpadSource := configuration.pad_source_apply hle selected hold
    have hpadSource' :
        (configuration.pad hle).source.1
            ⟨cover.pattern.padSelectedEquiv hle selected, hselected⟩ =
          configuration.source.1 ⟨selected, hold⟩ := by
      convert hpadSource
    rw [hpadSource']
    exact hsource

theorem FewTimeCover.exists_paddedRealized_originConfiguration_of_queryBudget
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
      result.2.2.signing.toSigningLog index targetLeaves)
    (limit : Nat) (hle : result.2.2.signing.toSigningLog.length ≤ limit) :
    ∃ configuration : OriginConfiguration (cover.pattern.pad hle) q,
      configuration.PaddedRealizedBy cover hle result.2.2 rfl := by
  obtain ⟨configuration, hrealized⟩ :=
    cover.exists_realized_originConfiguration_of_queryBudget adversary q hq parameter
      hparameter otsSecret hots ftsSecret hfts result hresult f hf index targetLeaves
  exact ⟨configuration.pad hle, hrealized.pad hle⟩

end SphincsSecurity.Concrete
