import SphincsSecurity.Proof.TerminalSampling

/-!
# Message-digest collision witnesses

A message-digest collision supplies one successful signer whose complete digest is the forged
digest. That signer alone is therefore a few-time cover. The distinct digest inputs make the
cover compatible with the existing target monitor.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def singletonOriginUnionBound (signatures sources : Nat) : ℝ≥0∞ :=
  ∑ pattern : FewTimePattern signatures 1,
    ∑ configuration : OriginConfiguration pattern sources,
      Pr[configuration.Hit |
        ($ᵗ configuration.Sample : ProbComp configuration.Sample)]

theorem singletonOriginUnionBound_eq (signatures sources : Nat) :
    singletonOriginUnionBound signatures sources =
      ∑ pattern : FewTimePattern signatures 1,
        originChoiceMass pattern.selected sources
            ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ *
          ((2 ^ 166 : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  rw [singletonOriginUnionBound]
  apply Finset.sum_congr rfl
  intro pattern _
  rw [sum_probEvent_originConfiguration_hit pattern]
  norm_num [totalHeight, ftsTreeHeight, ftsTrees]

theorem singletonOriginUnionBound_le_inv (q : Nat) (hq : q ≤ 2 ^ 120) :
    singletonOriginUnionBound signatureLimit q ≤
      ((2 ^ 141 : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  rw [singletonOriginUnionBound_eq]
  calc
    (∑ pattern : FewTimePattern signatureLimit 1,
        originChoiceMass pattern.selected q ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ *
          ((2 ^ 166 : Nat) : ℝ≥0∞)⁻¹) ≤
        ∑ _pattern : FewTimePattern signatureLimit 1,
          2 * ((2 ^ 166 : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro pattern _
      have hmass := pattern.originChoiceMass_le_two hq (by decide)
      simpa only [mul_comm] using
        (mul_le_mul_left hmass ((2 ^ 166 : Nat) : ℝ≥0∞)⁻¹)
    _ = (Fintype.card (FewTimePattern signatureLimit 1) : ℝ≥0∞) *
        (2 * ((2 ^ 166 : Nat) : ℝ≥0∞)⁻¹) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((2 ^ 141 : Nat) : ℝ≥0∞)⁻¹ := by
      have hcard : Fintype.card (FewTimePattern signatureLimit 1) = signatureLimit := by
        simp [fewTimePattern_card]
      rw [hcard, signatureLimit]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      norm_num

theorem probEvent_exists_singletonOriginConfiguration_fixedOrdinal_viewedEvent_le
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 120) (hcache : QueryCache.enncard initialCache ≤ q)
    (candidates : Nat)
    (viewedEvent : ∀ pattern : FewTimePattern signatures 1,
      OriginConfiguration pattern sources → Fin candidates →
        α × ViewedFullTraceState → Prop)
    (himp : ∀ (pattern : FewTimePattern signatures 1)
      (configuration : OriginConfiguration pattern sources) (candidate : Fin candidates)
      (result : α × OriginTargetMonitorState configuration),
      result ∈ support
        ((simulateQ
          (originTargetMonitoredAdversaryImpl configuration secretKey candidate.val)
          computation).run (OriginTargetMonitorState.initial configuration initialCache)) →
      viewedEvent pattern configuration candidate
          (result.1, result.2.origin.viewed) →
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            FixedFewTimePatternHit pattern.assignment
              (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q) :
    Pr[fun result => ∃ pattern : FewTimePattern signatures 1,
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin candidates,
          viewedEvent pattern configuration candidate result |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      candidates * singletonOriginUnionBound signatures sources := by
  classical
  let run := (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
    computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩
  calc
    Pr[fun result => ∃ pattern : FewTimePattern signatures 1,
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin candidates,
          viewedEvent pattern configuration candidate result | run] =
        Pr[fun result => ∃ pattern ∈
            (Finset.univ : Finset (FewTimePattern signatures 1)),
          ∃ configuration : OriginConfiguration pattern sources,
          ∃ candidate : Fin candidates,
            viewedEvent pattern configuration candidate result | run] := by
      congr 1
      funext result
      simp
    _ ≤ ∑ pattern : FewTimePattern signatures 1,
        Pr[fun result =>
          ∃ configuration : OriginConfiguration pattern sources,
          ∃ candidate : Fin candidates,
            viewedEvent pattern configuration candidate result | run] :=
      probEvent_exists_finset_le_sum Finset.univ run fun pattern result =>
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin candidates,
          viewedEvent pattern configuration candidate result
    _ ≤ ∑ pattern : FewTimePattern signatures 1,
        ∑ configuration : OriginConfiguration pattern sources,
          Pr[fun result => ∃ candidate : Fin candidates,
            viewedEvent pattern configuration candidate result | run] := by
      apply Finset.sum_le_sum
      intro pattern _
      calc
        _ = Pr[fun result => ∃ configuration ∈
              (Finset.univ : Finset (OriginConfiguration pattern sources)),
            ∃ candidate : Fin candidates,
              viewedEvent pattern configuration candidate result | run] := by
            congr 1
            funext result
            simp
        _ ≤ _ := probEvent_exists_finset_le_sum Finset.univ run fun configuration result =>
          ∃ candidate : Fin candidates,
            viewedEvent pattern configuration candidate result
    _ ≤ ∑ pattern : FewTimePattern signatures 1,
        ∑ configuration : OriginConfiguration pattern sources,
          candidates * Pr[configuration.Hit |
            ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
      apply Finset.sum_le_sum
      intro pattern _
      apply Finset.sum_le_sum
      intro configuration _
      exact probEvent_exists_fixedOrdinal_viewedEvent_le_ideal configuration secretKey
        computation initialCache q hq hcache candidates
          (viewedEvent pattern configuration) (himp pattern configuration)
    _ = candidates * singletonOriginUnionBound signatures sources := by
      rw [singletonOriginUnionBound]
      simp_rw [← Finset.mul_sum]

@[irreducible] def SomeFixedSingletonOriginTargetViewedTerminal
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q candidates : Nat)
    (result : α × ViewedFullTraceState) : Prop :=
  ∃ pattern : FewTimePattern signatures 1,
    ∃ configuration : OriginConfiguration pattern sources,
    ∃ candidate : Fin candidates,
      FixedOriginTargetViewedTerminal secretKey computation initialCache q
        configuration candidate.val result

noncomputable instance
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q candidates : Nat) :
    DecidablePred (SomeFixedSingletonOriginTargetViewedTerminal secretKey computation
      initialCache signatures sources q candidates) :=
  fun result => Classical.propDecidable
    (SomeFixedSingletonOriginTargetViewedTerminal secretKey computation initialCache
      signatures sources q candidates result)

theorem probEvent_someFixedSingletonOriginTargetViewedTerminal_le
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 120) (hcache : QueryCache.enncard initialCache ≤ q)
    (candidates : Nat) :
    Pr[SomeFixedSingletonOriginTargetViewedTerminal secretKey computation initialCache
        signatures sources q candidates |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      candidates * singletonOriginUnionBound signatures sources := by
  unfold SomeFixedSingletonOriginTargetViewedTerminal
  apply probEvent_exists_singletonOriginConfiguration_fixedOrdinal_viewedEvent_le
    secretKey computation initialCache signatures sources q hq hcache candidates
      (fun _ configuration candidate =>
        FixedOriginTargetViewedTerminal secretKey computation initialCache q
          configuration candidate.val)
  intro pattern configuration candidate result hresult hevent
  obtain ⟨hcacheFinal, hterminal⟩ := hevent
  obtain ⟨hcomplete, hhit⟩ := hterminal result hresult rfl
  exact ⟨hcomplete, hhit, hcacheFinal⟩

@[irreducible] def SomeFixedOneOriginTargetViewedTerminal
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q candidates : Nat)
    (result : α × ViewedFullTraceState) : Prop :=
  ∃ distinct : Nat, distinct = 1 ∧
    ∃ pattern : FewTimePattern signatures distinct,
    ∃ configuration : OriginConfiguration pattern sources,
    ∃ candidate : Fin candidates,
      FixedOriginTargetViewedTerminal secretKey computation initialCache q
        configuration candidate.val result

noncomputable instance
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q candidates : Nat) :
    DecidablePred (SomeFixedOneOriginTargetViewedTerminal secretKey computation
      initialCache signatures sources q candidates) :=
  fun result => Classical.propDecidable
    (SomeFixedOneOriginTargetViewedTerminal secretKey computation initialCache
      signatures sources q candidates result)

theorem someFixedOneOriginTargetViewedTerminal_iff
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q candidates : Nat)
    (result : α × ViewedFullTraceState) :
    SomeFixedOneOriginTargetViewedTerminal secretKey computation initialCache
        signatures sources q candidates result ↔
      SomeFixedSingletonOriginTargetViewedTerminal secretKey computation initialCache
        signatures sources q candidates result := by
  unfold SomeFixedOneOriginTargetViewedTerminal
    SomeFixedSingletonOriginTargetViewedTerminal
  constructor
  · rintro ⟨distinct, rfl, pattern, configuration, candidate, hterminal⟩
    exact ⟨pattern, configuration, candidate, hterminal⟩
  · rintro ⟨pattern, configuration, candidate, hterminal⟩
    exact ⟨1, rfl, pattern, configuration, candidate, hterminal⟩

theorem probEvent_someFixedOneOriginTargetViewedTerminal_le
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 120) (hcache : QueryCache.enncard initialCache ≤ q)
    (candidates : Nat) :
    Pr[SomeFixedOneOriginTargetViewedTerminal secretKey computation initialCache
        signatures sources q candidates |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      candidates * singletonOriginUnionBound signatures sources := by
  calc
    _ = Pr[SomeFixedSingletonOriginTargetViewedTerminal secretKey computation initialCache
          signatures sources q candidates |
        (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
          computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] := by
      congr 1
      funext result
      exact propext (someFixedOneOriginTargetViewedTerminal_iff secretKey computation
        initialCache signatures sources q candidates result)
    _ ≤ _ := probEvent_someFixedSingletonOriginTargetViewedTerminal_le
      secretKey computation initialCache signatures sources q hq hcache candidates

theorem SuccessfulSignRun.honest_fts_at_of_digest {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hrun : SuccessfulSignRun f cache secretKey message signature)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest secretKey.parameter secretKey.root message signature.randomness) = digest) :
    HonestFtsSignAt f cache secretKey message signature
      (digestIndex digest) (digestLeaves digest) := by
  obtain ⟨index, leaves, hhonest⟩ := hrun.honest_fts_at
  obtain ⟨_, actualDigest, hactualDigest, _, hindex, hleaves, _⟩ := hhonest.1.extract
  have hdigestEq : actualDigest = digest := hactualDigest.symm.trans hdigest
  simpa only [hindex, hleaves, hdigestEq] using hhonest

noncomputable def SuccessfulSignRun.singletonFewTimeCover {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {message : Message} {signature : Signature}
    (hrun : SuccessfulSignRun f cache secretKey message signature)
    (hentry : (⟨message, some signature⟩ : SigningEntry) ∈ signingLog)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest secretKey.parameter secretKey.root message signature.randomness) = digest) :
    FewTimeCover f cache secretKey signingLog (digestIndex digest) (digestLeaves digest) :=
  ⟨fun _ =>
    ⟨⟨message, some signature⟩, signature, digestLeaves digest, hentry, rfl, hrun,
      hrun.honest_fts_at_of_digest digest hdigest, rfl⟩⟩

@[simp] theorem SuccessfulSignRun.singletonFewTimeCover_entries {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {message : Message} {signature : Signature}
    (hrun : SuccessfulSignRun f cache secretKey message signature)
    (hentry : (⟨message, some signature⟩ : SigningEntry) ∈ signingLog)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest secretKey.parameter secretKey.root message signature.randomness) = digest) :
    (hrun.singletonFewTimeCover hentry digest hdigest).entries =
      {⟨message, some signature⟩} := by
  classical
  ext entry
  simp [FewTimeCover.entries, SuccessfulSignRun.singletonFewTimeCover, SigningEntry.flat,
    show Nonempty FtsTree from ⟨⟨0, by decide⟩⟩]

@[simp] theorem SuccessfulSignRun.singletonFewTimeCover_entries_card {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {message : Message} {signature : Signature}
    (hrun : SuccessfulSignRun f cache secretKey message signature)
    (hentry : (⟨message, some signature⟩ : SigningEntry) ∈ signingLog)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest secretKey.parameter secretKey.root message signature.randomness) = digest) :
    (hrun.singletonFewTimeCover hentry digest hdigest).entries.card = 1 := by
  rw [hrun.singletonFewTimeCover_entries hentry digest hdigest]
  simp

theorem SuccessfulSignRun.singletonFewTimeCover_entryDigestInput {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {message : Message} {signature : Signature}
    (hrun : SuccessfulSignRun f cache secretKey message signature)
    (hentry : (⟨message, some signature⟩ : SigningEntry) ∈ signingLog)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest secretKey.parameter secretKey.root message signature.randomness) = digest)
    (entry : (hrun.singletonFewTimeCover hentry digest hdigest).entries) :
    (hrun.singletonFewTimeCover hentry digest hdigest).entryDigestInput entry =
      tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message signature.randomness) := by
  classical
  simp only [FewTimeCover.entryDigestInput, SuccessfulSignRun.singletonFewTimeCover]

theorem MessageDigestCollision.exists_singletonFewTimeCover
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {forgery : Forgery}
    (hcollision : MessageDigestCollision f cache secretKey signingLog forgery)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest secretKey.parameter secretKey.root forgery.message
        forgery.signature.randomness) = digest) :
    ∃ cover : FewTimeCover f cache secretKey signingLog
        (digestIndex digest) (digestLeaves digest),
      cover.entries.card = 1 ∧
        ∀ entry : cover.entries,
          tweakableHashInput secretKey.parameter .message
              (messageDigestPayload secretKey.root forgery.message
                forgery.signature.randomness) ≠
            cover.entryDigestInput entry := by
  classical
  obtain ⟨entry, signature, hentry, hresponse, hrun, _, hinput, heval⟩ := hcollision
  have hflatEntry : (⟨entry.1, some signature⟩ : SigningEntry) ∈ signingLog := by
    have hentryEq : (⟨entry.1, some signature⟩ : SigningEntry) = entry := by
      cases entry with
      | mk request response =>
          simp only at hresponse ⊢
          subst response
          rfl
    rw [hentryEq]
    exact hentry
  have hsignedDigest : evalWithAnswerFn f
      (messageDigest secretKey.parameter secretKey.root entry.1 signature.randomness) = digest :=
    heval.trans hdigest
  let cover := hrun.singletonFewTimeCover hflatEntry digest hsignedDigest
  refine ⟨cover, hrun.singletonFewTimeCover_entries_card hflatEntry digest hsignedDigest, ?_⟩
  intro selected hsame
  have hselectedInput : cover.entryDigestInput selected =
      tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root entry.1 signature.randomness) := by
    dsimp only [cover]
    exact hrun.singletonFewTimeCover_entryDigestInput hflatEntry digest hsignedDigest selected
  apply hinput
  exact hselectedInput.symm.trans hsame.symm

theorem FewTimeCover.direct_target_not_configured_source_of_input_ne
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (targetInput : HashInput)
    (hne : ∀ entry : cover.entries, targetInput ≠ cover.entryDigestInput entry)
    {q limit : Nat} (hle : signingLog.length ≤ limit)
    (configuration : OriginConfiguration (cover.pattern.pad hle) q)
    (trace : FullAdversaryTrace) (hlog : trace.signing.toSigningLog = signingLog)
    (hrealized : configuration.PaddedRealizedBy cover hle trace hlog)
    (hvalid : trace.ValidIntervals secretKey)
    (position : Fin trace.intervals.length) (output : HashOutput)
    (initialCache finalCache : QueryCache HashSpec)
    (hinterval : trace.intervals.get position =
      ⟨.inl (.inr targetInput), output, initialCache, finalCache⟩) :
    configuration.sourceAt?
      (directIntervalCount (trace.intervals.take position.val)) = none := by
  classical
  cases hsource : configuration.sourceAt?
      (directIntervalCount (trace.intervals.take position.val)) with
  | none => rfl
  | some selected =>
      exfalso
      have hgood := configuration.paddedRealized_direct_good hrealized hvalid position
        targetInput output initialCache finalCache hinterval
        (directIntervalCount (trace.intervals.take position.val)) rfl selected hsource
      apply hne (cover.paddedEntry hle selected.1)
      simpa only [FewTimeCover.paddedExpectedInputs] using hgood.1

theorem FewTimeCover.signer_target_not_selectedAt_of_input_ne
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (state : ViewedFullTraceState) (hlog : state.trace.signing.toSigningLog = signingLog)
    (hvalidViews : state.ValidViews secretKey) (hconsistent : state.trace.Consistent)
    (hcaches : state.trace.signing.CachesLe cache) (hf : cache.AgreesWithFn f)
    {limit : Nat} (hle : signingLog.length ≤ limit)
    (position : Fin state.trace.intervals.length) (request : SignRequest)
    (signature : Option Signature) (initialCache finalCache : QueryCache HashSpec)
    (hinterval : state.trace.intervals.get position =
      ⟨.inr request, signature, initialCache, finalCache⟩)
    (targetPayload : HashInput) (output : HashOutput)
    (hbefore : initialCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = none)
    (hafter : finalCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = some output)
    (houtput : signAttemptResultOfOutput output = some (index, targetLeaves))
    (hne : ∀ entry : cover.entries,
      tweakableHashInput secretKey.parameter .message targetPayload ≠
        cover.entryDigestInput entry) :
    (cover.pattern.pad hle).selectedAt?
      (signerIntervalCount (state.trace.intervals.take position.val)) = none := by
  classical
  cases hselected : (cover.pattern.pad hle).selectedAt?
      (signerIntervalCount (state.trace.intervals.take position.val)) with
  | none => rfl
  | some selected =>
      exfalso
      have hrank : signerIntervalCount (state.trace.intervals.take position.val) =
          selected.1.val :=
        ((cover.pattern.pad hle).selectedAt?_eq_some_iff _ selected).mp hselected |>.symm
      have hsigner := cover.originReplayEvents_get_signer state hlog hvalidViews hconsistent
        hcaches hf hle selected position request signature initialCache finalCache hinterval hrank
      let entry := cover.paddedEntry hle selected
      let selectedEntry := cover.select (cover.representativeTree entry)
      obtain ⟨signingPosition, viewPosition, _, _, _, hviewRun⟩ :=
        ViewedFullTraceState.ValidViews.signer_interval hvalidViews hconsistent position
          request signature initialCache finalCache hinterval
      obtain ⟨randomness, hpayload, _, hrandomness⟩ :=
        signingCacheEntry_validView_fresh_admissible_transition_view hviewRun targetPayload
          output index targetLeaves hbefore hafter houtput
      have hfields := cover.cacheEntry_request_signature state.trace.signing hlog entry
      have hrequest : request = selectedEntry.entry.1 := by
        calc
          request = (cover.cacheEntry state.trace.signing hlog entry).request :=
            congrArg SigningCacheEntry.request hsigner.2
          _ = selectedEntry.entry.1 := hfields.1
      have hsignature : signature = some selectedEntry.signature := by
        calc
          signature = (cover.cacheEntry state.trace.signing hlog entry).signature :=
            congrArg SigningCacheEntry.signature hsigner.2
          _ = some selectedEntry.signature := hfields.2
      have hrandomness' : randomness = selectedEntry.signature.randomness :=
        hrandomness selectedEntry.signature hsignature
      apply hne entry
      apply congrArg (tweakableHashInput secretKey.parameter .message)
      rw [hpayload, hrequest, hrandomness']

theorem FewTimeCover.target_source_interval_allowed_of_input_ne
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (targetPayload : HashInput)
    (hne : ∀ entry : cover.entries,
      tweakableHashInput secretKey.parameter .message targetPayload ≠
        cover.entryDigestInput entry)
    (state : ViewedFullTraceState) (hlog : state.trace.signing.toSigningLog = signingLog)
    (hvalidViews : state.ValidViews secretKey) (hconsistent : state.trace.Consistent)
    (hcaches : state.trace.signing.CachesLe cache) (hf : cache.AgreesWithFn f)
    {q limit : Nat} (hle : signingLog.length ≤ limit)
    (configuration : OriginConfiguration (cover.pattern.pad hle) q)
    (hrealized : configuration.PaddedRealizedBy cover hle state.trace hlog)
    (hvalidIntervals : state.trace.ValidIntervals secretKey)
    (position : Fin state.trace.intervals.length) (output : HashOutput)
    (hbefore : (state.trace.intervals.get position).initialCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = none)
    (hafter : (state.trace.intervals.get position).finalCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = some output)
    (houtput : signAttemptResultOfOutput output = some (index, targetLeaves))
    (hkind : (state.trace.intervals.get position).input = .inl (.inr
        (tweakableHashInput secretKey.parameter .message targetPayload)) ∨
      ∃ request, (state.trace.intervals.get position).input = .inr request) :
    targetCandidateIntervalAllowed configuration state position = true := by
  let entry := state.trace.intervals.get position
  have hentry : state.trace.intervals.get position = entry := rfl
  rcases entry with ⟨entryInput, entryOutput, initialCache, finalCache⟩
  rw [hentry] at hbefore hafter hkind
  rcases hkind with hdirect | ⟨request, hsigner⟩
  · change entryInput = .inl (.inr
      (tweakableHashInput secretKey.parameter .message targetPayload)) at hdirect
    subst entryInput
    have hnone := cover.direct_target_not_configured_source_of_input_ne
      (tweakableHashInput secretKey.parameter .message targetPayload) hne hle
      configuration state.trace hlog hrealized hvalidIntervals position entryOutput
        initialCache finalCache hentry
    have hinputElem : state.trace.intervals[position.val].input = .inl (.inr
        (tweakableHashInput secretKey.parameter .message targetPayload)) := by
      simpa only [List.get_eq_getElem] using congrArg AdversaryCacheEntry.input hentry
    simp [targetCandidateIntervalAllowed, hinputElem, hnone]
  · change entryInput = .inr request at hsigner
    subst entryInput
    have hnone := cover.signer_target_not_selectedAt_of_input_ne state hlog hvalidViews
      hconsistent hcaches hf hle position request entryOutput initialCache finalCache hentry
        targetPayload output (by simpa using hbefore) (by simpa using hafter)
        (by simpa using houtput) hne
    have hinputElem : state.trace.intervals[position.val].input = .inr request := by
      simpa only [List.get_eq_getElem] using congrArg AdversaryCacheEntry.input hentry
    simp [targetCandidateIntervalAllowed, hinputElem, hnone]

theorem OriginConfiguration.target_monitored_complete_of_projection_for_cover
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.cache.AgreesWithFn f)
    (digest : MessageDigest)
    (cover : FewTimeCover f result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.trace.signing.toSigningLog (digestIndex digest) (digestLeaves digest))
    {limit sources : Nat} (hle : result.2.trace.signing.toSigningLog.length ≤ limit)
    (configuration : OriginConfiguration (cover.pattern.pad hle) sources)
    (hrealized : configuration.PaddedRealizedBy cover hle result.2.trace rfl)
    (source : Fin result.2.trace.intervals.length)
    (hcandidate : FreshTargetCandidate
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      (result.2.trace.intervals.get source))
    (hsourceView : targetCandidateIntervalView result.2 source =
      fewTimeTargetView (digestIndex digest) (digestLeaves digest))
    (hallowed : targetCandidateIntervalAllowed configuration result.2 source = true)
    (targetOrdinal : Nat)
    (htargetOrdinal : targetOrdinal = result.2.trace.intervals.countPBefore
      (fun entry => decide (FreshTargetCandidate
        ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ entry)) source.val)
    (rootCache : QueryCache HashSpec)
    (monitored : Forgery × OriginTargetMonitorState configuration)
    (hmonitored : monitored ∈ support
      ((simulateQ
        (originTargetMonitoredAdversaryImpl configuration
          ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ targetOrdinal)
        (adversary.main ⟨result.1.1, parameter⟩)).run
          (OriginTargetMonitorState.initial configuration rootCache)))
    (htrace : result.2.trace = monitored.2.origin.viewed.trace)
    (hviews : result.2.views = monitored.2.origin.viewed.views) :
    monitored.2.Complete ∧
      ∀ target, monitored.2.targetView = some target →
        FixedFewTimePatternHit (cover.pattern.pad hle).assignment
          (monitored.2.origin.observation.views, target) := by
  let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
  let monitoredPosition := castTracePosition result.2 monitored.2.origin.viewed
    htrace source
  have hcandidateMonitored : FreshTargetCandidate secretKey
      (monitored.2.origin.viewed.trace.intervals.get monitoredPosition) := by
    rw [get_castTracePosition result.2 monitored.2.origin.viewed htrace source]
    exact hcandidate
  have hviewMonitored : targetCandidateIntervalView monitored.2.origin.viewed
      monitoredPosition = fewTimeTargetView (digestIndex digest) (digestLeaves digest) := by
    rw [targetCandidateIntervalView_castTracePosition result.2
      monitored.2.origin.viewed htrace hviews source]
    exact hsourceView
  have hallowedMonitored : targetCandidateIntervalAllowed configuration
      monitored.2.origin.viewed monitoredPosition = true := by
    rw [targetCandidateIntervalAllowed_castTracePosition configuration result.2
      monitored.2.origin.viewed htrace source]
    exact hallowed
  have hbase : (result.1, result.2.base) ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
    rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
      support_map]
    exact ⟨result, hresult, rfl⟩
  have hinvariants := gameAfterSecretsWithFullTrace_support_invariants adversary
    parameter otsSecret ftsSecret (result.1, result.2.base) hbase
  have hintervals := gameAfterSecretsWithFullTrace_support_interval_invariants adversary
    parameter otsSecret ftsSecret (result.1, result.2.base) hbase
  have hvalidIntervals := gameAfterSecretsWithFullTrace_support_validIntervals adversary
    parameter otsSecret ftsSecret (result.1, result.2.base) hbase
  have htraceCoherent := originTargetMonitoredAdversaryImpl_candidateTraceCoherent
    configuration secretKey targetOrdinal (adversary.main ⟨result.1.1, parameter⟩)
    (OriginTargetMonitorState.initial configuration rootCache) monitored
    (OriginTargetMonitorState.candidateTraceCoherent_initial configuration secretKey rootCache)
    hmonitored
  have hallowedTraceCoherent :=
    originTargetMonitoredAdversaryImpl_candidateAllowedTraceCoherent
      configuration secretKey targetOrdinal (adversary.main ⟨result.1.1, parameter⟩)
      (OriginTargetMonitorState.initial configuration rootCache) monitored
      (OriginTargetMonitorState.candidateAllowedTraceCoherent_initial
        configuration secretKey rootCache)
      hmonitored
  have hviewsCoherent := originTargetMonitoredAdversaryImpl_candidateViewsCoherent
    configuration secretKey targetOrdinal (adversary.main ⟨result.1.1, parameter⟩)
    (OriginTargetMonitorState.initial configuration rootCache) monitored
    (OriginTargetMonitorState.candidateViewsCoherent_initial configuration rootCache
      targetOrdinal) hmonitored
  have hallowedCoherent := originTargetMonitoredAdversaryImpl_candidateAllowedCoherent
    configuration secretKey targetOrdinal (adversary.main ⟨result.1.1, parameter⟩)
    (OriginTargetMonitorState.initial configuration rootCache) monitored
    (OriginTargetMonitorState.candidateAllowedCoherent_initial configuration rootCache
      targetOrdinal) hmonitored
  have htargetOrdinalMonitored : targetOrdinal =
      monitored.2.origin.viewed.trace.intervals.countPBefore
        (fun entry => decide (FreshTargetCandidate secretKey entry))
          monitoredPosition.val := by
    rw [htargetOrdinal]
    rw [List.countPBefore_eq_countP_take, List.countPBefore_eq_countP_take,
      take_castTracePosition result.2 monitored.2.origin.viewed htrace source]
  obtain ⟨hlogMonitored, hrealizedMonitored⟩ :=
    configuration.paddedRealized_transport result.2.trace
      monitored.2.origin.viewed.trace htrace rfl hrealized
  have hvalidIntervalsMonitored :
      monitored.2.origin.viewed.trace.ValidIntervals secretKey := by
    rw [← htrace]
    exact hvalidIntervals
  have hchronologicalMonitored : FullAdversaryTrace.Chronological
      monitored.2.origin.viewed.trace.intervals := by
    rw [← htrace]
    exact hintervals.2.2
  have hcachesMonitored : monitored.2.origin.viewed.trace.signing.CachesLe
      result.2.cache := by
    rw [← htrace]
    exact hinvariants.2.1
  exact configuration.paddedRealized_target_complete_and_hit
    hlogMonitored hrealizedMonitored htraceCoherent.1 hvalidIntervalsMonitored
    hchronologicalMonitored hcachesMonitored hf monitoredPosition hcandidateMonitored
    hviewMonitored hallowedMonitored (by rwa [← htargetOrdinalMonitored])
    htraceCoherent.2 (by rwa [← htargetOrdinalMonitored]) hallowedTraceCoherent.2

theorem OriginConfiguration.verifierTarget_fixedTerminal_for_cover
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.cache.AgreesWithFn f)
    (digest : MessageDigest)
    (cover : FewTimeCover f result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.trace.signing.toSigningLog (digestIndex digest) (digestLeaves digest))
    {limit sources : Nat} (hle : result.2.trace.signing.toSigningLog.length ≤ limit)
    (configuration : OriginConfiguration (cover.pattern.pad hle) sources)
    (hrealized : configuration.PaddedRealizedBy cover hle result.2.trace rfl)
    (rootCache : QueryCache HashSpec) (state : ViewedFullTraceState)
    (hadversary : (result.1.2.1, state) ∈ support
      ((simulateQ (viewedFullTracedMappedAdversaryImpl
        ⟨parameter, result.1.1, otsSecret, ftsSecret⟩)
        (adversary.main ⟨result.1.1, parameter⟩)).run
          ⟨rootCache, ⟨[], [], []⟩, [], none⟩))
    (htrace : result.2.trace = state.trace) (hviews : result.2.views = state.views)
    (input : HashInput) (output : HashOutput) (digestCache : QueryCache HashSpec)
    (hinput : input = tweakableHashInput parameter .message
      (messageDigestPayload result.1.1 result.1.2.1.message
        result.1.2.1.signature.randomness))
    (hmiss : state.cache input = none)
    (hquery : (output, digestCache) ∈ support ((randomOracle input).run state.cache))
    (_hdigestCache : digestCache ≤ result.2.cache)
    (htargetView : hashOutputFewTimeView output =
      fewTimeTargetView (digestIndex digest) (digestLeaves digest))
    (q : Nat) (hcache : QueryCache.enncard digestCache ≤ q) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    let publicKey : PublicKey := ⟨result.1.1, parameter⟩
    let appended := appendTargetViewedState (.inl (.inr input)) state.cache output
      digestCache none state
    let targetOrdinal := freshTargetCandidateCount secretKey state.trace
    FixedOriginTargetViewedTerminal secretKey
      (adversaryWithTargetQuery adversary publicKey) rootCache q configuration
        targetOrdinal ((result.1.2.1, output), appended) := by
  classical
  let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
  let publicKey : PublicKey := ⟨result.1.1, parameter⟩
  let appended := appendTargetViewedState (.inl (.inr input)) state.cache output
    digestCache none state
  let targetOrdinal := freshTargetCandidateCount secretKey state.trace
  have haugmented : ((result.1.2.1, output), appended) ∈ support
      ((simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        (adversaryWithTargetQuery adversary publicKey)).run
          ⟨rootCache, ⟨[], [], []⟩, [], none⟩) := by
    subst input
    exact adversaryWithTargetQuery_viewed_support adversary publicKey secretKey
      rootCache result.1.2.1 state hadversary output digestCache hquery
  refine ⟨hcache, ?_⟩
  intro monitored hmonitored heq
  have hstateEq : monitored.2.origin.viewed = appended := congrArg Prod.snd heq
  have hstateTraceEq : appended.trace = monitored.2.origin.viewed.trace :=
    congrArg ViewedFullTraceState.trace hstateEq.symm
  have hstateViewsEq : appended.views = monitored.2.origin.viewed.views :=
    congrArg ViewedFullTraceState.views hstateEq.symm
  let appendedPosition : Fin appended.trace.intervals.length :=
    ⟨state.trace.intervals.length, by
      simp [appended, appendTargetViewedState, fullAdversaryTraceUpdate]⟩
  let monitoredPosition := castTracePosition appended monitored.2.origin.viewed
    hstateTraceEq appendedPosition
  have hcandidateEntry : FreshTargetCandidate secretKey
      (⟨.inl (.inr input), output, state.cache, digestCache⟩ : AdversaryCacheEntry) := by
    exact (freshTargetCandidate_direct_iff secretKey input output state.cache digestCache
      hquery).2 hmiss
  have hcandidate : FreshTargetCandidate secretKey
      (appended.trace.intervals.get appendedPosition) := by
    simpa [appendedPosition, appended, appendTargetViewedState,
      fullAdversaryTraceUpdate] using hcandidateEntry
  have hcandidateMonitored : FreshTargetCandidate secretKey
      (monitored.2.origin.viewed.trace.intervals.get monitoredPosition) := by
    rw [get_castTracePosition appended monitored.2.origin.viewed hstateTraceEq
      appendedPosition]
    exact hcandidate
  have hvalidViewsState : state.ValidViews secretKey := by
    have hvalid := gameAfterSecretsWithViewTrace_support_validViews adversary parameter
      otsSecret ftsSecret result hresult
    simpa only [ViewedFullTraceState.ValidViews, htrace, hviews] using hvalid
  have hbase : (result.1, result.2.base) ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
    rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
      support_map]
    exact ⟨result, hresult, rfl⟩
  have hgameIntervals := gameAfterSecretsWithFullTrace_support_interval_invariants adversary
    parameter otsSecret ftsSecret (result.1, result.2.base) hbase
  have hconsistentState : state.trace.Consistent := by
    rw [← htrace]
    exact hgameIntervals.1
  have hview : targetCandidateIntervalView appended appendedPosition =
      fewTimeTargetView (digestIndex digest) (digestLeaves digest) := by
    rw [targetCandidateIntervalView_appendTargetViewedState_last secretKey state
      hvalidViewsState hconsistentState]
    exact htargetView
  have hviewMonitored : targetCandidateIntervalView monitored.2.origin.viewed
      monitoredPosition = fewTimeTargetView (digestIndex digest) (digestLeaves digest) := by
    rw [targetCandidateIntervalView_castTracePosition appended
      monitored.2.origin.viewed hstateTraceEq hstateViewsEq appendedPosition]
    exact hview
  have hsourceNone := configuration.paddedRealized_sourceAt_directIntervalCount_eq_none
    hrealized
  have hallowed : targetCandidateIntervalAllowed configuration appended appendedPosition = true := by
    rw [targetCandidateIntervalAllowed_appendTargetViewedState_last configuration state
      (.inl (.inr input)) state.cache output digestCache none]
    simpa only [decide_eq_true_eq, htrace] using hsourceNone
  have hallowedMonitored : targetCandidateIntervalAllowed configuration
      monitored.2.origin.viewed monitoredPosition = true := by
    rw [targetCandidateIntervalAllowed_castTracePosition configuration appended
      monitored.2.origin.viewed hstateTraceEq appendedPosition]
    exact hallowed
  have htraceCoherent := originTargetMonitoredAdversaryImpl_candidateTraceCoherent
    configuration secretKey targetOrdinal (adversaryWithTargetQuery adversary publicKey)
    (OriginTargetMonitorState.initial configuration rootCache) monitored
    (OriginTargetMonitorState.candidateTraceCoherent_initial configuration secretKey rootCache)
    hmonitored
  have hallowedTraceCoherent :=
    originTargetMonitoredAdversaryImpl_candidateAllowedTraceCoherent
      configuration secretKey targetOrdinal (adversaryWithTargetQuery adversary publicKey)
      (OriginTargetMonitorState.initial configuration rootCache) monitored
      (OriginTargetMonitorState.candidateAllowedTraceCoherent_initial
        configuration secretKey rootCache) hmonitored
  have hviewsCoherent := originTargetMonitoredAdversaryImpl_candidateViewsCoherent
    configuration secretKey targetOrdinal (adversaryWithTargetQuery adversary publicKey)
    (OriginTargetMonitorState.initial configuration rootCache) monitored
    (OriginTargetMonitorState.candidateViewsCoherent_initial configuration rootCache
      targetOrdinal) hmonitored
  have hallowedCoherent := originTargetMonitoredAdversaryImpl_candidateAllowedCoherent
    configuration secretKey targetOrdinal (adversaryWithTargetQuery adversary publicKey)
    (OriginTargetMonitorState.initial configuration rootCache) monitored
    (OriginTargetMonitorState.candidateAllowedCoherent_initial configuration rootCache
      targetOrdinal) hmonitored
  have htargetOrdinal : targetOrdinal =
      monitored.2.origin.viewed.trace.intervals.countPBefore
        (fun entry => decide (FreshTargetCandidate secretKey entry))
          monitoredPosition.val := by
    change freshTargetCandidateCount secretKey state.trace = _
    rw [List.countPBefore_eq_countP_take,
      take_castTracePosition appended monitored.2.origin.viewed hstateTraceEq appendedPosition]
    simp [appendedPosition, appended, appendTargetViewedState, fullAdversaryTraceUpdate,
      freshTargetCandidateCount]
  obtain ⟨hlogState, hrealizedState⟩ :=
    configuration.paddedRealized_transport result.2.trace state.trace htrace rfl hrealized
  obtain ⟨hlogAppended, hrealizedAppended⟩ :=
    configuration.paddedRealized_append_direct state hlogState hrealizedState
      input output digestCache
  obtain ⟨hlogMonitored, hrealizedMonitored⟩ :=
    configuration.paddedRealized_transport appended.trace
      monitored.2.origin.viewed.trace hstateTraceEq hlogAppended hrealizedAppended
  have haugmentedIntervals := viewedFullTracedMappedAdversaryImpl_interval_invariants
    secretKey (adversaryWithTargetQuery adversary publicKey) rootCache
      ((result.1.2.1, output), appended) haugmented
  have haugmentedValid := viewedFullTracedMappedAdversaryImpl_validIntervals
    secretKey (adversaryWithTargetQuery adversary publicKey) rootCache
      ((result.1.2.1, output), appended) haugmented
  have hcaches : appended.trace.signing.CachesLe result.2.cache := by
    have hcachesState : state.trace.signing.CachesLe result.2.cache := by
      rw [← htrace]
      exact (gameAfterSecretsWithFullTrace_support_invariants adversary parameter
        otsSecret ftsSecret (result.1, result.2.base) hbase).2.1
    simpa [appended, appendTargetViewedState, fullAdversaryTraceUpdate,
      signingCacheTraceUpdate] using hcachesState
  have hvalidIntervalsMonitored :
      monitored.2.origin.viewed.trace.ValidIntervals secretKey := by
    rw [← hstateTraceEq]
    exact haugmentedValid
  have hchronologicalMonitored : FullAdversaryTrace.Chronological
      monitored.2.origin.viewed.trace.intervals := by
    rw [← hstateTraceEq]
    exact haugmentedIntervals.2.2
  have hcachesMonitored : monitored.2.origin.viewed.trace.signing.CachesLe
      result.2.cache := by
    rw [← hstateTraceEq]
    exact hcaches
  exact configuration.paddedRealized_target_complete_and_hit
    hlogMonitored hrealizedMonitored htraceCoherent.1
    hvalidIntervalsMonitored hchronologicalMonitored hcachesMonitored hf
    monitoredPosition hcandidateMonitored hviewMonitored hallowedMonitored
    (by rwa [← htargetOrdinal]) htraceCoherent.2
    (by rwa [← htargetOrdinal]) hallowedTraceCoherent.2

theorem gameAfterSecretsWithViewTrace_singletonCover_target_classified_at_adversary_state
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
    (cover : FewTimeCover f result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.trace.signing.toSigningLog (digestIndex digest) (digestLeaves digest))
    (hcard : cover.entries.card = 1)
    (hne : ∀ entry : cover.entries,
      tweakableHashInput parameter .message
          (messageDigestPayload result.1.1 result.1.2.1.message
            result.1.2.1.signature.randomness) ≠
        cover.entryDigestInput entry)
    (hle : result.2.trace.signing.toSigningLog.length ≤ signatureLimit)
    (rootCache : QueryCache HashSpec) (state : ViewedFullTraceState)
    (htrace : result.2.trace = state.trace) (hviews : result.2.views = state.views)
    (hstateCache : state.cache ≤ result.2.cache) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    VerifierFreshTarget parameter result ∨
      ∃ (distinct : Nat), distinct = 1 ∧
      ∃ (pattern : FewTimePattern signatureLimit distinct)
          (configuration : OriginConfiguration pattern q) (candidate : Fin q),
        FixedOriginTargetViewedTerminal secretKey
          (adversary.main ⟨result.1.1, parameter⟩) rootCache q
            configuration candidate.val (result.1.2.1, state) := by
  classical
  let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
  let targetPayload := messageDigestPayload result.1.1 result.1.2.1.message
    result.1.2.1.signature.randomness
  let targetInput := tweakableHashInput parameter .message targetPayload
  obtain ⟨sourceRootCache, adversaryCache, digestCache, output, hrootNone, hchain, hquery,
      hdigestLe, htargetView, horigin, _⟩ :=
    gameAfterSecretsWithViewTrace_target_source_kind adversary parameter otsSecret
      ftsSecret result hresult
  rcases horigin with hverifier | ⟨source, hsourceInitial, hsourceFinal, hkind⟩
  · exact Or.inl ⟨sourceRootCache, adversaryCache, digestCache, output,
      hrootNone, hchain, by simpa only [targetInput, targetPayload] using hverifier,
      by simpa only [targetInput, targetPayload] using hquery, hdigestLe, htargetView⟩
  · obtain ⟨sourceOutput, hcandidate, hsourceView, hsourceOutput, hattempt⟩ :=
      gameAfterSecretsWithViewTrace_target_source_candidate adversary parameter otsSecret
        ftsSecret result hresult f hf digest hdigest hadmissible source
          (by simpa only [targetInput, targetPayload] using hsourceInitial)
          (by simpa only [targetInput, targetPayload] using hsourceFinal)
          (by simpa only [targetInput, targetPayload] using hkind)
    have hbase : (result.1, result.2.base) ∈ support
        (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
      rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
        support_map]
      exact ⟨result, hresult, rfl⟩
    obtain ⟨configuration, hrealized⟩ :=
      cover.exists_paddedRealized_originConfiguration_of_queryBudget
        adversary q hq parameter hparameter otsSecret hots ftsSecret hfts
          (result.1, result.2.base) hbase f hf (digestIndex digest) (digestLeaves digest)
          signatureLimit hle
    have hinvariants := gameAfterSecretsWithFullTrace_support_invariants adversary
      parameter otsSecret ftsSecret (result.1, result.2.base) hbase
    have hintervals := gameAfterSecretsWithFullTrace_support_interval_invariants adversary
      parameter otsSecret ftsSecret (result.1, result.2.base) hbase
    have hvalidIntervals := gameAfterSecretsWithFullTrace_support_validIntervals adversary
      parameter otsSecret ftsSecret (result.1, result.2.base) hbase
    have hvalidViews := gameAfterSecretsWithViewTrace_support_validViews adversary parameter
      otsSecret ftsSecret result hresult
    have hallowed : targetCandidateIntervalAllowed configuration result.2 source = true :=
      cover.target_source_interval_allowed_of_input_ne targetPayload hne result.2 rfl
        hvalidViews hintervals.1 hinvariants.2.1 hf hle configuration hrealized
          hvalidIntervals source sourceOutput
          (by simpa only [targetInput, targetPayload] using hsourceInitial)
          (by simpa only [targetInput, targetPayload] using hsourceOutput)
          hattempt (by simpa only [targetInput, targetPayload] using hkind)
    let targetOrdinal := result.2.trace.intervals.countPBefore
      (fun entry => decide (FreshTargetCandidate secretKey entry)) source.val
    have hordinalLt : targetOrdinal < freshTargetCandidateCount secretKey result.2.trace := by
      apply List.countPBefore_lt_countP_of_lt_length_of_pos
      exact decide_eq_true hcandidate
    have hcountLe : freshTargetCandidateCount secretKey result.2.trace ≤ q := by
      rw [freshTargetCandidateCount_eq_card]
      have hbound := gameAfterSecretsWithViewTrace_freshTargetCandidatePositions_card_le
        adversary q hq parameter hparameter otsSecret hots ftsSecret hfts result hresult
      exact_mod_cast hbound
    let candidate : Fin q := ⟨targetOrdinal, hordinalLt.trans_le hcountLe⟩
    have hfinalCache : QueryCache.enncard result.2.cache ≤ q :=
      gameAfterSecretsWithFullTrace_support_enncard_le adversary q hq parameter hparameter
        otsSecret hots ftsSecret hfts (result.1, result.2.base) hbase
    have hviewedCache : QueryCache.enncard state.cache ≤ q :=
      (QueryCache.enncard_mono hstateCache).trans hfinalCache
    refine Or.inr ⟨cover.entries.card, hcard, cover.pattern.pad hle,
      configuration, candidate, hviewedCache, ?_⟩
    intro monitored hmonitored heq
    have hstateEq : monitored.2.origin.viewed = state := congrArg Prod.snd heq
    have htrace' : result.2.trace = monitored.2.origin.viewed.trace := by
      rw [hstateEq]
      exact htrace
    have hviews' : result.2.views = monitored.2.origin.viewed.views := by
      rw [hstateEq]
      exact hviews
    exact configuration.target_monitored_complete_of_projection_for_cover adversary parameter
      otsSecret ftsSecret result hresult f hf digest cover hle hrealized source
      hcandidate hsourceView hallowed targetOrdinal rfl rootCache monitored hmonitored
      htrace' hviews'

theorem gameAfterSecretsWithViewTrace_singletonCover_target_classified
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
    (cover : FewTimeCover f result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.trace.signing.toSigningLog (digestIndex digest) (digestLeaves digest))
    (hcard : cover.entries.card = 1)
    (hne : ∀ entry : cover.entries,
      tweakableHashInput parameter .message
          (messageDigestPayload result.1.1 result.1.2.1.message
            result.1.2.1.signature.randomness) ≠
        cover.entryDigestInput entry)
    (hle : result.2.trace.signing.toSigningLog.length ≤ signatureLimit) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    VerifierFreshTarget parameter result ∨
      ∃ (rootCache : QueryCache HashSpec) (state : ViewedFullTraceState)
          (distinct : Nat), distinct = 1 ∧
      ∃ (pattern : FewTimePattern signatureLimit distinct)
          (configuration : OriginConfiguration pattern q) (candidate : Fin q),
        (result.1.2.1, state) ∈ support
          ((simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
            (adversary.main ⟨result.1.1, parameter⟩)).run
              ⟨rootCache, ⟨[], [], []⟩, [], none⟩) ∧
        FixedOriginTargetViewedTerminal secretKey
          (adversary.main ⟨result.1.1, parameter⟩) rootCache q
            configuration candidate.val (result.1.2.1, state) := by
  obtain ⟨rootCache, state, _, hadversary, htrace, hviews, hstateCache⟩ :=
    gameAfterSecretsWithViewTrace_support_adversary_state adversary parameter otsSecret
      ftsSecret result hresult
  rcases gameAfterSecretsWithViewTrace_singletonCover_target_classified_at_adversary_state
      adversary q hq parameter hparameter otsSecret hots ftsSecret hfts result hresult
      f hf digest hdigest hadmissible cover hcard hne hle rootCache state htrace
      hviews hstateCache with hfresh | hclassified
  · exact Or.inl hfresh
  · obtain ⟨distinct, hdistinct, pattern, configuration, candidate, hterminal⟩ :=
      hclassified
    exact Or.inr ⟨rootCache, state, distinct, hdistinct, pattern, configuration,
      candidate, hadversary, hterminal⟩

theorem probEvent_gameRestWithViewTrace_nonfresh_messageCollision_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 120)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (root : Digest) (rootCache : QueryCache HashSpec)
    (hroot : (root, rootCache) ∈ support
      ((simulateQ romImpl
        (liftM ((treeRoot parameter topLayer rootTree
          (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
            OracleComp OracleWorld Digest)).run ∅)) :
    Pr[fun rest =>
        let result : (Digest × Forgery × Bool) × ViewedFullTraceState :=
          ((root, rest.1.1, rest.1.2), rest.2)
        ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          ¬VerifierFreshTarget parameter result |
      gameRestWithViewTrace adversary ⟨root, parameter⟩
        ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache] ≤
      q * singletonOriginUnionBound signatureLimit q := by
  classical
  let secretKey : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
  let publicKey : PublicKey := ⟨root, parameter⟩
  let initialState : ViewedFullTraceState :=
    ⟨rootCache, ⟨[], [], []⟩, [], none⟩
  let run := (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
    (adversary.main publicKey)).run initialState
  let finish : Forgery × ViewedFullTraceState →
      ProbComp ((Forgery × Bool) × ViewedFullTraceState) := fun prior => do
    let ((verified, targetView), finalCache) ←
      (simulateQ romImpl
        (liftM (verifyWithView publicKey prior.1.message prior.1.signature) :
          OracleComp OracleWorld (Bool × FewTimeView))).run prior.2.cache
    let log := prior.2.trace.signing.toSigningLog
    let verdict := decide (SigningTranscript.Valid log ∧
      ¬SigningTranscript.Contains log prior.1) && verified
    pure ((prior.1, verdict),
      ⟨finalCache, prior.2.trace, prior.2.views, some targetView⟩)
  let prefixEvent := fun prior : Forgery × ViewedFullTraceState =>
    SomeFixedSingletonOriginTargetViewedTerminal secretKey
      (adversary.main publicKey) rootCache signatureLimit q q q prior
  have hgame : gameRestWithViewTrace adversary publicKey secretKey rootCache =
      run >>= finish := by
    rfl
  rw [show ⟨root, parameter⟩ = publicKey from rfl,
    show ⟨parameter, root, otsSecret, ftsSecret⟩ = secretKey from rfl, hgame]
  calc
    _ ≤ Pr[prefixEvent | run] := by
      apply probEvent_bind_le_probEvent
      intro prior hprior hnotPrefix
      rcases prior with ⟨forgery, state⟩
      apply probEvent_eq_zero
      intro rest hrest hevent
      rw [mem_support_bind_iff] at hrest
      obtain ⟨⟨⟨verified, targetView⟩, finalCache⟩, hverify, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst rest
      let result : (Digest × Forgery × Bool) × ViewedFullTraceState :=
        ((root, forgery,
          decide (SigningTranscript.Valid state.trace.signing.toSigningLog ∧
            ¬SigningTranscript.Contains state.trace.signing.toSigningLog forgery) &&
              verified),
          ⟨finalCache, state.trace, state.views, some targetView⟩)
      have hrestSupport :
          ((forgery,
              decide (SigningTranscript.Valid state.trace.signing.toSigningLog ∧
                ¬SigningTranscript.Contains state.trace.signing.toSigningLog forgery) &&
                  verified),
            ⟨finalCache, state.trace, state.views, some targetView⟩) ∈
            support (gameRestWithViewTrace adversary publicKey secretKey rootCache) := by
        rw [hgame, mem_support_bind_iff]
        refine ⟨(forgery, state), hprior, ?_⟩
        rw [mem_support_bind_iff]
        exact ⟨((verified, targetView), finalCache), hverify,
          by simp only [support_pure, Set.mem_singleton_iff]⟩
      have hresult : result ∈ support
          (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret) := by
        rw [gameAfterSecretsWithViewTrace, mem_support_bind_iff]
        refine ⟨(root, rootCache), hroot, ?_⟩
        rw [mem_support_bind_iff]
        exact ⟨_, hrestSupport, by simp [result]⟩
      obtain ⟨f, digest, hf, hvalid, _, hdigest, hadmissible,
        hcollision, _⟩ := hevent.1
      obtain ⟨cover, hcard, hne⟩ :=
        hcollision.exists_singletonFewTimeCover digest hdigest
      have hcacheLe : state.cache ≤ finalCache :=
        simulateQ_romImpl_cache_le
          (liftM (verifyWithView publicKey forgery.message forgery.signature) :
            OracleComp OracleWorld (Bool × FewTimeView)) state.cache
              ((verified, targetView), finalCache) hverify
      rcases gameAfterSecretsWithViewTrace_singletonCover_target_classified_at_adversary_state
          adversary q hq parameter hparameter otsSecret hots ftsSecret hfts result hresult
          f hf digest hdigest hadmissible cover hcard hne hvalid rootCache state rfl rfl
          hcacheLe with hfresh | hclassified
      · exact hevent.2 hfresh
      · obtain ⟨distinct, hdistinct, pattern, configuration, candidate, hterminal⟩ :=
          hclassified
        subst distinct
        apply hnotPrefix
        unfold prefixEvent SomeFixedSingletonOriginTargetViewedTerminal
        exact ⟨pattern, configuration, candidate, hterminal⟩
    _ ≤ _ := probEvent_someFixedSingletonOriginTargetViewedTerminal_le
      secretKey (adversary.main publicKey) rootCache signatureLimit q q hqMax
        (by
          have hroot' : QueryCache.enncard rootCache ≤ q := by
            have hprojected : (root, rootCache) ∈ support
                ((simulateQ romImpl
                  (liftM ((treeRoot parameter topLayer rootTree
                    (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
                      OracleComp OracleWorld Digest)).run ∅) := hroot
            have hgameBound := isQueryBoundP_gameAfterSecrets adversary q hq
              hparameter hots hfts
            rw [gameAfterSecrets] at hgameBound
            have hrootBound := OracleComp.IsQueryBoundP.of_bind_left
              (p := fun input : OracleWorld.Domain => input matches Sum.inr _) hgameBound
            have hbound := simulateQ_romImpl_enncard_le_queryBound
              (liftM ((treeRoot parameter topLayer rootTree
                (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
                  OracleComp OracleWorld Digest) q hrootBound
              (root, rootCache) hprojected
            exact hbound
          exact hroot') q

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
theorem probEvent_gameRestWithViewTrace_fresh_messageCollision_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 120)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (root : Digest) (rootCache : QueryCache HashSpec)
    (hroot : (root, rootCache) ∈ support
      ((simulateQ romImpl
        (liftM ((treeRoot parameter topLayer rootTree
          (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
            OracleComp OracleWorld Digest)).run ∅)) :
    Pr[fun rest =>
        let result : (Digest × Forgery × Bool) × ViewedFullTraceState :=
          ((root, rest.1.1, rest.1.2), rest.2)
        ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          VerifierFreshTarget parameter result |
      gameRestWithViewTrace adversary ⟨root, parameter⟩
        ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache] ≤
      ((q + 1 : Nat) : ℝ≥0∞) * singletonOriginUnionBound signatureLimit q := by
  classical
  let secretKey : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
  let publicKey : PublicKey := ⟨root, parameter⟩
  let initialState : ViewedFullTraceState :=
    ⟨rootCache, ⟨[], [], []⟩, [], none⟩
  let run := (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
    (adversary.main publicKey)).run initialState
  let finish : Forgery × ViewedFullTraceState →
      ProbComp ((Forgery × Bool) × ViewedFullTraceState) := fun prior => do
    let ((verified, targetView), finalCache) ←
      (simulateQ romImpl
        (liftM (verifyWithView publicKey prior.1.message prior.1.signature) :
          OracleComp OracleWorld (Bool × FewTimeView))).run prior.2.cache
    let log := prior.2.trace.signing.toSigningLog
    let verdict := decide (SigningTranscript.Valid log ∧
      ¬SigningTranscript.Contains log prior.1) && verified
    pure ((prior.1, verdict),
      ⟨finalCache, prior.2.trace, prior.2.views, some targetView⟩)
  let freshEvent := fun rest : (Forgery × Bool) × ViewedFullTraceState =>
    let result : (Digest × Forgery × Bool) × ViewedFullTraceState :=
      ((root, rest.1.1, rest.1.2), rest.2)
    ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
      VerifierFreshTarget parameter result
  have hrootNone : ∀ payload,
      rootCache (tweakableHashInput parameter .message payload) = none := by
    have hroot' : (root, rootCache) ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅) := by
      simpa only [simulateQ_romImpl_liftM] using hroot
    exact fun payload => treeRoot_cache_message_none parameter topLayer rootTree
      (otsSecret topLayer rootTree) root rootCache hroot' payload
  have hrootCache : QueryCache.enncard rootCache ≤ q := by
    have hgameBound := isQueryBoundP_gameAfterSecrets adversary q hq
      hparameter hots hfts
    rw [gameAfterSecrets] at hgameBound
    have hrootBound := OracleComp.IsQueryBoundP.of_bind_left
      (p := fun input : OracleWorld.Domain => input matches Sum.inr _) hgameBound
    exact simulateQ_romImpl_enncard_le_queryBound
      (liftM ((treeRoot parameter topLayer rootTree
        (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
          OracleComp OracleWorld Digest) q hrootBound (root, rootCache) hroot
  have hprefixBound :=
    probEvent_someFixedOneOriginTargetViewedTerminal_le
      (α := Forgery × HashOutput) (secretKey := secretKey)
      (computation := adversaryWithTargetQuery adversary publicKey)
      (initialCache := rootCache) (signatures := signatureLimit) (sources := q)
      (q := q) (hq := hqMax) (hcache := hrootCache) (candidates := q + 1)
  have hgame : gameRestWithViewTrace adversary publicKey secretKey rootCache =
      run >>= finish := rfl
  rw [show ⟨root, parameter⟩ = publicKey from rfl,
    show ⟨parameter, root, otsSecret, ftsSecret⟩ = secretKey from rfl, hgame]
  change Pr[freshEvent | run >>= finish] ≤ _
  have hfirst : Pr[freshEvent | run >>= finish] ≤
      Pr[SomeFixedOneOriginTargetViewedTerminal secretKey
        (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1) |
          (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
            (adversaryWithTargetQuery adversary publicKey)).run
              ⟨rootCache, ⟨[], [], []⟩, [], none⟩] := by
    rw [adversaryWithTargetQuery_viewed_run]
    change Pr[_ | run >>= _] ≤
      Pr[SomeFixedOneOriginTargetViewedTerminal secretKey
        (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1) |
          run >>= _]
    apply probEvent_bind_le_bind_of_forall_le
    rintro ⟨forgery, state⟩ hprior
    let input := tweakableHashInput parameter .message
      (messageDigestPayload root forgery.message forgery.signature.randomness)
    change Pr[_ |
      (simulateQ romImpl
        (liftM (verifyWithView publicKey forgery.message forgery.signature) :
          OracleComp OracleWorld (Bool × FewTimeView))).run state.cache >>= _] ≤ _
    rw [verifyWithView_split_run]
    simp only [bind_assoc]
    rw [show tweakableHashInput publicKey.parameter .message
      (messageDigestPayload publicKey.root forgery.message
        forgery.signature.randomness) = input from rfl]
    change _ ≤ Pr[SomeFixedOneOriginTargetViewedTerminal secretKey
      (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1) |
      (randomOracle input).run state.cache >>= pure ∘ fun source =>
        ((forgery, source.1), appendDirectTargetViewedState input state.cache
          source.1 source.2 state)]
    rw [probEvent_bind_pure_comp]
    change Pr[_ | (randomOracle input).run state.cache >>= _] ≤
      Pr[fun source => SomeFixedOneOriginTargetViewedTerminal secretKey
        (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1)
          ((forgery, source.1),
        appendDirectTargetViewedState input state.cache source.1 source.2 state) |
          (randomOracle input).run state.cache]
    apply probEvent_bind_le_probEvent
    rintro ⟨output, digestCache⟩ hquery hnotPrefix
    apply probEvent_eq_zero
    intro rest hrest hevent
    rw [mem_support_bind_iff] at hrest
    obtain ⟨⟨⟨verified, targetView⟩, finalCache⟩, hverifyRest, hpure⟩ := hrest
    simp only [support_pure, Set.mem_singleton_iff] at hpure
    subst rest
    let result : (Digest × Forgery × Bool) × ViewedFullTraceState :=
      ((root, forgery,
        decide (SigningTranscript.Valid state.trace.signing.toSigningLog ∧
          ¬SigningTranscript.Contains state.trace.signing.toSigningLog forgery) &&
            verified),
        ⟨finalCache, state.trace, state.views, some targetView⟩)
    change ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
      VerifierFreshTarget parameter result at hevent
    have hverify : ((verified, targetView), finalCache) ∈ support
        ((simulateQ romImpl
          (liftM (verifyWithView publicKey forgery.message forgery.signature) :
            OracleComp OracleWorld (Bool × FewTimeView))).run state.cache) := by
      rw [verifyWithView_split_run, mem_support_bind_iff]
      exact ⟨(output, digestCache), by simpa only [input, publicKey] using hquery,
        hverifyRest⟩
    have hrestSupport :
        ((forgery,
            decide (SigningTranscript.Valid state.trace.signing.toSigningLog ∧
              ¬SigningTranscript.Contains state.trace.signing.toSigningLog forgery) &&
                verified),
          ⟨finalCache, state.trace, state.views, some targetView⟩) ∈
          support (gameRestWithViewTrace adversary publicKey secretKey rootCache) := by
      rw [gameRestWithViewTrace, mem_support_bind_iff]
      refine ⟨(forgery, state), hprior, ?_⟩
      rw [mem_support_bind_iff]
      exact ⟨((verified, targetView), finalCache), hverify,
        by simp only [support_pure, Set.mem_singleton_iff]⟩
    have hresult : result ∈ support
        (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret) := by
      rw [gameAfterSecretsWithViewTrace, mem_support_bind_iff]
      refine ⟨(root, rootCache), hroot, ?_⟩
      rw [mem_support_bind_iff]
      exact ⟨_, hrestSupport, by simp [result]⟩
    obtain ⟨f, digest, hf, hvalid, _, hdigest, _, hcollision, _⟩ := hevent.1
    obtain ⟨cover, hcard, _⟩ :=
      hcollision.exists_singletonFewTimeCover digest hdigest
    obtain ⟨otherRootCache, adversaryCache, _, _, hotherRootNone,
      hotherChain, hadversaryMiss, _, _, _⟩ := hevent.2
    have hbase : (forgery, state.base) ∈ support
        ((simulateQ (fullTracedMappedAdversaryImpl secretKey)
          (adversary.main publicKey)).run initialState.base) := by
      rw [← viewedFullTracedMappedAdversaryImpl_projection secretKey
        (adversary.main publicKey) initialState, support_map]
      exact ⟨(forgery, state), hprior, rfl⟩
    have hchain : FullAdversaryTrace.CacheChain rootCache state.trace.intervals
        state.cache :=
      fullTracedMappedAdversaryImpl_cacheChain secretKey (adversary.main publicKey)
        rootCache rootCache ⟨[], [], []⟩ (forgery, state.base) (by rfl) hbase
    have hmiss : state.cache input = none := by
      have hrootInput : rootCache input = none := by
        simpa only [input] using hrootNone
          (messageDigestPayload root forgery.message forgery.signature.randomness)
      have hotherRootInput : otherRootCache input = none := by
        simpa only [input, result] using hotherRootNone
          (messageDigestPayload root forgery.message forgery.signature.randomness)
      have hlookup := FullAdversaryTrace.CacheChain.finish_lookup_eq input
        (hrootInput.trans hotherRootInput.symm) hchain
        (by simpa only [result] using hotherChain)
      exact hlookup.trans hadversaryMiss
    have hdigestLe : digestCache ≤ finalCache :=
      simulateQ_romImpl_cache_le
        (liftM (verifyWithViewAfterOutput publicKey forgery.signature output) :
          OracleComp OracleWorld (Bool × FewTimeView)) digestCache
            ((verified, targetView), finalCache) hverifyRest
    have hcachedDigest : digestCache input = some output :=
      randomOracle_output_cached input state.cache digestCache output (by
        have hquerySim : simulateQ (randomOracle : QueryImpl HashSpec _)
            (oracleHash input) = randomOracle input := by
          change simulateQ (randomOracle : QueryImpl HashSpec _)
            (liftM (HashSpec.query input)) = randomOracle input
          rw [simulateQ_spec_query]
        rw [hquerySim]
        exact hquery)
    have hcachedFinal : finalCache input = some output := hdigestLe hcachedDigest
    have hanswer : f input = output := hf (by simpa only [result] using hcachedFinal)
    have hdigestOutput : truncateMessageDigest output = digest := by
      have hdigest' : truncateMessageDigest (f input) = digest := by
        simpa only [messageDigest, oracleHash, evalWithAnswerFn_bind,
          evalWithAnswerFn_query, evalWithAnswerFn_pure, result, input] using hdigest
      rwa [hanswer] at hdigest'
    have htargetOutput : hashOutputFewTimeView output =
        fewTimeTargetView (digestIndex digest) (digestLeaves digest) := by
      simp [hashOutputFewTimeView, fewTimeTargetView, hdigestOutput]
    have hfullBase : (result.1, result.2.base) ∈ support
        (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
      rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret
        ftsSecret, support_map]
      exact ⟨result, hresult, rfl⟩
    obtain ⟨configuration, hrealized⟩ :=
      cover.exists_paddedRealized_originConfiguration_of_queryBudget
        adversary q hq parameter hparameter otsSecret hots ftsSecret hfts
          (result.1, result.2.base) hfullBase f hf (digestIndex digest)
            (digestLeaves digest) signatureLimit hvalid
    have hfinalCache : QueryCache.enncard finalCache ≤ q := by
      have hbound := gameAfterSecretsWithFullTrace_support_enncard_le adversary q hq
        parameter hparameter otsSecret hots ftsSecret hfts
          (result.1, result.2.base) hfullBase
      change QueryCache.enncard result.2.cache ≤ q at hbound
      simpa only [result] using hbound
    have hdigestCard : QueryCache.enncard digestCache ≤ q :=
      (QueryCache.enncard_mono hdigestLe).trans hfinalCache
    have hcountLe : freshTargetCandidateCount secretKey state.trace ≤ q := by
      rw [freshTargetCandidateCount_eq_card]
      have hbound := gameAfterSecretsWithViewTrace_freshTargetCandidatePositions_card_le
        adversary q hq parameter hparameter otsSecret hots ftsSecret hfts result hresult
      simp only [result] at hbound
      exact_mod_cast hbound
    let candidate : Fin (q + 1) :=
      ⟨freshTargetCandidateCount secretKey state.trace, by omega⟩
    unfold SomeFixedOneOriginTargetViewedTerminal at hnotPrefix
    apply hnotPrefix
    refine ⟨cover.entries.card, hcard, cover.pattern.pad hvalid,
      configuration, candidate, ?_⟩
    exact configuration.verifierTarget_fixedTerminal_for_cover adversary parameter otsSecret
      ftsSecret result hresult f hf digest cover hvalid hrealized
        rootCache state hprior rfl rfl input output digestCache rfl hmiss
          (by simpa only [input] using hquery) hdigestLe htargetOutput q hdigestCard
  calc
    Pr[freshEvent | run >>= finish] ≤
        Pr[SomeFixedOneOriginTargetViewedTerminal secretKey
          (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1) |
            (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
              (adversaryWithTargetQuery adversary publicKey)).run
                ⟨rootCache, ⟨[], [], []⟩, [], none⟩] := hfirst
    _ ≤ ((q + 1 : Nat) : ℝ≥0∞) * singletonOriginUnionBound signatureLimit q :=
      hprefixBound

theorem probEvent_gameAfterSecretsWithViewTrace_nonfresh_messageCollision_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 120)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result =>
        ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          ¬VerifierFreshTarget parameter result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      q * singletonOriginUnionBound signatureLimit q := by
  rw [gameAfterSecretsWithViewTrace]
  apply probEvent_bind_le_of_forall_le
  rintro ⟨root, rootCache⟩ hroot
  let attach := fun rest : (Forgery × Bool) × ViewedFullTraceState =>
    ((root, rest.1.1, rest.1.2), rest.2)
  change Pr[fun result =>
      ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
        ¬VerifierFreshTarget parameter result |
    gameRestWithViewTrace adversary ⟨root, parameter⟩
      ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache >>= pure ∘ attach] ≤ _
  rw [probEvent_bind_pure_comp]
  exact probEvent_gameRestWithViewTrace_nonfresh_messageCollision_le adversary q hq hqMax
    parameter hparameter otsSecret hots ftsSecret hfts root rootCache hroot

theorem probEvent_gameAfterSecretsWithViewTrace_fresh_messageCollision_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 120)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result =>
        ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          VerifierFreshTarget parameter result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      ((q + 1 : Nat) : ℝ≥0∞) * singletonOriginUnionBound signatureLimit q := by
  rw [gameAfterSecretsWithViewTrace]
  apply probEvent_bind_le_of_forall_le
  rintro ⟨root, rootCache⟩ hroot
  let attach := fun rest : (Forgery × Bool) × ViewedFullTraceState =>
    ((root, rest.1.1, rest.1.2), rest.2)
  change Pr[fun result =>
      ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
        VerifierFreshTarget parameter result |
    gameRestWithViewTrace adversary ⟨root, parameter⟩
      ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache >>= pure ∘ attach] ≤ _
  rw [probEvent_bind_pure_comp]
  exact probEvent_gameRestWithViewTrace_fresh_messageCollision_le adversary q hq hqMax
    parameter hparameter otsSecret hots ftsSecret hfts root rootCache hroot

theorem probEvent_gameAfterSecretsWithViewTrace_messageCollision_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 120)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      q * singletonOriginUnionBound signatureLimit q +
        ((q + 1 : Nat) : ℝ≥0∞) * singletonOriginUnionBound signatureLimit q := by
  classical
  calc
    _ ≤ Pr[fun result =>
        (ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          ¬VerifierFreshTarget parameter result) ∨
        (ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          VerifierFreshTarget parameter result) |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] := by
        apply probEvent_mono
        intro result _ hcollision
        by_cases hfresh : VerifierFreshTarget parameter result
        · exact Or.inr ⟨hcollision, hfresh⟩
        · exact Or.inl ⟨hcollision, hfresh⟩
    _ ≤ _ := (probEvent_or_le _ _ _).trans (add_le_add
      (probEvent_gameAfterSecretsWithViewTrace_nonfresh_messageCollision_le adversary q hq
        hqMax parameter hparameter otsSecret hots ftsSecret hfts)
      (probEvent_gameAfterSecretsWithViewTrace_fresh_messageCollision_le adversary q hq
        hqMax parameter hparameter otsSecret hots ftsSecret hfts))

theorem probEvent_gameAfterSecretsWithViewTrace_messageCollision_le_inv
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 120)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ q * singletonOriginUnionBound signatureLimit q +
          ((q + 1 : Nat) : ℝ≥0∞) * singletonOriginUnionBound signatureLimit q :=
      probEvent_gameAfterSecretsWithViewTrace_messageCollision_le adversary q hq hqMax
        parameter hparameter otsSecret hots ftsSecret hfts
    _ = ((2 * q + 1 : Nat) : ℝ≥0∞) *
        singletonOriginUnionBound signatureLimit q := by
      push_cast
      ring
    _ ≤ ((2 * q + 1 : Nat) : ℝ≥0∞) *
        ((2 ^ 141 : Nat) : ℝ≥0∞)⁻¹ := by
      have hmass := singletonOriginUnionBound_le_inv q hqMax
      calc
        ((2 * q + 1 : Nat) : ℝ≥0∞) * singletonOriginUnionBound signatureLimit q =
            singletonOriginUnionBound signatureLimit q * (2 * q + 1 : Nat) := mul_comm _ _
        _ ≤ ((2 ^ 141 : Nat) : ℝ≥0∞)⁻¹ * (2 * q + 1 : Nat) :=
          mul_le_mul_left hmass _
        _ = ((2 * q + 1 : Nat) : ℝ≥0∞) *
            ((2 ^ 141 : Nat) : ℝ≥0∞)⁻¹ := mul_comm _ _
    _ ≤ ((4 * q : Nat) : ℝ≥0∞) *
        ((2 ^ 141 : Nat) : ℝ≥0∞)⁻¹ := by
      have hcoeff : ((2 * q + 1 : Nat) : ℝ≥0∞) ≤ (4 * q : Nat) := by
        exact_mod_cast (show 2 * q + 1 ≤ 4 * q by omega)
      exact mul_le_mul_left hcoeff ((2 ^ 141 : Nat) : ℝ≥0∞)⁻¹
    _ = (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      norm_num
      ring

theorem probEvent_sampled_cleanMessage_le
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 120) :
    Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] ≤
      (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [probEvent_sampledViewedGame_eq_weighted]
  calc
    (∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
        Pr[cleanMessageEvent secrets.parameter secrets.otsSecret secrets.ftsSecret |
          gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret
            secrets.ftsSecret]) ≤
        ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
          ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹) := by
      apply ENNReal.tsum_le_tsum
      intro secrets
      by_cases hsecrets : secrets ∈ support sampleSecrets
      · obtain ⟨hparameter, hots, hfts⟩ := secrets.support_components hsecrets
        have hrisk :
            Pr[cleanMessageEvent secrets.parameter secrets.otsSecret secrets.ftsSecret |
                gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret
                  secrets.ftsSecret] ≤
              (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ := by
          apply le_trans (probEvent_mono fun _ _ event => event.2)
          exact probEvent_gameAfterSecretsWithViewTrace_messageCollision_le_inv adversary q
            hqPos hq hqMax secrets.parameter hparameter secrets.otsSecret hots
              secrets.ftsSecret hfts
        calc
          Pr[= secrets | sampleSecrets] *
              Pr[cleanMessageEvent secrets.parameter secrets.otsSecret secrets.ftsSecret |
                gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret
                  secrets.ftsSecret] =
              Pr[cleanMessageEvent secrets.parameter secrets.otsSecret secrets.ftsSecret |
                gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret
                  secrets.ftsSecret] * Pr[= secrets | sampleSecrets] := mul_comm _ _
          _ ≤ ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹) *
              Pr[= secrets | sampleSecrets] :=
            mul_le_mul_left hrisk _
          _ = Pr[= secrets | sampleSecrets] *
              ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹) := mul_comm _ _
      · rw [probOutput_eq_zero_of_not_mem_support hsecrets, zero_mul, zero_mul]
    _ = (∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets]) *
        ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹) := by
      rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹) :=
      mul_le_mul_left tsum_probOutput_le_one _
    _ = (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ := one_mul _

end SphincsSecurity.Concrete
