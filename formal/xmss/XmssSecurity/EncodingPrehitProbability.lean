import XmssSecurity.EncodingQueryBound

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem cacheTracedMappedAdversaryImpl_query_trace_update
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (hresult : result ∈ support
      ((cacheTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialTrace))) :
    result.2.2 = signingCacheTraceUpdate input initialCache result.1
      result.2.1 initialTrace := by
  rw [cacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hresult
  obtain ⟨baseResult, _hbase, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  rfl

theorem cacheTracedMappedAdversaryImpl_trace_eq_append
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (hresult : result ∈ support
      ((simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    ∃ suffix, result.2.2 = initialTrace ++ suffix := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialTrace result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨[], by simp⟩
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hresult
      have hquery' : (output, middleState) ∈ support
          ((cacheTracedMappedAdversaryImpl publicKey secretKey input).run
            (initialCache, initialTrace)) := by
        simpa [simulateQ_query] using hquery
      have hmiddle := cacheTracedMappedAdversaryImpl_query_trace_update
        publicKey secretKey input initialCache initialTrace (output, middleState) hquery'
      obtain ⟨later, hlater⟩ := ih output middleState.1 middleState.2 result hrest
      cases input with
      | inl worldInput =>
          refine ⟨later, ?_⟩
          rw [hlater, hmiddle]
          simp [signingCacheTraceUpdate]
      | inr request =>
          refine ⟨[SigningCacheEntry.mk request output initialCache middleState.1] ++
            later, ?_⟩
          rw [hlater, hmiddle]
          simp [signingCacheTraceUpdate, List.append_assoc]

theorem cacheTracedMappedAdversaryImpl_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (hresult : result ∈ support
      ((simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    initialCache ≤ result.2.1 := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialTrace result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact le_rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hresult
      have hquery' : (output, middleState) ∈ support
          ((cacheTracedMappedAdversaryImpl publicKey secretKey input).run
            (initialCache, initialTrace)) := by
        simpa [simulateQ_query] using hquery
      have hbase : (output, middleState.1) ∈ support
          ((unloggedMappedAdversaryImpl publicKey secretKey input).run initialCache) := by
        have hprojection := cacheTracedMappedAdversaryImpl_cache_projection
          publicKey secretKey
          (liftM ((OracleWorld + SigningSpec).query input)) initialCache initialTrace
        simp only [simulateQ_spec_query] at hprojection
        rw [← hprojection, support_map]
        exact ⟨(output, middleState), hquery', rfl⟩
      exact (unloggedMappedAdversaryImpl_cache_le publicKey secretKey input
        initialCache (output, middleState.1) hbase).trans
          (ih output middleState.1 middleState.2 result hrest)

noncomputable def cacheTracedSigningQuery
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (initialCache : QueryCache HashSpec)
    (initialTrace : SigningCacheTrace) :
    ProbComp (Option Signature × (QueryCache HashSpec × SigningCacheTrace)) :=
  ((cacheTracedMappedAdversaryImpl publicKey secretKey (.inr request) :
    StateT (QueryCache HashSpec × SigningCacheTrace) ProbComp
      (Option Signature))).run (initialCache, initialTrace)

theorem cacheTracedSigningQuery_encodingInputPrehit_probability_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (initialCache : QueryCache HashSpec)
    (initialTrace : SigningCacheTrace) :
    Pr[fun result : Option Signature ×
        (QueryCache HashSpec × SigningCacheTrace) =>
      (SigningCacheEntry.mk request result.1 initialCache result.2.1)
        |>.EncodingInputPrehit secretKey |
      cacheTracedSigningQuery publicKey secretKey request initialCache initialTrace] ≤
      QueryCache.enncard initialCache *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  have hprojection :
      Prod.map id Prod.fst <$>
          cacheTracedSigningQuery publicKey secretKey request initialCache initialTrace =
        (simulateQ xmssRomImpl
          (Concrete.sign publicKey secretKey request.epoch request.message)).run
            initialCache := by
    unfold cacheTracedSigningQuery cacheTracedMappedAdversaryImpl
    rw [QueryImpl.extendState_apply]
    change Prod.map id Prod.fst <$>
        ((simulateQ xmssRomImpl
          (Concrete.sign publicKey secretKey request.epoch request.message)).run
            initialCache >>= _) = _
    simp
  calc
    _ = Pr[fun result : Option Signature × QueryCache HashSpec =>
        (SigningCacheEntry.mk request result.1 initialCache result.2)
          |>.EncodingInputPrehit secretKey |
        Prod.map id Prod.fst <$>
          cacheTracedSigningQuery publicKey secretKey request initialCache
            initialTrace] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun result : Option Signature × QueryCache HashSpec =>
        (SigningCacheEntry.mk request result.1 initialCache result.2)
          |>.EncodingInputPrehit secretKey |
        (simulateQ xmssRomImpl
          (Concrete.sign publicKey secretKey request.epoch request.message)).run
            initialCache] := by rw [hprojection]
    _ ≤ _ := signingCacheEntry_encodingInputPrehit_probability_le publicKey secretKey
      request initialCache

def SigningCacheTrace.HasEncodingInputPrehitAt
    (trace : SigningCacheTrace) (secretKey : SecretKey) (targetEpoch : Epoch) : Prop :=
  ∃ entry ∈ trace,
    entry.request.epoch = targetEpoch ∧ entry.EncodingInputPrehit secretKey

def SigningCacheTrace.HasEncodingInputPrehit
    (trace : SigningCacheTrace) (secretKey : SecretKey) : Prop :=
  ∃ entry ∈ trace, entry.EncodingInputPrehit secretKey

theorem cacheTracedMappedAdversary_fixedEpoch_prehit_probability_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (targetEpoch : Epoch) (q : Nat)
    (htargetAbsent : targetEpoch ∉ initialTrace.epochs) :
    Pr[fun result : α × (QueryCache HashSpec × SigningCacheTrace) =>
      result.2.2.epochs.Nodup ∧
        QueryCache.enncard result.2.1 ≤ (q : ℝ≥0∞) ∧
        result.2.2.HasEncodingInputPrehitAt secretKey targetEpoch |
      (simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace)] ≤
      (q : ℝ≥0∞) * ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialTrace with
  | pure value =>
      refine le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
      intro result hresult hevent
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      obtain ⟨_hnodup, _hcard, entry, hentry, hepoch, _hprehit⟩ := hevent
      apply htargetAbsent
      rw [SigningCacheTrace.epochs, List.mem_map]
      exact ⟨entry, hentry, hepoch⟩
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind]
      simp only [simulateQ_spec_query]
      by_cases hinitialCard : QueryCache.enncard initialCache ≤ (q : ℝ≥0∞)
      · cases input with
        | inl worldInput =>
            refine probEvent_bind_le_of_forall_le fun middle hmiddle => ?_
            have htrace := cacheTracedMappedAdversaryImpl_query_trace_update
              publicKey secretKey (.inl worldInput) initialCache initialTrace middle hmiddle
            have htargetAbsent' : targetEpoch ∉ middle.2.2.epochs := by
              rw [htrace]
              simpa [signingCacheTraceUpdate] using htargetAbsent
            exact ih middle.1 middle.2.1 middle.2.2 htargetAbsent'
        | inr request =>
            by_cases hepoch : request.epoch = targetEpoch
            · refine (probEvent_bind_le_probEvent
                (p := fun middle : Option Signature ×
                    (QueryCache HashSpec × SigningCacheTrace) =>
                  (SigningCacheEntry.mk request middle.1 initialCache middle.2.1)
                    |>.EncodingInputPrehit secretKey) ?_).trans ?_
              · intro middle hmiddle hmiss
                apply probEvent_eq_zero
                intro result hresult hevent
                have htrace := cacheTracedMappedAdversaryImpl_query_trace_update
                  publicKey secretKey (.inr request) initialCache initialTrace middle
                    hmiddle
                obtain ⟨suffix, hfinalTrace⟩ :=
                  cacheTracedMappedAdversaryImpl_trace_eq_append publicKey secretKey
                    (next middle.1) middle.2.1 middle.2.2 result hresult
                let current := SigningCacheEntry.mk request middle.1 initialCache middle.2.1
                have hcurrent : current ∈ result.2.2 := by
                  rw [hfinalTrace, htrace]
                  simp [current, signingCacheTraceUpdate]
                obtain ⟨hnodup, _hcard, witness, hwitness, hwitnessEpoch,
                  hwitnessPrehit⟩ := hevent
                have hwitnessEq : witness = current := by
                  exact List.inj_on_of_nodup_map
                    (by simpa [SigningCacheTrace.epochs] using hnodup)
                    hwitness hcurrent (hwitnessEpoch.trans hepoch.symm)
                apply hmiss
                simpa [current, hwitnessEq] using hwitnessPrehit
              · refine (cacheTracedSigningQuery_encodingInputPrehit_probability_le
                  publicKey secretKey request initialCache initialTrace).trans ?_
                exact mul_le_mul' hinitialCard le_rfl
            · refine probEvent_bind_le_of_forall_le fun middle hmiddle => ?_
              have htrace := cacheTracedMappedAdversaryImpl_query_trace_update
                publicKey secretKey (.inr request) initialCache initialTrace middle
                  hmiddle
              have htargetAbsent' : targetEpoch ∉ middle.2.2.epochs := by
                rw [htrace]
                simp only [signingCacheTraceUpdate, SigningCacheTrace.epochs_append,
                  List.mem_append, not_or]
                exact ⟨htargetAbsent, by
                  simp [SigningCacheTrace.epochs, Ne.symm hepoch]⟩
              exact ih middle.1 middle.2.1 middle.2.2 htargetAbsent'
      · refine le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
        intro result hresult hevent
        have hcacheLe := cacheTracedMappedAdversaryImpl_cache_le publicKey secretKey
          (liftM ((OracleWorld + SigningSpec).query input) >>= next) initialCache
          initialTrace result ?_
        · exact hinitialCard
            ((QueryCache.enncard_mono hcacheLe).trans hevent.2.1)
        · simpa [simulateQ_bind, StateT.run_bind] using hresult

theorem cacheTracedMappedAdversary_prehit_probability_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (q : Nat) :
    Pr[fun result : α × (QueryCache HashSpec × SigningCacheTrace) =>
      result.2.2.epochs.Nodup ∧
        QueryCache.enncard result.2.1 ≤ (q : ℝ≥0∞) ∧
        result.2.2.HasEncodingInputPrehit secretKey |
      (simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, [])] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  let run := (simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
    computation).run (initialCache, [])
  let fixedEvent := fun targetEpoch (result : α ×
      (QueryCache HashSpec × SigningCacheTrace)) =>
    result.2.2.epochs.Nodup ∧
      QueryCache.enncard result.2.1 ≤ (q : ℝ≥0∞) ∧
      result.2.2.HasEncodingInputPrehitAt secretKey targetEpoch
  calc
    _ ≤ Pr[fun result => ∃ targetEpoch ∈ (Finset.univ : Finset Epoch),
          fixedEvent targetEpoch result | run] := by
      apply probEvent_mono''
      intro result hevent
      obtain ⟨hnodup, hcard, entry, hentry, hprehit⟩ := hevent
      exact ⟨entry.request.epoch, Finset.mem_univ _, hnodup, hcard, entry,
        hentry, rfl, hprehit⟩
    _ ≤ ∑ targetEpoch ∈ (Finset.univ : Finset Epoch),
        Pr[fixedEvent targetEpoch | run] :=
      probEvent_exists_finset_le_sum Finset.univ run fixedEvent
    _ ≤ ∑ _targetEpoch ∈ (Finset.univ : Finset Epoch),
        (q : ℝ≥0∞) * ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro targetEpoch _htargetEpoch
      exact cacheTracedMappedAdversary_fixedEpoch_prehit_probability_le
        publicKey secretKey computation initialCache [] targetEpoch q
          (by simp [SigningCacheTrace.epochs])
    _ = (lifetime : ℝ≥0∞) *
        ((q : ℝ≥0∞) * ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    _ ≤ (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
      simpa [div_eq_mul_inv] using lifetime_mul_randomness_loss_le_digest_loss q

theorem detailedGameAfterKeygenWithSigningTrace_winning_prehit_probability_le
    (q : Nat) (adversary : Adversary Concrete.singleAttemptScheme)
    (hbound : HasHashQueryBound Concrete.singleAttemptScheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅)) :
    Pr[fun execution : GameOutcome ×
        (QueryCache HashSpec × SigningCacheTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
        execution.2.2.HasEncodingInputPrehit execution.1.secretKey |
      detailedGameAfterKeygenWithSigningTrace adversary keyResult.1.1
        keyResult.1.2 keyResult.2] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  unfold detailedGameAfterKeygenWithSigningTrace
  refine (probEvent_bind_le_probEvent
    (p := fun result : Forgery × (QueryCache HashSpec × SigningCacheTrace) =>
      result.2.2.epochs.Nodup ∧
        QueryCache.enncard result.2.1 ≤ (q : ℝ≥0∞) ∧
        result.2.2.HasEncodingInputPrehit keyResult.1.2) ?_).trans ?_
  · intro adversaryResult hadversaryResult hprefix
    apply probEvent_eq_zero
    intro execution hexecution hevent
    have htail := hexecution
    rw [mem_support_bind_iff] at hexecution
    obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hexecution
    simp only [support_pure, Set.mem_singleton_iff] at hfinal
    subst execution
    have hafter :
        (⟨keyResult.1.1, keyResult.1.2, adversaryResult.1,
          adversaryResult.2.2.toSigningLog, verified⟩,
            (finalCache, adversaryResult.2.2)) ∈ support
          (detailedGameAfterKeygenWithSigningTrace adversary keyResult.1.1
            keyResult.1.2 keyResult.2) := by
      unfold detailedGameAfterKeygenWithSigningTrace
      rw [mem_support_bind_iff]
      exact ⟨adversaryResult, hadversaryResult, htail⟩
    have hgame :
        (⟨keyResult.1.1, keyResult.1.2, adversaryResult.1,
          adversaryResult.2.2.toSigningLog, verified⟩,
            (finalCache, adversaryResult.2.2)) ∈
          support (detailedGameWithSigningTrace adversary) := by
      unfold detailedGameWithSigningTrace
      rw [mem_support_bind_iff]
      exact ⟨keyResult, hkeyResult, hafter⟩
    have hfinalCard : QueryCache.enncard finalCache ≤ (q : ℝ≥0∞) :=
      detailedGameWithSigningTrace_cache_enncard_le_of_mem_support
        adversary q hbound _ hgame
    have hadversaryCacheLe : adversaryResult.2.1 ≤ finalCache :=
      xmssRom_cache_le
        (Concrete.singleAttemptScheme.verify keyResult.1.1 adversaryResult.1.epoch
          adversaryResult.1.message adversaryResult.1.signature)
        adversaryResult.2.1 (verified, finalCache) hverify
    apply hprefix
    refine ⟨?_, (QueryCache.enncard_mono hadversaryCacheLe).trans hfinalCard, ?_⟩
    · have hvalid := hevent.1.signingTranscript_valid
      unfold SigningTranscript.Valid at hvalid
      simpa [SigningCacheTrace.epochs, SigningCacheTrace.toSigningLog,
        List.map_map, Function.comp_def] using hvalid
    · simpa [SigningCacheTrace.HasEncodingInputPrehit] using hevent.2
  · exact cacheTracedMappedAdversary_prehit_probability_le keyResult.1.1
      keyResult.1.2 (adversary.main keyResult.1.1) keyResult.2 q

theorem detailedGameWithSigningTrace_winning_prehit_probability_le
    (q : Nat) (adversary : Adversary Concrete.singleAttemptScheme)
    (hbound : HasHashQueryBound Concrete.singleAttemptScheme adversary q) :
    Pr[fun execution : GameOutcome ×
        (QueryCache HashSpec × SigningCacheTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
        execution.2.2.HasEncodingInputPrehit execution.1.secretKey |
      detailedGameWithSigningTrace adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  unfold detailedGameWithSigningTrace
  refine probEvent_bind_le_of_forall_le fun keyResult hkeyResult => ?_
  exact detailedGameAfterKeygenWithSigningTrace_winning_prehit_probability_le
    q adversary hbound keyResult hkeyResult

end XmssSecurity
