import XmssSecurity.Proof.CappedEncodingExpectedBound
import XmssSecurity.Proof.CappedEncodingPrehitProbability

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option maxRecDepth 100000

noncomputable def expectedFinalEpochEncodingEntryCount
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (targetEpoch : Epoch) : ℝ≥0∞ :=
  ∑' result,
    Pr[= result |
      (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace)] *
      cachedEncodingEntryCount result.2.1 secretKey.parameter targetEpoch

noncomputable def expectedFinalEpochPrehitRisk
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (targetEpoch : Epoch) : ℝ≥0∞ :=
  ∑' result,
    Pr[= result |
      (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace)] *
      ((signingAttemptLimit : ℝ≥0∞) *
        cachedEncodingEntryCount result.2.1 secretKey.parameter targetEpoch *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹)

attribute [irreducible] expectedFinalEpochPrehitRisk

theorem probEvent_bind_le_expected_of_support
    (headComp : ProbComp β) (continuation : β → ProbComp γ)
    (event : γ → Prop) (cost : γ → ℝ≥0∞)
    (hcontinuation : ∀ middle ∈ support headComp,
      Pr[event | continuation middle] ≤
        ∑' result, Pr[= result | continuation middle] * cost result) :
    Pr[event | headComp >>= continuation] ≤
      ∑' result, Pr[= result | headComp >>= continuation] * cost result := by
  rw [probEvent_bind_eq_tsum, tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro middle
  by_cases hmiddle : middle ∈ support headComp
  · exact mul_le_mul_right (hcontinuation middle hmiddle) _
  · rw [probOutput_eq_zero_of_not_mem_support hmiddle]
    simp

theorem le_expected_of_support
    (computation : ProbComp β) (cost : β → ℝ≥0∞) (lower : ℝ≥0∞)
    (hmass : ∑' result, Pr[= result | computation] = 1)
    (hlower : ∀ result ∈ support computation, lower ≤ cost result) :
    lower ≤ ∑' result, Pr[= result | computation] * cost result := by
  calc
    lower = (∑' result, Pr[= result | computation]) * lower := by rw [hmass, one_mul]
    _ = ∑' result, Pr[= result | computation] * lower :=
      ENNReal.tsum_mul_right.symm
    _ ≤ ∑' result, Pr[= result | computation] * cost result := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support computation
      · exact mul_le_mul_right (hlower result hresult) _
      · rw [probOutput_eq_zero_of_not_mem_support hresult]
        simp

theorem initialEpochPrehitRisk_le_expectedFinalEpochPrehitRisk
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (targetEpoch : Epoch) :
    (signingAttemptLimit : ℝ≥0∞) *
        cachedEncodingEntryCount initialCache secretKey.parameter targetEpoch *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ ≤
      expectedFinalEpochPrehitRisk publicKey secretKey computation initialCache
        initialTrace targetEpoch := by
  rw [expectedFinalEpochPrehitRisk]
  apply le_expected_of_support
  · exact tsum_probOutput_eq_one' (by simp)
  · intro result hresult
    have hcacheLe := cappedCacheTracedMappedAdversaryImpl_cache_le
      publicKey secretKey computation initialCache initialTrace result hresult
    exact mul_le_mul'
      (mul_le_mul' le_rfl
        (cachedEncodingEntryCount_mono initialCache result.2.1
          secretKey.parameter targetEpoch hcacheLe)) le_rfl

theorem probEvent_query_bind_le_expectedFinalEpochPrehitRisk
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input →
      OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (targetEpoch : Epoch) (event : α × (QueryCache HashSpec × SigningCacheTrace) → Prop)
    (hnext : ∀ middle ∈ support
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialTrace)),
      Pr[event |
        (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
          (next middle.1)).run middle.2] ≤
        expectedFinalEpochPrehitRisk publicKey secretKey (next middle.1)
          middle.2.1 middle.2.2 targetEpoch) :
    Pr[event |
      (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        (liftM ((OracleWorld + SigningSpec).query input) >>= next)).run
          (initialCache, initialTrace)] ≤
      expectedFinalEpochPrehitRisk publicKey secretKey
        (liftM ((OracleWorld + SigningSpec).query input) >>= next)
          initialCache initialTrace targetEpoch := by
  rw [expectedFinalEpochPrehitRisk, simulateQ_bind, StateT.run_bind]
  apply probEvent_bind_le_expected_of_support
  intro middle hmiddle
  have hmiddle' : middle ∈ support
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialTrace)) := by
    simpa [simulateQ_query] using hmiddle
  have hbound := hnext middle hmiddle'
  rw [expectedFinalEpochPrehitRisk] at hbound
  exact hbound

theorem cappedCacheTracedMappedAdversary_fixedEpoch_prehit_probability_le_expectedRisk
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (targetEpoch : Epoch)
    (htargetAbsent : targetEpoch ∉ initialTrace.epochs) :
    Pr[fun result : α × (QueryCache HashSpec × SigningCacheTrace) =>
      result.2.2.epochs.Nodup ∧
        result.2.2.HasEncodingInputPrehitAt secretKey targetEpoch |
      (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace)] ≤
      expectedFinalEpochPrehitRisk publicKey secretKey computation initialCache
        initialTrace targetEpoch := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialTrace with
  | pure value =>
      refine le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
      intro result hresult hevent
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      obtain ⟨_hnodup, entry, hentry, hepoch, _hprehit⟩ := hevent
      apply htargetAbsent
      rw [SigningCacheTrace.epochs, List.mem_map]
      exact ⟨entry, hentry, hepoch⟩
  | query_bind input next ih =>
      cases input with
      | inl worldInput =>
          apply probEvent_query_bind_le_expectedFinalEpochPrehitRisk
          intro middle hmiddle
          have htrace := cappedCacheTracedMappedAdversaryImpl_query_trace_update
            publicKey secretKey (.inl worldInput) initialCache initialTrace middle hmiddle
          have htargetAbsent' : targetEpoch ∉ middle.2.2.epochs := by
            rw [htrace]
            simpa [signingCacheTraceUpdate] using htargetAbsent
          exact ih middle.1 middle.2.1 middle.2.2 htargetAbsent'
      | inr request =>
          by_cases hepoch : request.epoch = targetEpoch
          · rw [simulateQ_bind, StateT.run_bind]
            simp only [simulateQ_spec_query]
            refine (probEvent_bind_le_probEvent
                (p := fun middle : Option Signature ×
                    (QueryCache HashSpec × SigningCacheTrace) =>
                  (SigningCacheEntry.mk request middle.1 initialCache middle.2.1)
                    |>.EncodingInputPrehit secretKey) ?_).trans ?_
            · intro middle hmiddle hmiss
              apply probEvent_eq_zero
              intro result hresult hevent
              have htrace := cappedCacheTracedMappedAdversaryImpl_query_trace_update
                publicKey secretKey (.inr request) initialCache initialTrace middle hmiddle
              obtain ⟨suffix, hfinalTrace⟩ :=
                cappedCacheTracedMappedAdversaryImpl_trace_eq_append publicKey secretKey
                  (next middle.1) middle.2.1 middle.2.2 result hresult
              let current := SigningCacheEntry.mk request middle.1 initialCache middle.2.1
              have hcurrent : current ∈ result.2.2 := by
                rw [hfinalTrace, htrace]
                simp [current, signingCacheTraceUpdate]
              obtain ⟨hnodup, witness, hwitness, hwitnessEpoch,
                hwitnessPrehit⟩ := hevent
              have hwitnessEq : witness = current := by
                exact List.inj_on_of_nodup_map
                  (by simpa [SigningCacheTrace.epochs] using hnodup)
                  hwitness hcurrent (hwitnessEpoch.trans hepoch.symm)
              apply hmiss
              simpa [current, hwitnessEq] using hwitnessPrehit
            · refine (cappedCacheTracedSigningQuery_encodingInputPrehit_probability_le_cachedCount
                publicKey secretKey request initialCache initialTrace).trans ?_
              rw [hepoch]
              exact initialEpochPrehitRisk_le_expectedFinalEpochPrehitRisk
                publicKey secretKey
                (liftM ((OracleWorld + SigningSpec).query (.inr request)) >>= next)
                initialCache initialTrace targetEpoch
          · apply probEvent_query_bind_le_expectedFinalEpochPrehitRisk
            intro middle hmiddle
            have htrace := cappedCacheTracedMappedAdversaryImpl_query_trace_update
              publicKey secretKey (.inr request) initialCache initialTrace middle hmiddle
            have htargetAbsent' : targetEpoch ∉ middle.2.2.epochs := by
              rw [htrace]
              simp only [signingCacheTraceUpdate, SigningCacheTrace.epochs_append,
                List.mem_append, not_or]
              exact ⟨htargetAbsent, by
                simp [SigningCacheTrace.epochs, Ne.symm hepoch]⟩
            exact ih middle.1 middle.2.1 middle.2.2 htargetAbsent'

theorem cappedCacheTracedMappedAdversary_prehit_probability_le_sum_expectedRisk
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) :
    Pr[fun result : α × (QueryCache HashSpec × SigningCacheTrace) =>
      result.2.2.epochs.Nodup ∧
        result.2.2.HasEncodingInputPrehit secretKey |
      (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, [])] ≤
      ∑ targetEpoch ∈ (Finset.univ : Finset Epoch),
        expectedFinalEpochPrehitRisk publicKey secretKey computation initialCache []
          targetEpoch := by
  let run :=
    (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
      computation).run (initialCache, [])
  let fixedEvent := fun targetEpoch (result : α ×
      (QueryCache HashSpec × SigningCacheTrace)) =>
    result.2.2.epochs.Nodup ∧
      result.2.2.HasEncodingInputPrehitAt secretKey targetEpoch
  calc
    _ ≤ Pr[fun result => ∃ targetEpoch ∈ (Finset.univ : Finset Epoch),
          fixedEvent targetEpoch result | run] := by
      apply probEvent_mono''
      intro result hevent
      obtain ⟨hnodup, entry, hentry, hprehit⟩ := hevent
      exact ⟨entry.request.epoch, Finset.mem_univ _, hnodup, entry, hentry, rfl,
        hprehit⟩
    _ ≤ ∑ targetEpoch ∈ (Finset.univ : Finset Epoch),
        Pr[fixedEvent targetEpoch | run] :=
      probEvent_exists_finset_le_sum Finset.univ run fixedEvent
    _ ≤ ∑ targetEpoch ∈ (Finset.univ : Finset Epoch),
        expectedFinalEpochPrehitRisk publicKey secretKey computation initialCache []
          targetEpoch := by
      apply Finset.sum_le_sum
      intro targetEpoch _htargetEpoch
      exact
        cappedCacheTracedMappedAdversary_fixedEpoch_prehit_probability_le_expectedRisk
          publicKey secretKey computation initialCache [] targetEpoch
            (by simp [SigningCacheTrace.epochs])

noncomputable def expectedFinalEncodingEntryCount
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) : ℝ≥0∞ :=
  ∑' result,
    Pr[= result |
      (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, [])] *
      ∑ epoch ∈ (Finset.univ : Finset Epoch),
        cachedEncodingEntryCount result.2.1 secretKey.parameter epoch

theorem mul_fintypeSum_mul (left right : ℝ≥0∞) (value : Epoch → ℝ≥0∞) :
    (left * ∑ epoch, value epoch) * right =
      ∑ epoch, (left * value epoch) * right := by
  rw [Finset.mul_sum, Finset.sum_mul]

theorem mul_mul_fintypeSum_mul (left middle right : ℝ≥0∞)
    (value : Epoch → ℝ≥0∞) :
    left * (middle * ∑ epoch, value epoch) * right =
      ∑ epoch, (left * (middle * value epoch)) * right := by
  rw [← mul_assoc, mul_fintypeSum_mul]
  apply Finset.sum_congr rfl
  intro epoch _hepoch
  simp only [mul_assoc]

theorem sum_expectedFinalEpochPrehitRisk_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) :
    (∑ epoch ∈ (Finset.univ : Finset Epoch),
      expectedFinalEpochPrehitRisk publicKey secretKey computation initialCache [] epoch) =
      (signingAttemptLimit : ℝ≥0∞) *
        expectedFinalEncodingEntryCount publicKey secretKey computation initialCache *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  simp_rw [expectedFinalEpochPrehitRisk, expectedFinalEncodingEntryCount]
  rw [← tsum_fintype (L := .unconditional _) (fun epoch : Epoch =>
    ∑' result : α × (QueryCache HashSpec × SigningCacheTrace),
      Pr[= result |
        (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialCache, [])] *
        ((signingAttemptLimit : ℝ≥0∞) *
          cachedEncodingEntryCount result.2.1 secretKey.parameter epoch *
          ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹)), ENNReal.tsum_comm]
  simp_rw [tsum_fintype (L := .unconditional _)]
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro result
  rw [mul_mul_fintypeSum_mul]
  apply Finset.sum_congr rfl
  intro epoch _hepoch
  ac_rfl

theorem cachedEncodingInputCount_romImpl_step_le
    (parameter : PublicParameter) (input : OracleWorld.Domain)
    (initialCache : QueryCache HashSpec)
    (result : OracleWorld.Range input × QueryCache HashSpec)
    (hresult : result ∈ support ((romImpl input).run initialCache)) :
    cachedEncodingInputCount result.2 parameter ≤
      cachedEncodingInputCount initialCache parameter +
        if CappedEncodingMonitor.IsEncodingHashQuery parameter input then 1 else 0 := by
  cases input with
  | inl uniformIndex =>
      have hrun :
          (unifFwdImpl HashSpec uniformIndex).run initialCache =
            (fun sample => (sample, initialCache)) <$>
              (liftM (unifSpec.query uniformIndex) : ProbComp _) := by
        simpa [simulateQ_query] using
          (unifFwdImpl.simulateQ_run
            (hashSpec := HashSpec)
            (liftM (unifSpec.query uniformIndex) : ProbComp _) initialCache)
      change result ∈ support
        ((unifFwdImpl HashSpec uniformIndex).run initialCache) at hresult
      rw [hrun, support_map] at hresult
      obtain ⟨sampled, _hsampled, heq⟩ := hresult
      have hcache : initialCache = result.2 := congrArg Prod.snd heq
      rw [← hcache]
      simp [CappedEncodingMonitor.IsEncodingHashQuery]
  | inr hashInput =>
      rcases result with ⟨returned, finalCache⟩
      change HashOutput at returned
      change (returned, finalCache) ∈
        support ((randomOracle (spec := HashSpec) hashInput).run initialCache) at hresult
      cases hcache : initialCache hashInput with
      | none =>
          rw [QueryImpl.withCaching_run_none _ hcache, support_map,
            Set.mem_image] at hresult
          obtain ⟨sampled, _hsampled, heq⟩ := hresult
          have hfinal : finalCache = initialCache.cacheQuery hashInput sampled :=
            (congrArg Prod.snd heq).symm
          change cachedEncodingInputCount finalCache parameter ≤ _
          rw [hfinal]
          have hindicator :
              (if CappedEncodingMonitor.IsEncodingHashQuery parameter (.inr hashInput)
                then (1 : ℝ≥0∞) else 0) =
              if (encodingInputEpoch? parameter hashInput).isSome then 1 else 0 := by
            by_cases hencoding : (encodingInputEpoch? parameter hashInput).isSome
            · simp [CappedEncodingMonitor.IsEncodingHashQuery_inr, hencoding]
            · simp [CappedEncodingMonitor.IsEncodingHashQuery_inr, hencoding]
          rw [hindicator]
          exact cachedEncodingInputCount_cacheQuery_le initialCache parameter hashInput sampled
      | some cached =>
          rw [QueryImpl.withCaching_run_some _ hcache, support_pure,
            Set.mem_singleton_iff] at hresult
          have hfinal : finalCache = initialCache := congrArg Prod.snd hresult
          change cachedEncodingInputCount finalCache parameter ≤ _
          rw [hfinal]
          simp [CappedEncodingMonitor.IsEncodingHashQuery]

theorem expectedFinalEncodingInputCount_le_initial_add_expectedQueries
    (parameter : PublicParameter) (computation : OracleComp OracleWorld α)
    (initialCache : QueryCache HashSpec) :
    (∑' result,
      Pr[= result | (simulateQ romImpl computation).run initialCache] *
        cachedEncodingInputCount result.2 parameter) ≤
      cachedEncodingInputCount initialCache parameter +
        expectedSimulatedQueryCount romImpl
          (CappedEncodingMonitor.IsEncodingHashQuery parameter) computation initialCache := by
  exact expectedResource_le_initial_add_expectedSimulatedQueryCount
    romImpl (CappedEncodingMonitor.IsEncodingHashQuery parameter)
      (fun cache => cachedEncodingInputCount cache parameter)
      (cachedEncodingInputCount_romImpl_step_le parameter)
      computation initialCache

theorem Concrete.keygen_cachedEncodingInputCount_eq_zero
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    cachedEncodingInputCount keyResult.2 keyResult.1.2.parameter = 0 := by
  unfold cachedEncodingInputCount
  have hempty : cachedEncodingInputSet keyResult.2 keyResult.1.2.parameter = ∅ := by
    ext entry
    simp only [cachedEncodingInputSet, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hcache
    change keyResult.2 entry.1 = some entry.2 at hcache
    cases hepoch : encodingInputEpoch? keyResult.1.2.parameter entry.1 with
    | none => simp
    | some epoch =>
        intro _hisSome
        obtain ⟨payload, hinput⟩ :=
          exists_encodingInput_of_encodingInputEpoch?_eq_some
            keyResult.1.2.parameter entry.1 epoch hepoch
        have hmem' : keyResult ∈ support
            ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) := by
          simpa [Concrete.scheme] using hmem
        have hnone := Concrete.precomputedKeygen_cache_none_encodingInput
          keyResult hmem' epoch payload
        rw [hinput] at hnone
        rw [hnone] at hcache
        exact (Option.some_ne_none entry.2) hcache.symm
  rw [hempty]
  simp

theorem expectedFinalEncodingEntryCount_afterKeygen_le_sourceQueries
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    expectedFinalEncodingEntryCount keyResult.1.1 keyResult.1.2
        (adversary.main keyResult.1.1) keyResult.2 ≤
      expectedSimulatedQueryCount romImpl
        (CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter)
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary
          keyResult.1.1 keyResult.1.2) keyResult.2 := by
  let publicKey := keyResult.1.1
  let secretKey := keyResult.1.2
  let initialCache := keyResult.2
  let tracedRun :=
    (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run (initialCache, [])
  let unloggedRun :=
    (simulateQ (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run initialCache
  let sourceHead :=
    simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)
  let sourceFinish : Forgery → OracleComp OracleWorld (Forgery × Bool) :=
    fun forgery => do
      let verified ← Concrete.scheme.verify publicKey forgery.epoch
        forgery.message forgery.signature
      pure (forgery, verified)
  have hprojection :
      Prod.map id Prod.fst <$> tracedRun = unloggedRun := by
    simpa [tracedRun, unloggedRun] using
      cappedCacheTracedMappedAdversaryImpl_cache_projection publicKey secretKey
        (adversary.main publicKey) initialCache []
  have hunlogged : unloggedRun =
      (simulateQ romImpl sourceHead).run initialCache := by
    simpa [unloggedRun, sourceHead] using
      CappedEncodingMonitor.cappedUnloggedMappedAdversary_simulateQ_run_eq_source
        publicKey secretKey
        (adversary.main publicKey) initialCache
  have hheadResource :
      (∑' result, Pr[= result | (simulateQ romImpl sourceHead).run initialCache] *
        cachedEncodingInputCount result.2 secretKey.parameter) ≤
      cachedEncodingInputCount initialCache secretKey.parameter +
        expectedSimulatedQueryCount romImpl
          (CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter)
          sourceHead initialCache :=
    expectedFinalEncodingInputCount_le_initial_add_expectedQueries
      secretKey.parameter sourceHead initialCache
  have hinitial : cachedEncodingInputCount initialCache secretKey.parameter = 0 := by
    exact Concrete.keygen_cachedEncodingInputCount_eq_zero keyResult hkeyResult
  have hheadLeFull :
      expectedSimulatedQueryCount romImpl
          (CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter)
          sourceHead initialCache ≤
        expectedSimulatedQueryCount romImpl
          (CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter)
          (sourceHead >>= sourceFinish) initialCache := by
    rw [expectedSimulatedQueryCount_bind]
    exact le_add_right le_rfl
  unfold expectedFinalEncodingEntryCount
  simp_rw [sum_cachedEncodingEntryCount_univ_eq_cachedEncodingInputCount]
  calc
    (∑' result, Pr[= result | tracedRun] *
        cachedEncodingInputCount result.2.1 secretKey.parameter) =
      ∑' result, Pr[= result |
          Prod.map id Prod.fst <$> tracedRun] *
        cachedEncodingInputCount result.2 secretKey.parameter := by
      rw [tsum_probOutput_map_mul]
      rfl
    _ = ∑' result, Pr[= result | unloggedRun] *
        cachedEncodingInputCount result.2 secretKey.parameter := by rw [hprojection]
    _ = ∑' result, Pr[= result |
          (simulateQ romImpl sourceHead).run initialCache] *
        cachedEncodingInputCount result.2 secretKey.parameter := by rw [hunlogged]
    _ ≤ cachedEncodingInputCount initialCache secretKey.parameter +
        expectedSimulatedQueryCount romImpl
          (CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter)
          sourceHead initialCache := hheadResource
    _ = expectedSimulatedQueryCount romImpl
          (CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter)
          sourceHead initialCache := by rw [hinitial, zero_add]
    _ ≤ expectedSimulatedQueryCount romImpl
          (CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter)
          (sourceHead >>= sourceFinish) initialCache := hheadLeFull
    _ = expectedSimulatedQueryCount romImpl
          (CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter)
          (cappedSourceUnloggedDetailedGameAfterKeygen adversary
            keyResult.1.1 keyResult.1.2) keyResult.2 := by
      rfl

theorem cappedDetailedGameAfterKeygenWithSigningTrace_winning_prehit_probability_le_expected
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    Pr[fun execution : GameOutcome ×
        (QueryCache HashSpec × SigningCacheTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
        execution.2.2.HasEncodingInputPrehit execution.1.secretKey |
      cappedDetailedGameAfterKeygenWithSigningTrace adversary keyResult.1.1
        keyResult.1.2 keyResult.2] ≤
      (signingAttemptLimit : ℝ≥0∞) *
        expectedSimulatedQueryCount romImpl
          (CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter)
          (cappedSourceUnloggedDetailedGameAfterKeygen adversary
            keyResult.1.1 keyResult.1.2) keyResult.2 *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold cappedDetailedGameAfterKeygenWithSigningTrace
  refine (probEvent_bind_le_probEvent
    (p := fun result : Forgery × (QueryCache HashSpec × SigningCacheTrace) =>
      result.2.2.epochs.Nodup ∧
        result.2.2.HasEncodingInputPrehit keyResult.1.2) ?_).trans ?_
  · intro adversaryResult hadversaryResult hprefix
    apply probEvent_eq_zero
    intro execution hexecution hevent
    have htail := hexecution
    rw [mem_support_bind_iff] at hexecution
    obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hexecution
    simp only [support_pure, Set.mem_singleton_iff] at hfinal
    subst execution
    apply hprefix
    refine ⟨?_, ?_⟩
    · have hvalid := hevent.1.signingTranscript_valid
      unfold SigningTranscript.Valid at hvalid
      simpa [SigningCacheTrace.epochs, SigningCacheTrace.toSigningLog,
        List.map_map, Function.comp_def] using hvalid
    · simpa [SigningCacheTrace.HasEncodingInputPrehit] using hevent.2
  · calc
      _ ≤ ∑ targetEpoch ∈ (Finset.univ : Finset Epoch),
          expectedFinalEpochPrehitRisk keyResult.1.1 keyResult.1.2
            (adversary.main keyResult.1.1) keyResult.2 [] targetEpoch :=
        cappedCacheTracedMappedAdversary_prehit_probability_le_sum_expectedRisk
          keyResult.1.1 keyResult.1.2 (adversary.main keyResult.1.1) keyResult.2
      _ = (signingAttemptLimit : ℝ≥0∞) *
          expectedFinalEncodingEntryCount keyResult.1.1 keyResult.1.2
            (adversary.main keyResult.1.1) keyResult.2 *
          ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ :=
        sum_expectedFinalEpochPrehitRisk_eq keyResult.1.1 keyResult.1.2
          (adversary.main keyResult.1.1) keyResult.2
      _ ≤ (signingAttemptLimit : ℝ≥0∞) *
          expectedSimulatedQueryCount romImpl
            (CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter)
            (cappedSourceUnloggedDetailedGameAfterKeygen adversary
              keyResult.1.1 keyResult.1.2) keyResult.2 *
          ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
        exact mul_le_mul'
          (mul_le_mul' le_rfl
            (expectedFinalEncodingEntryCount_afterKeygen_le_sourceQueries
              adversary keyResult hkeyResult)) le_rfl

theorem tsum_probability_mul_scaledCost
    (probability cost : β → ℝ≥0∞) (left right : ℝ≥0∞) :
    (∑' result, probability result * (left * cost result * right)) =
      left * (∑' result, probability result * cost result) * right := by
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro result
  ac_rfl

theorem cappedDetailedGameWithSigningTrace_winning_prehit_probability_le_expected
    (adversary : Adversary) :
    Pr[fun execution : GameOutcome ×
        (QueryCache HashSpec × SigningCacheTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
        execution.2.2.HasEncodingInputPrehit execution.1.secretKey |
      cappedDetailedGameWithSigningTrace adversary] ≤
      (signingAttemptLimit : ℝ≥0∞) *
        CappedEncodingMonitor.expectedPostKeygenEncodingQueries adversary *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold cappedDetailedGameWithSigningTrace
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' keyResult,
        Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
          ((signingAttemptLimit : ℝ≥0∞) *
            expectedSimulatedQueryCount romImpl
              (CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter)
              (cappedSourceUnloggedDetailedGameAfterKeygen adversary
                keyResult.1.1 keyResult.1.2) keyResult.2 *
            ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) := by
      apply ENNReal.tsum_le_tsum
      intro keyResult
      by_cases hkeyResult : keyResult ∈ support
          ((simulateQ romImpl Concrete.scheme.keygen).run ∅)
      · exact mul_le_mul_right
          (cappedDetailedGameAfterKeygenWithSigningTrace_winning_prehit_probability_le_expected
            adversary keyResult hkeyResult) _
      · rw [probOutput_eq_zero_of_not_mem_support hkeyResult]
        simp
    _ = (signingAttemptLimit : ℝ≥0∞) *
        (∑' keyResult,
          Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
            expectedSimulatedQueryCount romImpl
              (CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter)
              (cappedSourceUnloggedDetailedGameAfterKeygen adversary
                keyResult.1.1 keyResult.1.2) keyResult.2) *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
      exact tsum_probability_mul_scaledCost _ _ _ _
    _ = (signingAttemptLimit : ℝ≥0∞) *
        CappedEncodingMonitor.expectedPostKeygenEncodingQueries adversary *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
      rfl

theorem signingAttemptLimit_mul_randomness_loss_le_digest_loss
    (queries : ℝ≥0∞) :
    (signingAttemptLimit : ℝ≥0∞) * queries *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ ≤
      queries / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  rw [div_eq_mul_inv]
  calc
    (signingAttemptLimit : ℝ≥0∞) * queries *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ =
      queries * ((signingAttemptLimit : ℝ≥0∞) *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) := by ac_rfl
    _ ≤ queries * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      gcongr
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast]
      norm_num [signingAttemptLimit, randomnessBits, digestBits]
    _ = _ := rfl

theorem cappedDetailedGameWithSigningTrace_winning_prehit_probability_le_expectedDigest
    (adversary : Adversary) :
    Pr[fun execution : GameOutcome ×
        (QueryCache HashSpec × SigningCacheTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
        execution.2.2.HasEncodingInputPrehit execution.1.secretKey |
      cappedDetailedGameWithSigningTrace adversary] ≤
      CappedEncodingMonitor.expectedPostKeygenEncodingQueries adversary /
        ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  exact
    (cappedDetailedGameWithSigningTrace_winning_prehit_probability_le_expected
      adversary).trans
        (signingAttemptLimit_mul_randomness_loss_le_digest_loss
          (CappedEncodingMonitor.expectedPostKeygenEncodingQueries adversary))

end XmssSecurity
