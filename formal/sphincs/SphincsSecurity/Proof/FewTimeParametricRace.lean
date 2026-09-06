import SphincsSecurity.Proof.FewTimeRace

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

noncomputable local instance parametricRaceRandomnessSampleable : SampleableType Randomness := SampleableType.ofFintype Randomness

theorem uniform_randomness_messageInput_cacheMiss_ge_of_budget
    (secretKey : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (budget : Nat) (hcache : QueryCache.enncard cache ≤ budget) :
    1 - (budget : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ ≤
      Pr[fun randomness : Randomness => cache (tweakableHashInput secretKey.parameter .message
        (Concrete.messageDigestPayload secretKey.root message randomness)) = none | $ᵗ Randomness] := by
  apply probEvent_one_sub_le_of_compl_le (by simp only [probFailure_of_liftM_PMF])
  calc
    _ = Pr[fun randomness : Randomness => ∃ output,
        cache (tweakableHashInput secretKey.parameter .message
          (Concrete.messageDigestPayload secretKey.root message randomness)) = some output | $ᵗ Randomness] := by
      apply probEvent_congr'
      · intro randomness _
        exact Option.ne_none_iff_exists'
      · rfl
    _ ≤ cachedMessageEntryCount cache secretKey.parameter secretKey.root message *
        ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ :=
      uniform_randomness_messageInput_cacheHit_le_cachedMessageEntryCount secretKey.parameter secretKey.root message cache
    _ ≤ _ := mul_le_mul' ((cachedMessageEntryCount_le_enncard cache secretKey.parameter secretKey.root message).trans hcache) le_rfl

set_option linter.constructorNameAsVariable false in
theorem Concrete.probEvent_signDigestAttemptPrefix_success_ge_of_budget
    (secretKey : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (budget : Nat) (hcache : QueryCache.enncard cache ≤ budget) :
    (1 - (budget : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
        ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ ≤
      Pr[fun attempt => attempt.2.1 ≠ none | signDigestAttemptPrefix secretKey message cache] := by
  rw [signDigestAttemptPrefix]
  apply mul_le_probEvent_bind
  · exact uniform_randomness_messageInput_cacheMiss_ge_of_budget secretKey message cache budget hcache
  · intro randomness _hrandomness hmiss
    change ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ ≤
      Pr[fun attempt => attempt.2.1 ≠ none |
        (simulateQ (randomOracle : QueryImpl HashSpec _)
          (signAttempt secretKey message randomness)).run cache >>= fun result => pure (randomness, result)]
    rw [show (fun result => pure (randomness, result)) = pure ∘ fun result => (randomness, result) from rfl,
      probEvent_bind_pure_comp]
    exact le_of_eq (probEvent_signAttempt_fresh_success_eq secretKey message randomness cache hmiss).symm

theorem Concrete.probEvent_signDigestAttemptPrefix_retry_le_of_budget
    (secretKey : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (budget : Nat) (hcache : QueryCache.enncard cache ≤ budget)
    (rate : ENNReal) (hrate : rate ≤ (1 - (budget : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹) :
    Pr[fun attempt => attempt.2.1 = none | signDigestAttemptPrefix secretKey message cache] ≤ 1 - rate := by
  have hsuccess := hrate.trans (probEvent_signDigestAttemptPrefix_success_ge_of_budget secretKey message cache budget hcache)
  have hrateOne : rate ≤ 1 := hsuccess.trans probEvent_le_one
  have hcompl := probEvent_compl_le_of_one_sub_le
    (mx := signDigestAttemptPrefix secretKey message cache) (p := fun attempt => attempt.2.1 ≠ none)
    (ε := 1 - rate) (by simp [signDigestAttemptPrefix]) (by
      rw [ENNReal.sub_sub_cancel (by simp) hrateOne]
      exact hsuccess)
  simpa only [not_ne_iff] using hcompl

theorem prehit_race_recurrence_of_weight
    (count rate weight : ENNReal)
    (hweight : ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ + (1 - rate) * weight ≤ weight) :
    count * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ + (1 - rate) * (count * weight) ≤ count * weight := by
  calc
    _ = count * (((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ + (1 - rate) * weight) := by ring
    _ ≤ _ := mul_le_mul' le_rfl hweight

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.probEvent_signDigestLoop_prehitSelectedView_le_parametric_race
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (P : FewTimeView → Prop)
    (hreference : referenceCache ≤ workingCache)
    (budget : Nat) (rate weight : ENNReal)
    (hrate : rate ≤ (1 - (budget : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹)
    (hweight : ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ + (1 - rate) * weight ≤ weight)
    (hbudget : QueryCache.enncard workingCache + (attempts : ℝ≥0∞) ≤
      (budget : ENNReal)) :
    Pr[PrehitSelectedView referenceCache secretKey message P |
      (simulateQ romImpl
        (signDigestLoop attempts secretKey message)).run workingCache] ≤
      cachedMessageEntryCountWhere referenceCache secretKey.parameter secretKey.root message P *
        weight := by
  induction attempts generalizing workingCache with
  | zero =>
      refine le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
      intro result hresult hevent
      have hresultEq : result = (none, workingCache) := by
        simpa only [signDigestLoop, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hresult
      obtain ⟨randomness, index, leaves, hselected, _⟩ := hevent
      rw [hresultEq] at hselected
      simp at hselected
  | succ attempts ih =>
      rw [signDigestLoop_run_succ_eq_attemptPrefix]
      let count := cachedMessageEntryCountWhere referenceCache secretKey.parameter
        secretKey.root message P
      let epsilon := count * weight
      refine (probEvent_bind_le_probEvent_add_mul
        (hit := FavorablePrehitAttempt referenceCache secretKey message P)
        (retry := fun attempt => attempt.2.1 = none)
        (epsilon := epsilon) ?_ ?_).trans ?_
      · intro attempt _hattempt hnotHit hnotRetry
        cases hattemptResult : attempt.2.1 with
        | none => exact (hnotRetry hattemptResult).elim
        | some selected =>
            rcases selected with ⟨selectedIndex, selectedLeaves⟩
            refine probEvent_eq_zero ?_
            intro result hresult hevent
            have hresultEq : result =
                (some (attempt.1, selectedIndex, selectedLeaves), attempt.2.2) := by
              simpa only [signDigestLoopContinuation, hattemptResult, support_pure,
                Set.mem_singleton_iff] using hresult
            obtain ⟨foundRandomness, foundIndex, foundLeaves, hfound, output, hcached,
              houtputResult, hP⟩ := hevent
            have hrandomness : attempt.1 = foundRandomness := by
              have htuple : (attempt.1, selectedIndex, selectedLeaves) =
                  (foundRandomness, foundIndex, foundLeaves) :=
                Option.some.inj ((congrArg Prod.fst hresultEq).symm.trans hfound)
              exact congrArg Prod.fst htuple
            apply hnotHit
            refine ⟨output, ?_, ?_, hP⟩
            · rw [hrandomness]
              exact hcached
            · rw [houtputResult]
              simp
      · intro attempt hattempt hrejected
        rw [signDigestAttemptPrefix, mem_support_bind_iff] at hattempt
        obtain ⟨randomness, _hrandomness, hattempt⟩ := hattempt
        rw [mem_support_bind_iff] at hattempt
        obtain ⟨attemptResult, hattemptResult, hpure⟩ := hattempt
        simp only [support_pure, Set.mem_singleton_iff] at hpure
        have hattemptPair : attempt.2 = attemptResult := congrArg Prod.snd hpure
        have hgrowth := signAttempt_enncard_le secretKey message randomness workingCache
          attemptResult hattemptResult
        have hbudget' : QueryCache.enncard attempt.2.2 + (attempts : ℝ≥0∞) ≤
            (budget : ENNReal) := by
          calc
            QueryCache.enncard attempt.2.2 + (attempts : ℝ≥0∞) =
                QueryCache.enncard attemptResult.2 + (attempts : ℝ≥0∞) := by
              rw [hattemptPair]
            _ ≤ (QueryCache.enncard workingCache + 1) + (attempts : ℝ≥0∞) := by
              exact add_le_add hgrowth le_rfl
            _ = QueryCache.enncard workingCache + ((attempts + 1 : Nat) : ℝ≥0∞) := by
              push_cast
              ring
            _ ≤ _ := hbudget
        have hmemWorld : attemptResult ∈ support
            ((simulateQ romImpl
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))) :
                  OracleComp OracleWorld (Option (Index × (DigestTree → FtsLeaf))))).run
                workingCache) := by
          rw [simulateQ_romImpl_liftM]
          exact hattemptResult
        have hworkingLe : workingCache ≤ attemptResult.2 :=
          simulateQ_romImpl_cache_le
            (liftM (signAttempt secretKey message randomness :
              OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))) :
                OracleComp OracleWorld (Option (Index × (DigestTree → FtsLeaf))))
            workingCache attemptResult hmemWorld
        have hreference' : referenceCache ≤ attempt.2.2 := by
          rw [hattemptPair]
          exact hreference.trans hworkingLe
        simpa only [epsilon, count, hrejected, signDigestLoopContinuation] using
          ih attempt.2.2 hreference' hbudget'
      · have hworkingBudget : QueryCache.enncard workingCache ≤
            (budget : ENNReal) :=
          (le_add_right le_rfl).trans hbudget
        calc
          Pr[FavorablePrehitAttempt referenceCache secretKey message P |
              signDigestAttemptPrefix secretKey message workingCache] +
                Pr[fun attempt => attempt.2.1 = none |
                  signDigestAttemptPrefix secretKey message workingCache] * epsilon ≤
              count * ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ +
                (1 - rate) * epsilon := by
            gcongr
            · exact probEvent_signDigestAttemptPrefix_favorablePrehit_le
                referenceCache workingCache secretKey message P
            · exact probEvent_signDigestAttemptPrefix_retry_le_of_budget
                secretKey message workingCache budget hworkingBudget rate hrate
          _ ≤ count * weight := by
            exact prehit_race_recurrence_of_weight count rate weight hweight
          _ = _ := rfl


theorem prehit_race_weight_div_success
    (rate : ENNReal) (hpositive : rate ≠ 0) (hfinite : rate ≠ ∞) (hrate : rate ≤ 1) :
    ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ +
        (1 - rate) * (((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ / rate) =
      ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ / rate := by
  have hcancel : rate * (((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ / rate) =
      ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
    rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel hpositive hfinite, mul_one]
  calc
    _ = (rate + (1 - rate)) * (((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ / rate) := by rw [add_mul, hcancel]
    _ = _ := by rw [add_tsub_cancel_of_le hrate, one_mul]

set_option linter.constructorNameAsVariable false in
theorem Concrete.probEvent_signDigestLoop_prehitSelectedView_le_div_success
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (P : FewTimeView → Prop)
    (hreference : referenceCache ≤ workingCache) (budget : Nat)
    (hbudget : QueryCache.enncard workingCache + (attempts : ENNReal) ≤ budget)
    (rate : ENNReal) (hpositive : rate ≠ 0)
    (hrate : rate ≤ (1 - (budget : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹) :
    Pr[PrehitSelectedView referenceCache secretKey message P |
      (simulateQ romImpl (signDigestLoop attempts secretKey message)).run workingCache] ≤
      cachedMessageEntryCountWhere referenceCache secretKey.parameter secretKey.root message P *
        (((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ / rate) := by
  have hcache : QueryCache.enncard workingCache ≤ budget := (le_add_right le_rfl).trans hbudget
  have hrateOne := (hrate.trans (probEvent_signDigestAttemptPrefix_success_ge_of_budget secretKey message workingCache budget hcache)).trans probEvent_le_one
  exact probEvent_signDigestLoop_prehitSelectedView_le_parametric_race attempts secretKey message referenceCache workingCache P
    hreference budget rate _ hrate (prehit_race_weight_div_success rate hpositive (ne_top_of_le_ne_top (by simp) hrateOne) hrateOne).le hbudget

end SphincsSecurity
