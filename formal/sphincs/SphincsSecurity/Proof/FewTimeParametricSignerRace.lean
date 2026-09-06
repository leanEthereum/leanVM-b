import SphincsSecurity.Proof.FewTimeParametricRace

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.probEvent_signWithView_prehitSuccessful_le_div_success_reference
    (secretKey : SecretKey) (message : Message)
    (referenceCache initialCache : QueryCache HashSpec)
    (P : FewTimeView → Prop)
    (hreference : referenceCache ≤ initialCache) (budget : Nat)
    (rate : ENNReal) (hpositive : rate ≠ 0)
    (hrate : rate ≤ (1 - (budget : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹)
    (hbudget : QueryCache.enncard initialCache + (digestAttemptLimit : ℝ≥0∞) ≤
      (budget : ENNReal)) :
    Pr[PrehitSuccessfulSignerView referenceCache secretKey message P |
      (simulateQ romImpl (signWithView secretKey message)).run initialCache] ≤
      cachedMessageEntryCountWhere referenceCache secretKey.parameter secretKey.root message P *
        (((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ / rate) := by
  rw [signWithView, simulateQ_bind, StateT.run_bind]
  refine (probEvent_bind_le_probEvent
    (p := PrehitSelectedView referenceCache secretKey message P) ?_).trans
    (probEvent_signDigestLoop_prehitSelectedView_le_div_success digestAttemptLimit
      secretKey message referenceCache initialCache P hreference budget hbudget rate hpositive hrate)
  intro loopResult hloop hnotPrehit
  cases hloopResult : loopResult.1 with
  | none =>
      refine probEvent_eq_zero ?_
      intro result hresult hevent
      have hresultEq : result = ((none, none), loopResult.2) := by
        simpa only [hloopResult, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hresult
      obtain ⟨signature, view, hsuccessful, _⟩ := hevent
      rw [hresultEq] at hsuccessful
      simp at hsuccessful
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      refine probEvent_eq_zero ?_
      intro result hresult hevent
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨⟨signatureResult, signatureCache⟩, hsignature, hpure⟩ := hresult
      have hpureEq : result =
          ((signatureResult, some (selectedFewTimeView index leaves)), signatureCache) := by
        simpa only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hpure
      obtain ⟨signature, view, hsuccessful, output, hcached, hP⟩ := hevent
      have hpureFirst := congrArg Prod.fst hpureEq
      have hsignatureResult : signatureResult = some signature := by
        have hfirst := congrArg Prod.fst (hpureFirst.symm.trans hsuccessful)
        simpa using hfirst
      have hsignature' : (some signature, signatureCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec _)
            (signAfterDigest secretKey randomness index leaves)).run loopResult.2) := by
        rw [hsignatureResult] at hsignature
        simpa only [simulateQ_romImpl_liftM] using hsignature
      have hrandomness := signAfterDigest_support_some_randomness secretKey randomness
        index leaves loopResult.2 signatureCache signature hsignature'
      have hcached' : initialCache
          (tweakableHashInput secretKey.parameter .message
            (messageDigestPayload secretKey.root message randomness)) = some output := by
        apply hreference
        rw [← hrandomness]
        exact hcached
      have hloop' : (some (randomness, index, leaves), loopResult.2) ∈ support
          ((simulateQ romImpl
            (signDigestLoop digestAttemptLimit secretKey message)).run initialCache) := by
        have heq : loopResult = (some (randomness, index, leaves), loopResult.2) :=
          Prod.ext hloopResult rfl
        rw [← heq]
        exact hloop
      have hresultOutput := signDigestLoop_initial_cached_result
        digestAttemptLimit secretKey message randomness index leaves initialCache loopResult.2
        output hcached' hloop'
      apply hnotPrehit
      exact ⟨randomness, index, leaves, hloopResult, output, by
        rw [← hrandomness]
        exact hcached, hresultOutput, hP⟩


theorem digestRaceSuccessRate_ne_zero_of_budget_lt
    (budget : Nat) (hbudget : budget < 2 ^ randomnessBits) :
    (1 - (budget : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ ≠ 0 := by
  have hfraction : (budget : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, ENNReal.div_lt_iff (by left; positivity) (by left; finiteness), one_mul]
    exact_mod_cast hbudget
  exact mul_ne_zero (ne_of_gt (tsub_pos_iff_lt.mpr hfraction)) (ENNReal.inv_ne_zero.mpr (by finiteness))

set_option linter.constructorNameAsVariable false in
theorem Concrete.probEvent_signWithView_prehitSuccessful_le_cacheBudget
    (secretKey : SecretKey) (message : Message) (referenceCache initialCache : QueryCache HashSpec)
    (P : FewTimeView → Prop) (hreference : referenceCache ≤ initialCache)
    (budget : Nat) (hbudget : budget < 2 ^ randomnessBits)
    (hcache : QueryCache.enncard initialCache + (digestAttemptLimit : ENNReal) ≤ budget) :
    Pr[PrehitSuccessfulSignerView referenceCache secretKey message P |
      (simulateQ romImpl (signWithView secretKey message)).run initialCache] ≤
      cachedMessageEntryCountWhere referenceCache secretKey.parameter secretKey.root message P *
        (((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ /
          ((1 - (budget : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
            ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹)) :=
  probEvent_signWithView_prehitSuccessful_le_div_success_reference secretKey message referenceCache initialCache P hreference
    budget _ (digestRaceSuccessRate_ne_zero_of_budget_lt budget hbudget) le_rfl hcache

set_option linter.constructorNameAsVariable false in
theorem Concrete.probEvent_signWithView_prehitSuccessful_le_queryBudget127
    (secretKey : SecretKey) (message : Message) (referenceCache initialCache : QueryCache HashSpec)
    (P : FewTimeView → Prop) (hreference : referenceCache ≤ initialCache)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard initialCache ≤ q) :
    Pr[PrehitSuccessfulSignerView referenceCache secretKey message P |
      (simulateQ romImpl (signWithView secretKey message)).run initialCache] ≤
      cachedMessageEntryCountWhere referenceCache secretKey.parameter secretKey.root message P *
        (((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ /
          ((1 - ((q + digestAttemptLimit : Nat) : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
            ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹)) := by
  apply probEvent_signWithView_prehitSuccessful_le_cacheBudget secretKey message referenceCache initialCache P hreference
    (q + digestAttemptLimit)
  · norm_num [digestAttemptLimit, randomnessBits] at *
    omega
  · simpa only [Nat.cast_add] using add_le_add hcache (le_refl (digestAttemptLimit : ENNReal))

theorem digestRaceSuccessRate_ge_two_thirds_of_queryBudget126 :
    (2 / 3 : ENNReal) * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ ≤
      (1 - ((2 ^ 126 + digestAttemptLimit : Nat) : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
        ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ := by
  apply mul_le_mul' _ le_rfl
  have hfraction : ((2 ^ 126 + digestAttemptLimit : Nat) : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ ≤ 1 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, digestAttemptLimit, randomnessBits]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_sub_of_le hfraction (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv, digestAttemptLimit, randomnessBits]

set_option linter.constructorNameAsVariable false in
theorem Concrete.probEvent_signWithView_prehitSuccessful_le_three_mul_inv119
    (secretKey : SecretKey) (message : Message) (referenceCache initialCache : QueryCache HashSpec)
    (P : FewTimeView → Prop) (hreference : referenceCache ≤ initialCache)
    (q : Nat) (hq : q ≤ 2 ^ 126) (hcache : QueryCache.enncard initialCache ≤ q) :
    Pr[PrehitSuccessfulSignerView referenceCache secretKey message P |
      (simulateQ romImpl (signWithView secretKey message)).run initialCache] ≤
      cachedMessageEntryCountWhere referenceCache secretKey.parameter secretKey.root message P *
        (3 * ((2 ^ 119 : Nat) : ENNReal)⁻¹) := by
  have hbudget : QueryCache.enncard initialCache + (digestAttemptLimit : ENNReal) ≤
      ((2 ^ 126 + digestAttemptLimit : Nat) : ENNReal) := by
    rw [Nat.cast_add]
    exact add_le_add (hcache.trans (Nat.cast_le.mpr hq)) le_rfl
  have hbound := probEvent_signWithView_prehitSuccessful_le_div_success_reference secretKey message referenceCache initialCache P
    hreference (2 ^ 126 + digestAttemptLimit) ((2 / 3 : ENNReal) * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹)
    (by norm_num [ftsTreeHeight]) digestRaceSuccessRate_ge_two_thirds_of_queryBudget126 hbudget
  have hweight : ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ /
      ((2 / 3 : ENNReal) * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹) = 3 * ((2 ^ 119 : Nat) : ENNReal)⁻¹ := by
    have hnonzero : (2 / 3 : ENNReal) * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ ≠ 0 := by norm_num [ftsTreeHeight]
    apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.div_ne_top (by finiteness) hnonzero) (by finiteness)).mp
    norm_num [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv, randomnessBits, ftsTreeHeight]
  simpa only [hweight] using hbound

end SphincsSecurity
