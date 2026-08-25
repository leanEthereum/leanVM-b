import SphincsSecurity.Proof.FewTimePrehitArith

/-!
# A weighted prefix split for the digest race

The cached branch of a digest retry loop wins immediately, a rejected answer continues, and an
ordinary successful answer ends the event. The weighted split below keeps the continuation
probability instead of paying one full copy of its bound at every retry.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

theorem cachedMessageEntryCount_le_enncard
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (root : Digest) (message : Message) :
    cachedMessageEntryCount cache parameter root message ≤ QueryCache.enncard cache := by
  have hsubset : cachedMessageInputSet cache parameter root message ⊆ cache.toSet := by
    intro entry hentry
    exact hentry.1
  simpa only [cachedMessageEntryCount, QueryCache.enncard] using
    ENat.toENNReal_mono (Set.encard_le_encard hsubset)

set_option maxRecDepth 100000 in
theorem Concrete.probEvent_signAttempt_fresh_success_eq
    (secretKey : SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec)
    (hcache : cache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = none) :
    Pr[fun result => result.1 ≠ none |
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAttempt secretKey message randomness)).run cache] =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ := by
  have hcoordinates := evalDist_signAttempt_fresh_bind_coordinates
    secretKey message randomness cache hcache
    (fun result => pure result)
  simp only [bind_pure] at hcoordinates
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hcoordinates]
  change Pr[fun result => result.1 ≠ none |
    ($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>=
      pure ∘ fun coordinates =>
        (signAttemptResultOfOutput (hashOutputCoordinatesEquiv.symm coordinates),
          cache.cacheQuery
            (tweakableHashInput secretKey.parameter .message
              (messageDigestPayload secretKey.root message randomness))
            (hashOutputCoordinatesEquiv.symm coordinates))] = _
  rw [probEvent_bind_pure_comp]
  let event : HashOutputCoordinates → Prop := fun coordinates => coordinates.1.2 = 0
  calc
    Pr[fun coordinates : HashOutputCoordinates =>
        (signAttemptResultOfOutput (hashOutputCoordinatesEquiv.symm coordinates),
          cache.cacheQuery
            (tweakableHashInput secretKey.parameter .message
              (messageDigestPayload secretKey.root message randomness))
            (hashOutputCoordinatesEquiv.symm coordinates)).1 ≠ none |
        ($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] =
        Pr[event | ($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] := by
      apply probEvent_congr'
      · intro coordinates _
        exact signAttemptResultOfOutput_coordinates_ne_none_iff coordinates
      · rfl
    _ = Pr[fun coordinates : FewTimeView × FtsLeaf => coordinates.2 = 0 |
        Prod.fst <$> ($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun coordinates : FewTimeView × FtsLeaf => coordinates.2 = 0 |
        ($ᵗ (FewTimeView × FtsLeaf) : ProbComp (FewTimeView × FtsLeaf))] := by
      apply probEvent_congr'
      · intro coordinates _
        rfl
      · exact evalDist_map_fst_uniformSample_prod
    _ = _ := by
      simpa only [and_true, probEvent_True_eq_sub, probFailure_of_liftM_PMF,
        tsub_zero, mul_one] using
        probEvent_uniformDigestCoordinates_admissible_view (fun _ => True)

theorem Concrete.signAttempt_enncard_le
    (secretKey : SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec)
    (result : Option (Index × (DigestTree → FtsLeaf)) × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAttempt secretKey message randomness)).run cache)) :
    QueryCache.enncard result.2 ≤ QueryCache.enncard cache + 1 := by
  rw [simulateQ_signAttempt_run_eq, mem_support_bind_iff] at hresult
  obtain ⟨oracleResult, horacle, hpure⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact romImpl_hash_query_enncard_le
    (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness))
    cache oracleResult horacle

set_option maxRecDepth 100000 in
theorem uniform_randomness_messageInput_cacheHit_le_two_neg_seven
    (secretKey : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hcache : QueryCache.enncard cache ≤ ((2 ^ 121 : Nat) : ℝ≥0∞)) :
    Pr[fun randomness : Randomness => ∃ output,
      cache (tweakableHashInput secretKey.parameter .message
        (Concrete.messageDigestPayload secretKey.root message randomness)) = some output |
      $ᵗ Randomness] ≤ ((2 ^ 7 : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ cachedMessageEntryCount cache secretKey.parameter secretKey.root message *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ :=
      uniform_randomness_messageInput_cacheHit_le_cachedMessageEntryCount
        secretKey.parameter secretKey.root message cache
    _ ≤ ((2 ^ 121 : Nat) : ℝ≥0∞) *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
      gcongr
      exact (cachedMessageEntryCount_le_enncard cache secretKey.parameter
        secretKey.root message).trans hcache
    _ = ((2 ^ 7 : Nat) : ℝ≥0∞)⁻¹ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      norm_num [randomnessBits]

set_option maxRecDepth 100000 in
theorem uniform_randomness_messageInput_cacheMiss_ge_one_sub_two_neg_seven
    (secretKey : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hcache : QueryCache.enncard cache ≤ ((2 ^ 121 : Nat) : ℝ≥0∞)) :
    1 - ((2 ^ 7 : Nat) : ℝ≥0∞)⁻¹ ≤
      Pr[fun randomness : Randomness =>
        cache (tweakableHashInput secretKey.parameter .message
          (Concrete.messageDigestPayload secretKey.root message randomness)) = none |
        $ᵗ Randomness] := by
  let miss : Randomness → Prop := fun randomness =>
    cache (tweakableHashInput secretKey.parameter .message
      (Concrete.messageDigestPayload secretKey.root message randomness)) = none
  apply probEvent_one_sub_le_of_compl_le (by simp only [probFailure_of_liftM_PMF])
  calc
    Pr[fun randomness => ¬ miss randomness | $ᵗ Randomness] =
        Pr[fun randomness : Randomness => ∃ output,
          cache (tweakableHashInput secretKey.parameter .message
            (Concrete.messageDigestPayload secretKey.root message randomness)) = some output |
          $ᵗ Randomness] := by
      apply probEvent_congr'
      · intro randomness _
        exact Option.ne_none_iff_exists'
      · rfl
    _ ≤ _ := uniform_randomness_messageInput_cacheHit_le_two_neg_seven
      secretKey message cache hcache

noncomputable def Concrete.signDigestAttemptPrefix
    (secretKey : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    ProbComp (Randomness ×
      (Option (Index × (DigestTree → FtsLeaf)) × QueryCache HashSpec)) :=
  ($ᵗ Randomness) >>= fun randomness =>
    (simulateQ (randomOracle : QueryImpl HashSpec _)
      (signAttempt secretKey message randomness)).run cache >>= fun result =>
        pure (randomness, result)

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.probEvent_signDigestAttemptPrefix_success_ge
    (secretKey : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hcache : QueryCache.enncard cache ≤ ((2 ^ 121 : Nat) : ℝ≥0∞)) :
    ((2 ^ 11 : Nat) : ℝ≥0∞)⁻¹ ≤
      Pr[fun attempt => attempt.2.1 ≠ none |
        signDigestAttemptPrefix secretKey message cache] := by
  have harithmetic : ((2 ^ 11 : Nat) : ℝ≥0∞)⁻¹ ≤
      (1 - ((2 ^ 7 : Nat) : ℝ≥0∞)⁻¹) *
        ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_sub_of_le (by norm_num) (by finiteness)]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_one]
    norm_num [ftsTreeHeight]
  refine harithmetic.trans ?_
  rw [signDigestAttemptPrefix]
  apply mul_le_probEvent_bind
  · exact uniform_randomness_messageInput_cacheMiss_ge_one_sub_two_neg_seven
      secretKey message cache hcache
  · intro randomness _hrandomness hmiss
    change ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ ≤
      Pr[fun attempt => attempt.2.1 ≠ none |
        (simulateQ (randomOracle : QueryImpl HashSpec _)
          (signAttempt secretKey message randomness)).run cache >>= fun result =>
            pure (randomness, result)]
    rw [show (fun result => pure (randomness, result)) =
      pure ∘ fun result => (randomness, result) from rfl,
      probEvent_bind_pure_comp]
    exact le_of_eq (probEvent_signAttempt_fresh_success_eq
      secretKey message randomness cache hmiss).symm

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.probEvent_signDigestAttemptPrefix_retry_le
    (secretKey : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hcache : QueryCache.enncard cache ≤ ((2 ^ 121 : Nat) : ℝ≥0∞)) :
    Pr[fun attempt => attempt.2.1 = none |
      signDigestAttemptPrefix secretKey message cache] ≤
      1 - ((2 ^ 11 : Nat) : ℝ≥0∞)⁻¹ := by
  have hcompl := probEvent_compl_le_of_one_sub_le
    (mx := signDigestAttemptPrefix secretKey message cache)
    (p := fun attempt => attempt.2.1 ≠ none)
    (ε := 1 - ((2 ^ 11 : Nat) : ℝ≥0∞)⁻¹)
    (by simp [signDigestAttemptPrefix]) (by
      calc
      1 - (1 - ((2 ^ 11 : Nat) : ℝ≥0∞)⁻¹) =
          ((2 ^ 11 : Nat) : ℝ≥0∞)⁻¹ := by
        exact ENNReal.sub_sub_cancel (by simp) (by norm_num)
      _ ≤ _ := probEvent_signDigestAttemptPrefix_success_ge
        secretKey message cache hcache)
  simpa only [not_ne_iff] using hcompl

theorem Concrete.signDigestLoop_run_succ_eq_attemptPrefix
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl
      (signDigestLoop (attempts + 1) secretKey message)).run cache =
      signDigestAttemptPrefix secretKey message cache >>= fun attempt =>
        signDigestLoopContinuation attempts secretKey message attempt.1 attempt.2 := by
  rw [signDigestLoop_run_succ_eq, signDigestAttemptPrefix]
  simp only [bind_assoc, pure_bind]

def Concrete.FavorablePrehitAttempt (referenceCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (P : FewTimeView → Prop)
    (attempt : Randomness ×
      (Option (Index × (DigestTree → FtsLeaf)) × QueryCache HashSpec)) : Prop :=
  ∃ output, referenceCache
    (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message attempt.1)) = some output
    ∧ signAttemptResultOfOutput output ≠ none
    ∧ P (hashOutputFewTimeView output)

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.probEvent_signDigestAttemptPrefix_favorablePrehit_le
    (referenceCache workingCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (P : FewTimeView → Prop) :
    Pr[FavorablePrehitAttempt referenceCache secretKey message P |
      signDigestAttemptPrefix secretKey message workingCache] ≤
      cachedMessageEntryCountWhere referenceCache secretKey.parameter secretKey.root message P *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [signDigestAttemptPrefix]
  refine (probEvent_bind_le_probEvent
    (p := fun randomness : Randomness => ∃ output,
      referenceCache
        (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness)) = some output
      ∧ signAttemptResultOfOutput output ≠ none
      ∧ P (hashOutputFewTimeView output)) ?_).trans
    (uniform_randomness_messageInput_cacheHitWhere_le_cachedCount
      secretKey.parameter secretKey.root message referenceCache P)
  intro randomness _hrandomness hnotFavorable
  refine probEvent_eq_zero ?_
  intro attempt hattempt hevent
  rw [mem_support_bind_iff] at hattempt
  obtain ⟨attemptResult, _hattemptResult, hpure⟩ := hattempt
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  obtain ⟨output, hcached, hsuccessful, hP⟩ := hevent
  apply hnotFavorable
  refine ⟨output, ?_, hsuccessful, hP⟩
  rw [congrArg Prod.fst hpure] at hcached
  exact hcached

theorem probEvent_bind_le_probEvent_add_mul
    {m : Type _ → Type _} [Monad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m]
    {alpha beta : Type} {mx : m alpha} {my : alpha → m beta}
    {event : beta → Prop} {hit retry : alpha → Prop} {epsilon : ℝ≥0∞}
    (hoff : ∀ x ∈ support mx, ¬ hit x → ¬ retry x →
      Pr[event | my x] = 0)
    (hretry : ∀ x ∈ support mx, retry x → Pr[event | my x] ≤ epsilon) :
    Pr[event | mx >>= my] ≤
      Pr[hit | mx] + Pr[retry | mx] * epsilon := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_indicator,
    probEvent_eq_tsum_indicator]
  calc
    ∑' x, Pr[= x | mx] * Pr[event | my x] ≤
        ∑' x, ({x | hit x}.indicator (fun y => Pr[= y | mx]) x +
          {x | retry x}.indicator (fun y => Pr[= y | mx] * epsilon) x) := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases hx : x ∈ support mx
      · by_cases hhit : hit x
        · calc
            Pr[= x | mx] * Pr[event | my x] ≤ Pr[= x | mx] := by
              simpa only [mul_one] using mul_le_mul' le_rfl probEvent_le_one
            _ ≤ {x | hit x}.indicator (fun y => Pr[= y | mx]) x +
                {x | retry x}.indicator (fun y => Pr[= y | mx] * epsilon) x := by
              simp [hhit]
        · by_cases hrx : retry x
          · calc
              Pr[= x | mx] * Pr[event | my x] ≤
                  Pr[= x | mx] * epsilon := mul_le_mul' le_rfl (hretry x hx hrx)
              _ = {x | hit x}.indicator (fun y => Pr[= y | mx]) x +
                  {x | retry x}.indicator (fun y => Pr[= y | mx] * epsilon) x := by
                simp [hhit, hrx]
          · rw [hoff x hx hhit hrx]
            simp [hhit, hrx]
      · rw [probOutput_eq_zero_of_not_mem_support hx]
        simp
    _ = (∑' x, {x | hit x}.indicator (fun y => Pr[= y | mx]) x) +
        ∑' x, {x | retry x}.indicator (fun y => Pr[= y | mx] * epsilon) x :=
      ENNReal.tsum_add
    _ = (∑' x, {x | hit x}.indicator (fun y => Pr[= y | mx]) x) +
        (∑' x, {x | retry x}.indicator (fun y => Pr[= y | mx]) x) * epsilon := by
      rw [← ENNReal.tsum_mul_right]
      congr 1
      apply tsum_congr
      intro x
      by_cases hrx : retry x <;> simp [hrx]

theorem prehit_race_recurrence_arith (count : ℝ≥0∞) (hcount : count ≠ ∞) :
    count * ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ +
        (1 - ((2 ^ 11 : Nat) : ℝ≥0∞)⁻¹) *
          (count * ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹) ≤
      count * ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul]
  rw [ENNReal.toReal_sub_of_le (by norm_num) (by finiteness)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_one]
  norm_num [randomnessBits]
  ring_nf
  exact le_rfl

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.probEvent_signDigestLoop_prehitSelectedView_le_race
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (P : FewTimeView → Prop)
    (hreference : referenceCache ≤ workingCache)
    (hbudget : QueryCache.enncard workingCache + (attempts : ℝ≥0∞) ≤
      ((2 ^ 121 : Nat) : ℝ≥0∞)) :
    Pr[PrehitSelectedView referenceCache secretKey message P |
      (simulateQ romImpl
        (signDigestLoop attempts secretKey message)).run workingCache] ≤
      cachedMessageEntryCountWhere referenceCache secretKey.parameter secretKey.root message P *
        ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ := by
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
      let epsilon := count * ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹
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
            ((2 ^ 121 : Nat) : ℝ≥0∞) := by
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
            ((2 ^ 121 : Nat) : ℝ≥0∞) :=
          (le_add_right le_rfl).trans hbudget
        have hcountLe : count ≤ QueryCache.enncard workingCache := by
          exact (cachedMessageEntryCountWhere_le_enncard referenceCache secretKey.parameter
            secretKey.root message P).trans (QueryCache.enncard_mono hreference)
        calc
          Pr[FavorablePrehitAttempt referenceCache secretKey message P |
              signDigestAttemptPrefix secretKey message workingCache] +
                Pr[fun attempt => attempt.2.1 = none |
                  signDigestAttemptPrefix secretKey message workingCache] * epsilon ≤
              count * ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ +
                (1 - ((2 ^ 11 : Nat) : ℝ≥0∞)⁻¹) * epsilon := by
            gcongr
            · exact probEvent_signDigestAttemptPrefix_favorablePrehit_le
                referenceCache workingCache secretKey message P
            · exact probEvent_signDigestAttemptPrefix_retry_le
                secretKey message workingCache hworkingBudget
          _ ≤ count * ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ := by
            exact prehit_race_recurrence_arith count
              (ne_top_of_le_ne_top (by finiteness) (hcountLe.trans hworkingBudget))
          _ = _ := rfl

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.probEvent_signWithView_prehitSuccessful_le_race
    (secretKey : SecretKey) (message : Message) (initialCache : QueryCache HashSpec)
    (P : FewTimeView → Prop)
    (hbudget : QueryCache.enncard initialCache + (digestAttemptLimit : ℝ≥0∞) ≤
      ((2 ^ 121 : Nat) : ℝ≥0∞)) :
    Pr[PrehitSuccessfulSignerView initialCache secretKey message P |
      (simulateQ romImpl (signWithView secretKey message)).run initialCache] ≤
      cachedMessageEntryCountWhere initialCache secretKey.parameter secretKey.root message P *
        ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [signWithView, simulateQ_bind, StateT.run_bind]
  refine (probEvent_bind_le_probEvent
    (p := PrehitSelectedView initialCache secretKey message P) ?_).trans
    (probEvent_signDigestLoop_prehitSelectedView_le_race digestAttemptLimit
      secretKey message initialCache initialCache P le_rfl hbudget)
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
      exact ⟨randomness, index, leaves, hloopResult, output, hcached', hresultOutput, hP⟩

theorem Concrete.probEvent_signWithView_prehitSuccessful_le_race_of_enncard_le
    (secretKey : SecretKey) (message : Message) (initialCache : QueryCache HashSpec)
    (P : FewTimeView → Prop) (q : Nat) (hq : q ≤ 2 ^ 120)
    (hcache : QueryCache.enncard initialCache ≤ q) :
    Pr[PrehitSuccessfulSignerView initialCache secretKey message P |
      (simulateQ romImpl (signWithView secretKey message)).run initialCache] ≤
      cachedMessageEntryCountWhere initialCache secretKey.parameter secretKey.root message P *
        ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ := by
  apply probEvent_signWithView_prehitSuccessful_le_race
  have hq' : (q : ℝ≥0∞) ≤ ((2 ^ 120 : Nat) : ℝ≥0∞) := by
    exact_mod_cast hq
  calc
    QueryCache.enncard initialCache + (digestAttemptLimit : ℝ≥0∞) ≤
        (q : ℝ≥0∞) + (digestAttemptLimit : ℝ≥0∞) :=
      add_le_add hcache le_rfl
    _ ≤ ((2 ^ 120 : Nat) : ℝ≥0∞) + (digestAttemptLimit : ℝ≥0∞) :=
      add_le_add hq' le_rfl
    _ ≤ ((2 ^ 121 : Nat) : ℝ≥0∞) := by
      norm_num [digestAttemptLimit]

end SphincsSecurity
