import SphincsSecurity.Proof.FewTimeFresh
import SphincsSecurity.Proof.CacheSize

/-!
# Cached signer views

The cached-input branch retains the predicate on the cached answer's few-time view. Its randomizer
reuse cost is charged only against cache entries that satisfy that predicate.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

def cachedMessageInputSetWhere (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (root : Digest) (message : Message) (P : Concrete.FewTimeView → Prop) :
    Set ((t : HashSpec.Domain) × HashSpec.Range t) :=
  {entry ∈ cachedMessageInputSet cache parameter root message |
    Concrete.signAttemptResultOfOutput entry.2 ≠ none
      ∧ P (Concrete.hashOutputFewTimeView entry.2)}

noncomputable def cachedMessageEntryCountWhere (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (P : Concrete.FewTimeView → Prop) : ℝ≥0∞ :=
  (((cachedMessageInputSetWhere cache parameter root message P).encard : ENat) : ℝ≥0∞)

theorem cachedMessageEntryCountWhere_le_enncard
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (root : Digest) (message : Message) (P : Concrete.FewTimeView → Prop) :
    cachedMessageEntryCountWhere cache parameter root message P ≤
      QueryCache.enncard cache := by
  have hsubset : cachedMessageInputSetWhere cache parameter root message P ⊆ cache.toSet := by
    intro entry hentry
    exact hentry.1.1
  simpa only [cachedMessageEntryCountWhere, QueryCache.enncard] using
    ENat.toENNReal_mono (Set.encard_le_encard hsubset)

theorem Concrete.gameAfterSecretsWithFullTrace_support_enncard_le
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound Concrete.scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support Concrete.sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support Concrete.sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support Concrete.sampleFtsSecrets)
    (result : (Digest × Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hresult : result ∈ support
      (Concrete.gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret)) :
    QueryCache.enncard result.2.1 ≤ q := by
  have hprojected : (result.1.2.2, result.2.1) ∈ support
      ((fun traced => (traced.1.2.2, traced.2.1)) <$>
        Concrete.gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
    rw [support_map]
    exact ⟨result, hresult, rfl⟩
  rw [Concrete.gameAfterSecretsWithFullTrace_projection] at hprojected
  exact simulateQ_romImpl_enncard_le_queryBound
    (Concrete.gameAfterSecrets adversary parameter otsSecret ftsSecret) q
    (Concrete.isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts)
    (result.1.2.2, result.2.1) hprojected

theorem Concrete.gameAfterSecretsWithFullTrace_signingEntry_cachedCountWhere_le
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound Concrete.scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support Concrete.sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support Concrete.sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support Concrete.sampleFtsSecrets)
    (result : (Digest × Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hresult : result ∈ support
      (Concrete.gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret))
    (entry : SigningCacheEntry) (hentry : entry ∈ result.2.2.signing)
    (P : Concrete.FewTimeView → Prop) :
    cachedMessageEntryCountWhere entry.initialCache parameter result.1.1 entry.request P ≤ q := by
  have hinvariants := Concrete.gameAfterSecretsWithFullTrace_support_invariants
    adversary parameter otsSecret ftsSecret result hresult
  calc
    cachedMessageEntryCountWhere entry.initialCache parameter result.1.1 entry.request P ≤
        QueryCache.enncard entry.initialCache :=
      cachedMessageEntryCountWhere_le_enncard entry.initialCache parameter result.1.1
        entry.request P
    _ ≤ QueryCache.enncard result.2.1 :=
      QueryCache.enncard_mono (hinvariants.2.1 entry hentry).1
    _ ≤ q := Concrete.gameAfterSecretsWithFullTrace_support_enncard_le adversary q hq
      parameter hparameter otsSecret hots ftsSecret hfts result hresult

set_option maxRecDepth 100000 in
theorem uniform_randomness_messageInput_cacheHitWhere_le_cachedCount
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (P : Concrete.FewTimeView → Prop) :
    Pr[fun randomness : Randomness => ∃ output,
      cache (tweakableHashInput parameter .message
        (Concrete.messageDigestPayload root message randomness)) = some output
        ∧ Concrete.signAttemptResultOfOutput output ≠ none
        ∧ P (Concrete.hashOutputFewTimeView output) |
      $ᵗ Randomness] ≤
      cachedMessageEntryCountWhere cache parameter root message P *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  let hit : Randomness → Prop := fun randomness => ∃ output,
    cache (tweakableHashInput parameter .message
      (Concrete.messageDigestPayload root message randomness)) = some output
      ∧ Concrete.signAttemptResultOfOutput output ≠ none
      ∧ P (Concrete.hashOutputFewTimeView output)
  let targets : Finset Randomness := Finset.univ.filter hit
  let fiber := cachedMessageInputSetWhere cache parameter root message P
  have hcard : (targets.card : ℝ≥0∞) ≤
      cachedMessageEntryCountWhere cache parameter root message P := by
    let embedding : (targets : Set Randomness) ↪ fiber :=
      ⟨fun randomness =>
          ⟨⟨tweakableHashInput parameter .message
                (Concrete.messageDigestPayload root message randomness.1),
              Classical.choose (Finset.mem_filter.mp randomness.2).2⟩,
            ⟨⟨Classical.choose_spec (Finset.mem_filter.mp randomness.2).2 |>.1,
                ⟨randomness.1, rfl⟩⟩,
              ⟨Classical.choose_spec (Finset.mem_filter.mp randomness.2).2 |>.2.1,
                Classical.choose_spec (Finset.mem_filter.mp randomness.2).2 |>.2.2⟩⟩⟩,
        fun left right heq => Subtype.ext <|
          (Concrete.messageDigestPayload_injective root <|
            (tweakableHashInput_injective parameter (by trivial) (by trivial) <|
              congrArg (fun entry : fiber => entry.1.1) heq).2).2⟩
    simpa only [cachedMessageEntryCountWhere, fiber,
      Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe] using
      ENat.toENNReal_mono embedding.encard_le
  rw [probEvent_uniformSample, card_randomness, div_eq_mul_inv]
  change (targets.card : ℝ≥0∞) *
      ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ ≤ _
  exact mul_le_mul' hcard le_rfl

def Concrete.PrehitSelectedView (referenceCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (P : Concrete.FewTimeView → Prop)
    (result : Option (Randomness × Index × (DigestTree → FtsLeaf)) ×
      QueryCache HashSpec) : Prop :=
  ∃ randomness index leaves,
    result.1 = some (randomness, index, leaves)
      ∧ ∃ output, referenceCache
        (tweakableHashInput secretKey.parameter .message
          (Concrete.messageDigestPayload secretKey.root message randomness)) = some output
        ∧ Concrete.signAttemptResultOfOutput output = some (index, leaves)
        ∧ P (Concrete.hashOutputFewTimeView output)

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.probEvent_signDigestLoop_prehitSelectedView_le_cachedCount
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (P : Concrete.FewTimeView → Prop) :
    Pr[Concrete.PrehitSelectedView referenceCache secretKey message P |
      (simulateQ romImpl
        (Concrete.signDigestLoop attempts secretKey message)).run workingCache] ≤
      (attempts : ℝ≥0∞) *
        cachedMessageEntryCountWhere referenceCache secretKey.parameter secretKey.root message P *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction attempts generalizing workingCache with
  | zero =>
      refine le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
      intro result hresult hevent
      have hresultEq : result = (none, workingCache) := by
        simpa only [Concrete.signDigestLoop, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hresult
      obtain ⟨randomness, index, leaves, hselected, _⟩ := hevent
      rw [hresultEq] at hselected
      simp at hselected
  | succ attempts ih =>
      rw [Concrete.signDigestLoop_run_succ_eq]
      refine (probEvent_bind_le_probEvent_add
        (p := fun randomness : Randomness => ∃ output,
          referenceCache
            (tweakableHashInput secretKey.parameter .message
              (Concrete.messageDigestPayload secretKey.root message randomness)) = some output
            ∧ Concrete.signAttemptResultOfOutput output ≠ none
            ∧ P (Concrete.hashOutputFewTimeView output))
        (ε := (attempts : ℝ≥0∞) *
          cachedMessageEntryCountWhere referenceCache secretKey.parameter secretKey.root message P *
          ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
      · intro randomness _hrandomness hmiss
        refine probEvent_bind_le_of_forall_le fun attemptResult _hattempt => ?_
        cases hresult : attemptResult.1 with
        | none =>
            simpa only [Concrete.signDigestLoopContinuation, hresult] using
              ih attemptResult.2
        | some selected =>
            rcases selected with ⟨selectedIndex, selectedLeaves⟩
            refine le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
            intro result hsupport hevent
            have hsupport' : result =
                (some (randomness, selectedIndex, selectedLeaves), attemptResult.2) := by
              simpa only [Concrete.signDigestLoopContinuation, hresult, support_pure,
                Set.mem_singleton_iff] using hsupport
            obtain ⟨foundRandomness, foundIndex, foundLeaves, hfound, output, hhit,
              houtputResult, hP⟩ := hevent
            have hrandomness : randomness = foundRandomness := by
              have htuple : (randomness, selectedIndex, selectedLeaves) =
                  (foundRandomness, foundIndex, foundLeaves) :=
                Option.some.inj ((congrArg Prod.fst hsupport').symm.trans hfound)
              exact congrArg Prod.fst htuple
            apply hmiss
            refine ⟨output, ?_, ?_, hP⟩
            · rw [hrandomness]
              exact hhit
            · rw [houtputResult]
              simp
      · calc
          _ ≤ cachedMessageEntryCountWhere referenceCache secretKey.parameter
                secretKey.root message P *
                ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹
              + (attempts : ℝ≥0∞) *
                cachedMessageEntryCountWhere referenceCache secretKey.parameter
                  secretKey.root message P *
                ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ :=
            add_le_add
              (uniform_randomness_messageInput_cacheHitWhere_le_cachedCount
                secretKey.parameter secretKey.root message referenceCache P) le_rfl
          _ = _ := by
            push_cast
            ring

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.signDigestLoop_initial_cached_result
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (initialCache finalCache : QueryCache HashSpec) (output : HashOutput)
    (hcached : initialCache
      (tweakableHashInput secretKey.parameter .message
        (Concrete.messageDigestPayload secretKey.root message randomness)) = some output)
    (hmem : (some (randomness, index, leaves), finalCache) ∈ support
      ((simulateQ romImpl
        (Concrete.signDigestLoop attempts secretKey message)).run initialCache)) :
    Concrete.signAttemptResultOfOutput output = some (index, leaves) := by
  induction attempts generalizing initialCache finalCache with
  | zero =>
      simp [Concrete.signDigestLoop] at hmem
  | succ attempts ih =>
      rw [Concrete.signDigestLoop_run_succ_eq, mem_support_bind_iff] at hmem
      obtain ⟨sampled, _hsampled, hrest⟩ := hmem
      rw [mem_support_bind_iff] at hrest
      obtain ⟨⟨attempt, attemptCache⟩, hattempt, hfinish⟩ := hrest
      have hattempt' : (attempt, attemptCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec _)
            (Concrete.signAttempt secretKey message sampled)).run initialCache) := by
        exact hattempt
      have hle : initialCache ≤ attemptCache :=
        simulateQ_romImpl_cache_le
          (liftM (Concrete.signAttempt secretKey message sampled :
            OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))) :
              OracleComp OracleWorld (Option (Index × (DigestTree → FtsLeaf))))
          initialCache (attempt, attemptCache) (by
            rw [simulateQ_romImpl_liftM]
            exact hattempt)
      cases hattemptResult : attempt with
      | none =>
          have hfuture : (some (randomness, index, leaves), finalCache) ∈ support
              ((simulateQ romImpl
                (Concrete.signDigestLoop attempts secretKey message)).run attemptCache) := by
            simpa only [Concrete.signDigestLoopContinuation, hattemptResult] using hfinish
          exact ih attemptCache finalCache (hle hcached) hfuture
      | some selected =>
          rcases selected with ⟨selectedIndex, selectedLeaves⟩
          have hfinishEq :
              (some (randomness, index, leaves), finalCache) =
                (some (sampled, selectedIndex, selectedLeaves), attemptCache) := by
            simpa only [Concrete.signDigestLoopContinuation, hattemptResult, support_pure,
              Set.mem_singleton_iff] using hfinish
          have htuple : (randomness, index, leaves) =
              (sampled, selectedIndex, selectedLeaves) :=
            Option.some.inj (congrArg Prod.fst hfinishEq)
          have hrandomness : randomness = sampled := congrArg Prod.fst htuple
          have hcached' : attemptCache
              (tweakableHashInput secretKey.parameter .message
                (Concrete.messageDigestPayload secretKey.root message sampled)) = some output :=
            hle (by
              rw [← hrandomness]
              exact hcached)
          have hattemptSelected : (some (selectedIndex, selectedLeaves), attemptCache) ∈ support
              ((simulateQ (randomOracle : QueryImpl HashSpec _)
                (Concrete.signAttempt secretKey message sampled)).run initialCache) := by
            have heq : (attempt, attemptCache) =
                (some (selectedIndex, selectedLeaves), attemptCache) :=
              Prod.ext hattemptResult rfl
            rw [← heq]
            exact hattempt'
          have hselectedResult :=
            (Concrete.signAttempt_result_of_cached secretKey message sampled initialCache
              attemptCache (some (selectedIndex, selectedLeaves)) output hcached'
              hattemptSelected).symm
          exact hselectedResult.trans (congrArg some (congrArg Prod.snd htuple).symm)

def Concrete.PrehitSuccessfulSignerView (initialCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (P : Concrete.FewTimeView → Prop)
    (result : (Option Signature × Option Concrete.FewTimeView) × QueryCache HashSpec) : Prop :=
  ∃ signature view,
    result.1 = (some signature, some view)
      ∧ ∃ output, initialCache
        (tweakableHashInput secretKey.parameter .message
          (Concrete.messageDigestPayload secretKey.root message signature.randomness)) = some output
        ∧ P (Concrete.hashOutputFewTimeView output)

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.probEvent_signWithView_prehitSuccessful_le_cachedCount
    (secretKey : SecretKey) (message : Message) (initialCache : QueryCache HashSpec)
    (P : Concrete.FewTimeView → Prop) :
    Pr[Concrete.PrehitSuccessfulSignerView initialCache secretKey message P |
      (simulateQ romImpl (Concrete.signWithView secretKey message)).run initialCache] ≤
      (digestAttemptLimit : ℝ≥0∞) *
        cachedMessageEntryCountWhere initialCache secretKey.parameter secretKey.root message P *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [Concrete.signWithView, simulateQ_bind, StateT.run_bind]
  refine (probEvent_bind_le_probEvent
    (p := Concrete.PrehitSelectedView initialCache secretKey message P) ?_).trans
    (Concrete.probEvent_signDigestLoop_prehitSelectedView_le_cachedCount
      digestAttemptLimit secretKey message initialCache initialCache P)
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
          ((signatureResult, some (Concrete.selectedFewTimeView index leaves)),
            signatureCache) := by
        simpa only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hpure
      obtain ⟨signature, view, hsuccessful, output, hcached, hP⟩ := hevent
      have hpureFirst := congrArg Prod.fst hpureEq
      have hsignatureResult : signatureResult = some signature := by
        have := congrArg Prod.fst (hpureFirst.symm.trans hsuccessful)
        simpa using this
      have hsignature' : (some signature, signatureCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec _)
            (Concrete.signAfterDigest secretKey randomness index leaves)).run loopResult.2) := by
        rw [hsignatureResult] at hsignature
        simpa only [simulateQ_romImpl_liftM] using hsignature
      have hrandomness := Concrete.signAfterDigest_support_some_randomness secretKey randomness
        index leaves loopResult.2 signatureCache signature hsignature'
      have hcached' : initialCache
          (tweakableHashInput secretKey.parameter .message
            (Concrete.messageDigestPayload secretKey.root message randomness)) = some output := by
        rw [← hrandomness]
        exact hcached
      have hloop' : (some (randomness, index, leaves), loopResult.2) ∈ support
          ((simulateQ romImpl
            (Concrete.signDigestLoop digestAttemptLimit secretKey message)).run initialCache) := by
        have heq : loopResult = (some (randomness, index, leaves), loopResult.2) :=
          Prod.ext hloopResult rfl
        rw [← heq]
        exact hloop
      have hresultOutput := Concrete.signDigestLoop_initial_cached_result
        digestAttemptLimit secretKey message randomness index leaves initialCache loopResult.2
        output hcached' hloop'
      apply hnotPrehit
      refine ⟨randomness, index, leaves, hloopResult, output, hcached', hresultOutput, ?_⟩
      exact hP

end SphincsSecurity
