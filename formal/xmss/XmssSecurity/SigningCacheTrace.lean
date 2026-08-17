import XmssSecurity.SignCacheHitProbability
import XmssSecurity.SigningLogReplay
import XmssSecurity.ConcreteQueryBound

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

structure SigningCacheEntry where
  request : SignRequest
  signature : Option Signature
  initialCache : QueryCache HashSpec
  finalCache : QueryCache HashSpec

abbrev SigningCacheTrace := List SigningCacheEntry

def SigningCacheTrace.CachesLe
    (trace : SigningCacheTrace) (cache : QueryCache HashSpec) : Prop :=
  ∀ entry ∈ trace, entry.initialCache ≤ cache ∧ entry.finalCache ≤ cache

/-- Signing snapshots occur in cache order: every earlier signing cache is contained in the initial cache of every later signing step. -/
def SigningCacheTrace.Chronological (trace : SigningCacheTrace) : Prop :=
  trace.Pairwise fun earlier later => earlier.finalCache ≤ later.initialCache

def SigningCacheTrace.toSigningLog (trace : SigningCacheTrace) : QueryLog SigningSpec :=
  trace.map fun entry => ⟨entry.request, entry.signature⟩

theorem SigningTranscript.returned_toSigningLog_iff
    (trace : SigningCacheTrace) (request : SignRequest) (signature : Signature) :
    SigningTranscript.Returned trace.toSigningLog request signature ↔
      ∃ entry ∈ trace,
        entry.request = request ∧ entry.signature = some signature := by
  constructor
  · rintro ⟨loggedEntry, hlogged, hrequest, hsignature⟩
    rw [SigningCacheTrace.toSigningLog, List.mem_map] at hlogged
    obtain ⟨entry, hentry, heq⟩ := hlogged
    subst loggedEntry
    exact ⟨entry, hentry, hrequest, hsignature⟩
  · rintro ⟨entry, hentry, hrequest, hsignature⟩
    refine ⟨⟨entry.request, entry.signature⟩, ?_, hrequest, hsignature⟩
    exact List.mem_map.mpr ⟨entry, hentry, rfl⟩

def SigningCacheEntry.EncodingInputPrehit
    (secretKey : SecretKey) (entry : SigningCacheEntry) : Prop :=
  ∃ signature output,
    entry.signature = some signature ∧
    entry.initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch
        (entry.request.message, signature.randomness)) = some output

def SigningCacheEntry.PreexistingEncodingCollision
    (secretKey : SecretKey) (entry : SigningCacheEntry) : Prop :=
  ∃ signature signedOutput oldInput oldOutput,
    entry.signature = some signature ∧
    entry.finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch
        (entry.request.message, signature.randomness)) = some signedOutput ∧
    entry.initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch oldInput) =
        some oldOutput ∧
    oldInput ≠ (entry.request.message, signature.randomness) ∧
    truncateHash signedOutput = truncateHash oldOutput

def SigningCacheEntry.FreshSigningEncodingCollision
    (secretKey : SecretKey) (entry : SigningCacheEntry) : Prop :=
  ∃ signature signedOutput oldInput oldOutput,
    entry.signature = some signature ∧
    entry.initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch
        (entry.request.message, signature.randomness)) = none ∧
    entry.finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch
        (entry.request.message, signature.randomness)) = some signedOutput ∧
    entry.initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch oldInput) =
        some oldOutput ∧
    oldInput ≠ (entry.request.message, signature.randomness) ∧
    truncateHash signedOutput = truncateHash oldOutput

def SigningCacheEntry.FreshForgedEncodingCollision
    (secretKey : SecretKey) (forgery : Forgery)
    (finalCache : QueryCache HashSpec) (entry : SigningCacheEntry) : Prop :=
  ∃ signature signedOutput forgedOutput,
    entry.signature = some signature ∧
    entry.request.epoch = forgery.epoch ∧
    entry.initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness)) = none ∧
    entry.finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch
        (entry.request.message, signature.randomness)) = some signedOutput ∧
    finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness)) = some forgedOutput ∧
    Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch
        (entry.request.message, signature.randomness) ≠
      Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness) ∧
    truncateHash signedOutput = truncateHash forgedOutput

def SigningCacheEntry.PostSigningFreshForgedEncodingCollision
    (secretKey : SecretKey) (forgery : Forgery)
    (finalCache : QueryCache HashSpec) (entry : SigningCacheEntry) : Prop :=
  entry.FreshForgedEncodingCollision secretKey forgery finalCache ∧
    entry.finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness)) = none ∧
    ∃ signature, entry.signature = some signature ∧
      entry.initialCache
        (Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch
          (entry.request.message, signature.randomness)) = none

def SigningCacheEntry.SuccessfulEncodingCached
    (secretKey : SecretKey) (entry : SigningCacheEntry) : Prop :=
  ∀ signature, entry.signature = some signature →
    ∃ output, entry.finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch
        (entry.request.message, signature.randomness)) = some output

def SigningCacheTrace.SuccessfulEncodingsCached
    (secretKey : SecretKey) (trace : SigningCacheTrace) : Prop :=
  ∀ entry ∈ trace, entry.SuccessfulEncodingCached secretKey

/-- A signing step cannot create a distinct encoding input that was absent before the step. -/
def SigningCacheEntry.PreservesOtherEncodingInputs
    (secretKey : SecretKey) (entry : SigningCacheEntry) : Prop :=
  ∀ signature, entry.signature = some signature →
    ∀ targetEpoch targetInput,
      Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch
          (entry.request.message, signature.randomness) ≠
        Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput →
      entry.initialCache
          (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none →
      entry.finalCache
          (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none

def SigningCacheTrace.PreservesOtherEncodingInputs
    (secretKey : SecretKey) (trace : SigningCacheTrace) : Prop :=
  ∀ entry ∈ trace, entry.PreservesOtherEncodingInputs secretKey

theorem SigningCacheEntry.preexistingEncodingCollision_cases
    (secretKey : SecretKey) (entry : SigningCacheEntry)
    (hevent : entry.PreexistingEncodingCollision secretKey) :
    entry.EncodingInputPrehit secretKey ∨
      entry.FreshSigningEncodingCollision secretKey := by
  obtain ⟨signature, signedOutput, oldInput, oldOutput, hsignature,
    hsigned, hold, hne, hdigest⟩ := hevent
  cases hinitial : entry.initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch
        (entry.request.message, signature.randomness)) with
  | none =>
      exact Or.inr ⟨signature, signedOutput, oldInput, oldOutput, hsignature,
        hinitial, hsigned, hold, hne, hdigest⟩
  | some output =>
      exact Or.inl ⟨signature, output, hsignature, hinitial⟩

theorem signingCacheEntry_encodingInputPrehit_probability_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (initialCache : QueryCache HashSpec) :
    Pr[fun result : Option Signature × QueryCache HashSpec =>
      (SigningCacheEntry.mk request result.1 initialCache result.2).EncodingInputPrehit
        secretKey |
      (simulateQ xmssRomImpl
        (Concrete.sign publicKey secretKey request.epoch request.message)).run
          initialCache] ≤
      QueryCache.enncard initialCache *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  simpa [SigningCacheEntry.EncodingInputPrehit] using
    Concrete.sign_encodingInput_initialCache_hit_le publicKey secretKey
      request.epoch request.message initialCache

theorem signingCacheEntry_preexistingEncodingCollision_probability_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (initialCache : QueryCache HashSpec)
    (hfinite : initialCache.toSet.Finite) :
    Pr[fun result : Option Signature × QueryCache HashSpec =>
      (SigningCacheEntry.mk request result.1 initialCache result.2).PreexistingEncodingCollision
        secretKey |
      (simulateQ xmssRomImpl
        (Concrete.sign publicKey secretKey request.epoch request.message)).run
          initialCache] ≤
      QueryCache.enncard initialCache *
          ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ +
        ((cachedEncodingEntries initialCache secretKey.parameter request.epoch).card : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  simpa [SigningCacheEntry.PreexistingEncodingCollision] using
    Concrete.sign_preexistingEncoding_collision_le publicKey secretKey
      request.epoch request.message initialCache hfinite

theorem signingCacheEntry_freshSigningEncodingCollision_probability_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (initialCache : QueryCache HashSpec)
    (hfinite : initialCache.toSet.Finite) :
    Pr[fun result : Option Signature × QueryCache HashSpec =>
      (SigningCacheEntry.mk request result.1 initialCache result.2)
        |>.FreshSigningEncodingCollision secretKey |
      (simulateQ xmssRomImpl
        (Concrete.sign publicKey secretKey request.epoch request.message)).run
          initialCache] ≤
      ((cachedEncodingEntries initialCache secretKey.parameter request.epoch).card :
        ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  simpa [SigningCacheEntry.FreshSigningEncodingCollision] using
    Concrete.sign_freshEncoding_collision_le publicKey secretKey request.epoch
      request.message initialCache hfinite

set_option linter.constructorNameAsVariable false in
theorem Concrete.sign_success_encodingInput_cached
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (initialCache finalCache : QueryCache HashSpec)
    (signature : Signature)
    (hmem : (some signature, finalCache) ∈ support
      ((simulateQ xmssRomImpl
        (Concrete.sign publicKey secretKey request.epoch request.message)).run
          initialCache)) :
    ∃ output, finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter request.epoch
        (request.message, signature.randomness)) = some output := by
  rw [Concrete.sign_eq, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨randomness, randomnessCache⟩, _hrandomness, hattempt⟩ := hmem
  have hroute :
      simulateQ xmssRomImpl
          (liftM (Concrete.signAttempt secretKey request.epoch request.message randomness :
            OracleComp HashSpec (Option Signature))) =
        simulateQ randomOracle
          (Concrete.signAttempt secretKey request.epoch request.message randomness :
            OracleComp HashSpec (Option Signature)) := by
    change simulateQ (unifFwdImpl HashSpec + randomOracle)
        (liftM (Concrete.signAttempt secretKey request.epoch request.message randomness :
          OracleComp HashSpec (Option Signature))) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.signAttempt secretKey request.epoch request.message randomness :
        OracleComp HashSpec (Option Signature))
  rw [hroute] at hattempt
  have hrandomness := Concrete.signAttempt_support_randomness secretKey request.epoch
    request.message randomness randomnessCache finalCache signature hattempt
  unfold Concrete.signAttempt at hattempt
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hattempt
  obtain ⟨⟨digest, digestCache⟩, hdigest, hrest⟩ := hattempt
  obtain ⟨output, hcached, _hdigest⟩ :=
    Concrete.CacheReplay.tweakableHash_query_cached secretKey.parameter
      (.encoding request.epoch)
      (Concrete.encodingPayload request.message randomness)
      randomnessCache digestCache digest hdigest
  have hcacheLe : digestCache ≤ finalCache :=
    Concrete.CacheReplay.randomOracle_cache_le
      (match TargetSum.decodeDigest digest with
        | none => pure none
        | some encoding => some <$>
          Concrete.signWithEncoding secretKey request.epoch randomness encoding)
      digestCache (some signature, finalCache) hrest
  refine ⟨output, ?_⟩
  rw [hrandomness]
  exact hcacheLe hcached

set_option linter.constructorNameAsVariable false in
theorem Concrete.sign_success_preserves_other_encodingInput
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (initialCache finalCache : QueryCache HashSpec)
    (signature : Signature)
    (hmem : (some signature, finalCache) ∈ support
      ((simulateQ xmssRomImpl
        (Concrete.sign publicKey secretKey request.epoch request.message)).run
          initialCache))
    (targetEpoch : Epoch) (targetInput : Message × Randomness)
    (hne : Concrete.CacheView.encodingInput secretKey.parameter request.epoch
        (request.message, signature.randomness) ≠
      Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none) :
    finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none := by
  rw [Concrete.sign_run_eq, mem_support_bind_iff] at hmem
  obtain ⟨randomness, _hrandomness, hattempt⟩ := hmem
  have hrandomness := Concrete.signAttempt_support_randomness secretKey request.epoch
    request.message randomness initialCache finalCache signature hattempt
  have hne' : Concrete.CacheView.encodingInput secretKey.parameter request.epoch
        (request.message, randomness) ≠
      Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput := by
    simpa [hrandomness] using hne
  exact Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.signAttempt secretKey request.epoch request.message randomness :
      OracleComp HashSpec (Option Signature))
    (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput)
    initialCache finalCache (some signature)
    (Concrete.signAttempt_queryBound_zero_at_other_encodingInput secretKey
      request.epoch targetEpoch request.message randomness targetInput hne')
    hnone hattempt

set_option linter.constructorNameAsVariable false in
theorem Concrete.sign_preserves_other_epoch_encodingInput
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (initialCache finalCache : QueryCache HashSpec)
    (result : Option Signature)
    (hmem : (result, finalCache) ∈ support
      ((simulateQ xmssRomImpl
        (Concrete.sign publicKey secretKey request.epoch request.message)).run
          initialCache))
    (targetEpoch : Epoch) (targetInput : Message × Randomness)
    (hne : request.epoch ≠ targetEpoch)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none) :
    finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none := by
  rw [Concrete.sign_run_eq, mem_support_bind_iff] at hmem
  obtain ⟨randomness, _hrandomness, hattempt⟩ := hmem
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.signAttempt secretKey request.epoch request.message randomness :
      OracleComp HashSpec (Option Signature))
    (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput)
    initialCache finalCache result
  · apply Concrete.signAttempt_queryBound_zero_at_other_encodingInput
    intro hinput
    exact hne (Concrete.CacheView.epoch_eq_of_encodingInput_eq secretKey.parameter hinput)
  · exact hnone
  · exact hattempt

/-- Across a valid signing trace, the same-epoch cache targets visible before each signature are disjointly charged to the final cache. -/
theorem signingCacheTrace_cachedEncodingEntries_sum_le
    (trace : SigningCacheTrace) (parameter : PublicParameter)
    (finalCache : QueryCache HashSpec)
    (hvalid : SigningTranscript.Valid trace.toSigningLog)
    (hle : ∀ entry ∈ trace, entry.initialCache ≤ finalCache)
    (hfinite : finalCache.toSet.Finite) :
    (((trace.map fun entry =>
        (cachedEncodingEntries entry.initialCache parameter
          entry.request.epoch).card).sum : Nat) : ℝ≥0∞) ≤
      QueryCache.enncard finalCache := by
  classical
  let epochs := trace.map fun entry => entry.request.epoch
  have hepochs : epochs.Nodup := by
    unfold SigningTranscript.Valid at hvalid
    simpa [epochs, SigningCacheTrace.toSigningLog, List.map_map,
      Function.comp_def] using hvalid
  have hpointwise :
      (trace.map fun entry =>
        (cachedEncodingEntries entry.initialCache parameter
          entry.request.epoch).card).sum ≤
      (trace.map fun entry =>
        (cachedEncodingEntries finalCache parameter
          entry.request.epoch).card).sum := by
    apply List.sum_le_sum
    intro entry hentry
    exact cachedEncodingEntries_card_mono entry.initialCache finalCache parameter
      entry.request.epoch (hle entry hentry) hfinite
  have htoFinset := List.sum_toFinset
    (fun epoch => (cachedEncodingEntries finalCache parameter epoch).card)
    hepochs
  calc
    (((trace.map fun entry =>
        (cachedEncodingEntries entry.initialCache parameter
          entry.request.epoch).card).sum : Nat) : ℝ≥0∞) ≤
        (((trace.map fun entry =>
          (cachedEncodingEntries finalCache parameter
            entry.request.epoch).card).sum : Nat) : ℝ≥0∞) := by
      exact_mod_cast hpointwise
    _ = (((∑ epoch ∈ epochs.toFinset,
        (cachedEncodingEntries finalCache parameter epoch).card : Nat)) : ℝ≥0∞) := by
      congr 1
      simpa [epochs, List.map_map, Function.comp_def] using htoFinset.symm
    _ ≤ QueryCache.enncard finalCache :=
      sum_cachedEncodingEntries_card_le_enncard finalCache parameter epochs.toFinset

noncomputable def SigningCacheEntry.preexistingEncodingRisk
    (parameter : PublicParameter) (entry : SigningCacheEntry) : ℝ≥0∞ :=
  QueryCache.enncard entry.initialCache *
      ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ +
    ((cachedEncodingEntries entry.initialCache parameter entry.request.epoch).card : ℝ≥0∞) *
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹

noncomputable def SigningCacheTrace.preexistingEncodingRisk
    (parameter : PublicParameter) (trace : SigningCacheTrace) : ℝ≥0∞ :=
  (trace.map fun entry => entry.preexistingEncodingRisk parameter).sum

noncomputable def SigningCacheTrace.encodingInputPrehitRisk
    (trace : SigningCacheTrace) : ℝ≥0∞ :=
  (trace.map fun entry => QueryCache.enncard entry.initialCache *
    ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹).sum

noncomputable def SigningCacheTrace.freshSigningEncodingCollisionRisk
    (parameter : PublicParameter) (trace : SigningCacheTrace) : ℝ≥0∞ :=
  (trace.map fun entry =>
    ((cachedEncodingEntries entry.initialCache parameter
      entry.request.epoch).card : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹).sum

/-- The 192-bit signing-randomness pre-hit charge across a valid trace is below one 128-bit term. -/
theorem SigningCacheTrace.encodingInputPrehitRisk_le
    (trace : SigningCacheTrace) (finalCache : QueryCache HashSpec) (q : Nat)
    (hvalid : SigningTranscript.Valid trace.toSigningLog)
    (hcaches : trace.CachesLe finalCache)
    (hcard : QueryCache.enncard finalCache ≤ (q : ℝ≥0∞)) :
    trace.encodingInputPrehitRisk ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  have hlength : trace.length ≤ lifetime := by
    unfold SigningTranscript.Valid at hvalid
    simpa [SigningCacheTrace.toSigningLog, List.map_map,
      Function.comp_def] using List.Nodup.length_le_card hvalid
  calc
    trace.encodingInputPrehitRisk ≤
        (trace.map fun _entry => (q : ℝ≥0∞) *
          ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹).sum := by
      unfold SigningCacheTrace.encodingInputPrehitRisk
      apply List.sum_le_sum
      intro entry hentry
      gcongr
      exact (QueryCache.enncard_mono (hcaches entry hentry).1).trans hcard
    _ = (trace.length : ℝ≥0∞) *
        ((q : ℝ≥0∞) * ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) := by
      simp
    _ ≤ (lifetime : ℝ≥0∞) *
        ((q : ℝ≥0∞) * ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) := by
      gcongr
    _ = (lifetime : ℝ≥0∞) *
        ((q : ℝ≥0∞) / ((2 ^ randomnessBits : Nat) : ℝ≥0∞)) := by
      rw [div_eq_mul_inv]
    _ ≤ (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
      lifetime_mul_randomness_loss_le_digest_loss q

/-- Same-epoch digest targets charged at fresh signing calls are disjoint across a valid trace, so their total risk is one 128-bit term. -/
theorem SigningCacheTrace.freshSigningEncodingCollisionRisk_le
    (trace : SigningCacheTrace) (parameter : PublicParameter)
    (finalCache : QueryCache HashSpec) (q : Nat)
    (hvalid : SigningTranscript.Valid trace.toSigningLog)
    (hcaches : trace.CachesLe finalCache)
    (hfinite : finalCache.toSet.Finite)
    (hcard : QueryCache.enncard finalCache ≤ (q : ℝ≥0∞)) :
    trace.freshSigningEncodingCollisionRisk parameter ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  have hrewrite : trace.freshSigningEncodingCollisionRisk parameter =
      (((trace.map fun entry =>
        (cachedEncodingEntries entry.initialCache parameter
          entry.request.epoch).card).sum : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
    unfold SigningCacheTrace.freshSigningEncodingCollisionRisk
    clear hvalid hcaches hfinite hcard q
    induction trace with
    | nil => simp
    | cons entry tail ih =>
        simp only [List.map_cons, List.sum_cons, Nat.cast_add]
        rw [ih, add_mul]
  rw [hrewrite, div_eq_mul_inv]
  exact mul_le_mul'
    ((signingCacheTrace_cachedEncodingEntries_sum_le trace parameter finalCache
      hvalid (fun entry hentry => (hcaches entry hentry).1) hfinite).trans hcard)
    le_rfl

/-- Summing the local pre-signing collision charges over a valid trace costs at most two elementary 128-bit terms. -/
theorem SigningCacheTrace.preexistingEncodingRisk_le
    (trace : SigningCacheTrace) (parameter : PublicParameter)
    (finalCache : QueryCache HashSpec) (q : Nat)
    (hvalid : SigningTranscript.Valid trace.toSigningLog)
    (hcaches : trace.CachesLe finalCache)
    (hfinite : finalCache.toSet.Finite)
    (hcard : QueryCache.enncard finalCache ≤ (q : ℝ≥0∞)) :
    trace.preexistingEncodingRisk parameter ≤
      2 * ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
  let randomnessLoss : ℝ≥0∞ := ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹
  let digestLoss : ℝ≥0∞ := ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
  have hlength : trace.length ≤ lifetime := by
    unfold SigningTranscript.Valid at hvalid
    simpa [SigningCacheTrace.toSigningLog, List.map_map, Function.comp_def] using
      List.Nodup.length_le_card hvalid
  have hsplit : trace.preexistingEncodingRisk parameter =
      (trace.map fun entry =>
        QueryCache.enncard entry.initialCache * randomnessLoss).sum +
      (trace.map fun entry =>
        ((cachedEncodingEntries entry.initialCache parameter
          entry.request.epoch).card : ℝ≥0∞) * digestLoss).sum := by
    unfold SigningCacheTrace.preexistingEncodingRisk
      SigningCacheEntry.preexistingEncodingRisk randomnessLoss digestLoss
    clear hlength hvalid hcaches hfinite hcard q
    induction trace with
    | nil => simp
    | cons entry tail ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        ac_rfl
  have hrandomness :
      (trace.map fun entry =>
        QueryCache.enncard entry.initialCache * randomnessLoss).sum ≤
      (lifetime : ℝ≥0∞) *
        ((q : ℝ≥0∞) / ((2 ^ randomnessBits : Nat) : ℝ≥0∞)) := by
    calc
      (trace.map fun entry =>
          QueryCache.enncard entry.initialCache * randomnessLoss).sum ≤
          (trace.map fun _entry => (q : ℝ≥0∞) * randomnessLoss).sum := by
        apply List.sum_le_sum
        intro entry hentry
        gcongr
        exact (QueryCache.enncard_mono (hcaches entry hentry).1).trans hcard
      _ = (trace.length : ℝ≥0∞) * ((q : ℝ≥0∞) * randomnessLoss) := by
        simp
      _ ≤ (lifetime : ℝ≥0∞) * ((q : ℝ≥0∞) * randomnessLoss) := by
        gcongr
      _ = (lifetime : ℝ≥0∞) *
          ((q : ℝ≥0∞) / ((2 ^ randomnessBits : Nat) : ℝ≥0∞)) := by
        rw [div_eq_mul_inv]
  have hencodingRewrite :
      (trace.map fun entry =>
        ((cachedEncodingEntries entry.initialCache parameter
          entry.request.epoch).card : ℝ≥0∞) * digestLoss).sum =
      (((trace.map fun entry =>
        (cachedEncodingEntries entry.initialCache parameter
          entry.request.epoch).card).sum : Nat) : ℝ≥0∞) * digestLoss := by
    clear hrandomness hsplit hlength hvalid hcaches hfinite hcard q randomnessLoss
    induction trace with
    | nil => simp
    | cons entry tail ih =>
        simp only [List.map_cons, List.sum_cons, Nat.cast_add]
        rw [ih, add_mul]
  have hencoding :
      (trace.map fun entry =>
        ((cachedEncodingEntries entry.initialCache parameter
          entry.request.epoch).card : ℝ≥0∞) * digestLoss).sum ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
    rw [hencodingRewrite, div_eq_mul_inv]
    exact mul_le_mul'
      ((signingCacheTrace_cachedEncodingEntries_sum_le trace parameter finalCache
        hvalid (fun entry hentry => (hcaches entry hentry).1) hfinite).trans hcard)
      le_rfl
  rw [hsplit, two_mul]
  exact add_le_add
    (hrandomness.trans (lifetime_mul_randomness_loss_le_digest_loss q))
    hencoding

noncomputable def unloggedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) ProbComp) := by
  classical
  intro input
  cases input with
  | inl worldInput =>
      exact xmssRomImpl worldInput
  | inr request =>
      exact simulateQ xmssRomImpl
        (Concrete.singleAttemptScheme.sign publicKey secretKey request.epoch request.message)

theorem unloggedMappedAdversaryImpl_apply_inl
    (publicKey : PublicKey) (secretKey : SecretKey)
    (worldInput : OracleWorld.Domain) :
    unloggedMappedAdversaryImpl publicKey secretKey (.inl worldInput) =
      xmssRomImpl worldInput := by
  rfl

theorem unloggedMappedAdversaryImpl_apply_inr
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) :
    unloggedMappedAdversaryImpl publicKey secretKey (.inr request) =
      (simulateQ xmssRomImpl
        (Concrete.singleAttemptScheme.sign publicKey secretKey request.epoch request.message) :
          StateT (QueryCache HashSpec) ProbComp (Option Signature)) := by
  rfl

def signingLogFragment
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) : QueryLog SigningSpec :=
  match input with
  | .inl _ => []
  | .inr request => [⟨request, output⟩]

@[simp]
theorem signingLogFragment_inl
    (input : OracleWorld.Domain) (output : OracleWorld.Range input) :
    signingLogFragment (.inl input) output = [] := rfl

@[simp]
theorem signingLogFragment_inr
    (request : SignRequest) (output : Option Signature) :
    signingLogFragment (.inr request) output = [⟨request, output⟩] := rfl

noncomputable def selectivelyLoggedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (StateT (QueryCache HashSpec) ProbComp)) :=
  QueryImpl.withTraceAppend (unloggedMappedAdversaryImpl publicKey secretKey)
    signingLogFragment

theorem selectivelyLoggedMappedAdversaryImpl_apply_inr
    (publicKey : PublicKey) (secretKey : SecretKey) (request : SignRequest) :
    selectivelyLoggedMappedAdversaryImpl publicKey secretKey (.inr request) =
      QueryImpl.withLogging
        (fun request => simulateQ xmssRomImpl
          (Concrete.singleAttemptScheme.sign publicKey secretKey request.epoch request.message))
        request := by
  rfl

theorem mappedAdversaryImpl_apply_inr
    (publicKey : PublicKey) (secretKey : SecretKey) (request : SignRequest) :
    mappedAdversaryImpl publicKey secretKey (.inr request) =
      QueryImpl.withLogging
        (fun request => simulateQ xmssRomImpl
          (Concrete.singleAttemptScheme.sign publicKey secretKey request.epoch request.message))
        request := by
  change WriterT.mk (simulateQ xmssRomImpl
      ((QueryImpl.withLogging (spec := SigningSpec)
        (fun request => Concrete.singleAttemptScheme.sign publicKey secretKey
          request.epoch request.message) request).run)) =
    QueryImpl.withLogging (spec := SigningSpec)
      (fun request => simulateQ xmssRomImpl
        (Concrete.singleAttemptScheme.sign publicKey secretKey request.epoch request.message))
      request
  apply WriterT.ext
  rw [WriterT.run_mk, QueryImpl.run_withLogging_apply,
    QueryImpl.run_withLogging_apply, simulateQ_bind]
  simp

theorem selectivelyLoggedMappedAdversaryImpl_eq_mappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    selectivelyLoggedMappedAdversaryImpl publicKey secretKey =
      mappedAdversaryImpl publicKey secretKey := by
  funext input
  cases input with
  | inl worldInput =>
      change (do
          let output ← liftM (xmssRomImpl worldInput)
          tell ([] : QueryLog SigningSpec)
          pure output) =
        WriterT.mk ((fun output => (output, ([] : QueryLog SigningSpec))) <$>
          xmssRomImpl worldInput)
      apply WriterT.ext
      simp
  | inr request =>
      rw [selectivelyLoggedMappedAdversaryImpl_apply_inr,
        mappedAdversaryImpl_apply_inr]

def signingCacheTraceUpdate
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec)
    (trace : SigningCacheTrace) : SigningCacheTrace :=
  match input with
  | .inl _ => trace
  | .inr request =>
      trace ++ [SigningCacheEntry.mk request output initialCache finalCache]

def signingLogUpdate
    (input : (OracleWorld + SigningSpec).Domain)
    (_initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (_finalCache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) : QueryLog SigningSpec :=
  log ++ signingLogFragment input output

theorem signingCacheTraceUpdate_toSigningLog
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (trace : SigningCacheTrace) :
    (signingCacheTraceUpdate input initialCache output finalCache trace).toSigningLog =
      signingLogUpdate input initialCache output finalCache trace.toSigningLog := by
  cases input <;> simp [signingCacheTraceUpdate, signingLogUpdate,
    signingLogFragment, SigningCacheTrace.toSigningLog]

theorem SigningCacheTrace.CachesLe.mono
    {trace : SigningCacheTrace} {initialCache finalCache : QueryCache HashSpec}
    (htrace : trace.CachesLe initialCache) (hle : initialCache ≤ finalCache) :
    trace.CachesLe finalCache := by
  intro entry hentry
  exact ⟨(htrace entry hentry).1.trans hle, (htrace entry hentry).2.trans hle⟩

theorem signingCacheTraceUpdate_cachesLe
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (trace : SigningCacheTrace)
    (htrace : trace.CachesLe initialCache) (hle : initialCache ≤ finalCache) :
    (signingCacheTraceUpdate input initialCache output finalCache trace).CachesLe
      finalCache := by
  cases input with
  | inl worldInput =>
      exact htrace.mono hle
  | inr request =>
      intro entry hentry
      rw [signingCacheTraceUpdate, List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · exact (htrace entry hentry).imp (fun h => h.trans hle) (fun h => h.trans hle)
      · simp only [List.mem_singleton] at hentry
        subst entry
        exact ⟨hle, le_rfl⟩

theorem signingCacheTraceUpdate_chronological
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (trace : SigningCacheTrace)
    (hchronological : trace.Chronological)
    (hcaches : trace.CachesLe initialCache) :
    (signingCacheTraceUpdate input initialCache output finalCache trace).Chronological := by
  cases input with
  | inl worldInput =>
      exact hchronological
  | inr request =>
      rw [SigningCacheTrace.Chronological, signingCacheTraceUpdate,
        List.pairwise_append]
      refine ⟨hchronological, by simp, ?_⟩
      intro earlier hearlier later hlater
      simp only [List.mem_singleton] at hlater
      subst later
      exact (hcaches earlier hearlier).2

noncomputable def cacheTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec × SigningCacheTrace) ProbComp) :=
  QueryImpl.extendState (unloggedMappedAdversaryImpl publicKey secretKey)
    signingCacheTraceUpdate

noncomputable def logTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec × QueryLog SigningSpec) ProbComp) :=
  QueryImpl.extendState (unloggedMappedAdversaryImpl publicKey secretKey)
    signingLogUpdate

theorem unloggedMappedAdversaryImpl_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (result : (OracleWorld + SigningSpec).Range input × QueryCache HashSpec)
    (hmem : result ∈ support
      ((unloggedMappedAdversaryImpl publicKey secretKey input).run initialCache)) :
    initialCache ≤ result.2 := by
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          have hrun :
              (unifFwdImpl HashSpec uniformInput).run initialCache =
                (fun sample => (sample, initialCache)) <$>
                  (liftM (unifSpec.query uniformInput) : ProbComp _) := by
            simpa [simulateQ_query] using
              (unifFwdImpl.simulateQ_run
                (hashSpec := HashSpec)
                (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache)
          change result ∈ support
            ((unifFwdImpl HashSpec uniformInput).run initialCache) at hmem
          rw [hrun, support_map] at hmem
          obtain ⟨sample, _hsample, heq⟩ := hmem
          exact le_of_eq (congrArg Prod.snd heq)
      | inr hashInput =>
          change result ∈ support
            ((randomOracle (spec := HashSpec) hashInput).run initialCache) at hmem
          exact QueryImpl.withCaching_cache_le uniformSampleImpl hashInput initialCache
            result hmem
  | inr request =>
      exact xmssRom_cache_le
        (Concrete.sign publicKey secretKey request.epoch request.message)
        initialCache result hmem

theorem cacheTracedMappedAdversaryImpl_query_cachesLe
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.CachesLe initialCache)
    (hmem : result ∈ support
      ((cacheTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialTrace))) :
    result.2.2.CachesLe result.2.1 := by
  rw [cacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact signingCacheTraceUpdate_cachesLe input initialCache output finalCache
    initialTrace htrace
    (unloggedMappedAdversaryImpl_cache_le publicKey secretKey input initialCache
      (output, finalCache) hbase)

theorem cacheTracedMappedAdversaryImpl_query_cacheOrder
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (hchronological : initialTrace.Chronological)
    (hcaches : initialTrace.CachesLe initialCache)
    (hmem : result ∈ support
      ((cacheTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialTrace))) :
    result.2.2.Chronological ∧ result.2.2.CachesLe result.2.1 := by
  rw [cacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  have hle := unloggedMappedAdversaryImpl_cache_le publicKey secretKey input
    initialCache (output, finalCache) hbase
  exact ⟨signingCacheTraceUpdate_chronological input initialCache output finalCache
      initialTrace hchronological hcaches,
    signingCacheTraceUpdate_cachesLe input initialCache output finalCache initialTrace
      hcaches hle⟩

theorem cacheTracedMappedAdversaryImpl_query_successfulEncodingsCached
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.SuccessfulEncodingsCached secretKey)
    (hmem : result ∈ support
      ((cacheTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialTrace))) :
    result.2.2.SuccessfulEncodingsCached secretKey := by
  rw [cacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  cases input with
  | inl worldInput =>
      simpa [signingCacheTraceUpdate] using htrace
  | inr request =>
      intro entry hentry
      rw [signingCacheTraceUpdate, List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · exact htrace entry hentry
      · simp only [List.mem_singleton] at hentry
        subst entry
        intro signature hsignature
        change output = some signature at hsignature
        subst output
        exact Concrete.sign_success_encodingInput_cached publicKey secretKey request
          initialCache finalCache signature hbase

theorem cacheTracedMappedAdversaryImpl_query_preservesOtherEncodingInputs
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.PreservesOtherEncodingInputs secretKey)
    (hmem : result ∈ support
      ((cacheTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialTrace))) :
    result.2.2.PreservesOtherEncodingInputs secretKey := by
  rw [cacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  cases input with
  | inl worldInput =>
      simpa [signingCacheTraceUpdate] using htrace
  | inr request =>
      intro entry hentry
      rw [signingCacheTraceUpdate, List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · exact htrace entry hentry
      · simp only [List.mem_singleton] at hentry
        subst entry
        intro signature hsignature targetEpoch targetInput hne hnone
        change output = some signature at hsignature
        subst output
        exact Concrete.sign_success_preserves_other_encodingInput publicKey secretKey
          request initialCache finalCache signature hbase targetEpoch targetInput hne hnone

theorem cacheTracedMappedAdversaryImpl_cachesLe
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.CachesLe initialCache)
    (hmem : result ∈ support
      ((simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.CachesLe result.2.1 := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialTrace result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      exact htrace
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hmem
      have hquery' : (output, middleState) ∈ support
          ((cacheTracedMappedAdversaryImpl publicKey secretKey input).run
            (initialCache, initialTrace)) := by
        simpa [simulateQ_query] using hquery
      exact ih output middleState.1 middleState.2 result
        (cacheTracedMappedAdversaryImpl_query_cachesLe publicKey secretKey input
          initialCache initialTrace (output, middleState) htrace hquery')
        hrest

theorem cacheTracedMappedAdversaryImpl_cacheOrder
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (hchronological : initialTrace.Chronological)
    (hcaches : initialTrace.CachesLe initialCache)
    (hmem : result ∈ support
      ((simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.Chronological ∧ result.2.2.CachesLe result.2.1 := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialTrace result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      exact ⟨hchronological, hcaches⟩
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hmem
      have hquery' : (output, middleState) ∈ support
          ((cacheTracedMappedAdversaryImpl publicKey secretKey input).run
            (initialCache, initialTrace)) := by
        simpa [simulateQ_query] using hquery
      obtain ⟨hmiddleChronological, hmiddleCaches⟩ :=
        cacheTracedMappedAdversaryImpl_query_cacheOrder publicKey secretKey input
          initialCache initialTrace (output, middleState) hchronological hcaches hquery'
      exact ih output middleState.1 middleState.2 result hmiddleChronological
        hmiddleCaches hrest

theorem cacheTracedMappedAdversaryImpl_successfulEncodingsCached
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.SuccessfulEncodingsCached secretKey)
    (hmem : result ∈ support
      ((simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.SuccessfulEncodingsCached secretKey := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialTrace result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      exact htrace
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hmem
      have hquery' : (output, middleState) ∈ support
          ((cacheTracedMappedAdversaryImpl publicKey secretKey input).run
            (initialCache, initialTrace)) := by
        simpa [simulateQ_query] using hquery
      exact ih output middleState.1 middleState.2 result
        (cacheTracedMappedAdversaryImpl_query_successfulEncodingsCached
          publicKey secretKey input initialCache initialTrace (output, middleState)
          htrace hquery') hrest

theorem cacheTracedMappedAdversaryImpl_preservesOtherEncodingInputs
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.PreservesOtherEncodingInputs secretKey)
    (hmem : result ∈ support
      ((simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.PreservesOtherEncodingInputs secretKey := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialTrace result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      exact htrace
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleState⟩, hquery, hrest⟩ := hmem
      have hquery' : (output, middleState) ∈ support
          ((cacheTracedMappedAdversaryImpl publicKey secretKey input).run
            (initialCache, initialTrace)) := by
        simpa [simulateQ_query] using hquery
      exact ih output middleState.1 middleState.2 result
        (cacheTracedMappedAdversaryImpl_query_preservesOtherEncodingInputs
          publicKey secretKey input initialCache initialTrace (output, middleState)
          htrace hquery') hrest

theorem cacheTracedMappedAdversaryImpl_cachedEncodingEntries_sum_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support
      ((simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, [])))
    (hvalid : SigningTranscript.Valid result.2.2.toSigningLog)
    (hfinite : result.2.1.toSet.Finite) :
    (((result.2.2.map fun entry =>
        (cachedEncodingEntries entry.initialCache secretKey.parameter
          entry.request.epoch).card).sum : Nat) : ℝ≥0∞) ≤
      QueryCache.enncard result.2.1 := by
  apply signingCacheTrace_cachedEncodingEntries_sum_le result.2.2
    secretKey.parameter result.2.1 hvalid
  · intro entry hentry
    exact (cacheTracedMappedAdversaryImpl_cachesLe publicKey secretKey computation
      initialCache [] result (by simp [SigningCacheTrace.CachesLe]) hmem
      entry hentry).1
  · exact hfinite

theorem cacheTracedMappedAdversaryImpl_cache_projection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace) :
    Prod.map id Prod.fst <$>
        (simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialCache, initialTrace) =
      (simulateQ (unloggedMappedAdversaryImpl publicKey secretKey)
        computation).run initialCache := by
  exact OracleComp.extendState_run_proj_eq
    (unloggedMappedAdversaryImpl publicKey secretKey) signingCacheTraceUpdate
    computation initialCache initialTrace

theorem cacheTracedMappedAdversaryImpl_log_projection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace) :
    Prod.map id (fun state => (state.1, state.2.toSigningLog)) <$>
        (simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialCache, initialTrace) =
      (simulateQ (logTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace.toSigningLog) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (cacheTracedMappedAdversaryImpl publicKey secretKey)
    (logTracedMappedAdversaryImpl publicKey secretKey)
    (fun state => (state.1, state.2.toSigningLog))
  intro input state
  rw [cacheTracedMappedAdversaryImpl, logTracedMappedAdversaryImpl,
    QueryImpl.extendState_apply, QueryImpl.extendState_apply, map_bind]
  apply bind_congr
  intro result
  simp only [map_pure]
  simpa [Prod.map] using congrArg (fun log => (result.1, (result.2, log)))
    (signingCacheTraceUpdate_toSigningLog input state.1 result.1 result.2 state.2)

theorem selectivelyLoggedMappedAdversaryImpl_query_run_eq_logTraced
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialLog : QueryLog SigningSpec) :
    (fun result =>
      (result.1.1, (result.2, initialLog ++ result.1.2))) <$>
        (((selectivelyLoggedMappedAdversaryImpl publicKey secretKey input).run).run
          initialCache) =
      (logTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialLog) := by
  rw [selectivelyLoggedMappedAdversaryImpl, QueryImpl.withTraceAppend_apply,
    logTracedMappedAdversaryImpl, QueryImpl.extendState_apply]
  simp only [WriterT.run_bind', WriterT.run_monadLift',
    WriterT.run_tell, WriterT.run_pure', StateT.run_bind, StateT.run_pure,
    map_bind, bind_map_left, pure_bind, map_pure, Prod.map, id_eq]
  apply bind_congr
  intro result
  simp [signingLogUpdate]

theorem selectivelyLoggedMappedAdversaryImpl_run_eq_logTraced
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialLog : QueryLog SigningSpec) :
    (fun result =>
      (result.1.1, (result.2, initialLog ++ result.1.2))) <$>
        (((simulateQ (selectivelyLoggedMappedAdversaryImpl publicKey secretKey)
          computation).run).run initialCache) =
      (simulateQ (logTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialLog) := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialLog with
  | pure value =>
      simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, WriterT.run_bind', StateT.run_bind, map_bind]
      simp only [id_map]
      rw [← selectivelyLoggedMappedAdversaryImpl_query_run_eq_logTraced
        publicKey secretKey input initialCache initialLog]
      simp only [bind_map_left]
      apply bind_congr
      intro prefixResult
      simpa [List.append_assoc] using
        ih prefixResult.1.1 prefixResult.2 (initialLog ++ prefixResult.1.2)

theorem cacheTracedMappedAdversaryImpl_log_projection_eq_mapped
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) :
    Prod.map id (fun state => (state.1, state.2.toSigningLog)) <$>
        (simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialCache, []) =
      (fun result => (result.1.1, (result.2, result.1.2))) <$>
        (((simulateQ (mappedAdversaryImpl publicKey secretKey)
          computation).run).run initialCache) := by
  rw [cacheTracedMappedAdversaryImpl_log_projection]
  simp only [SigningCacheTrace.toSigningLog, List.map_nil]
  rw [← selectivelyLoggedMappedAdversaryImpl_run_eq_logTraced
    publicKey secretKey computation initialCache []]
  rw [selectivelyLoggedMappedAdversaryImpl_eq_mappedAdversaryImpl]
  rfl

noncomputable def detailedGameAfterKeygenWithSigningTrace
    (adversary : Adversary Concrete.singleAttemptScheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    ProbComp (GameOutcome × (QueryCache HashSpec × SigningCacheTrace)) := do
  let (forgery, adversaryCache, trace) ←
    (simulateQ (cacheTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run (initialCache, [])
  let (verified, finalCache) ←
    (simulateQ xmssRomImpl
      (Concrete.singleAttemptScheme.verify publicKey forgery.epoch forgery.message
        forgery.signature)).run adversaryCache
  pure (⟨publicKey, secretKey, forgery, trace.toSigningLog, verified⟩,
    (finalCache, trace))

noncomputable def mappedDetailedGameAfterKeygenWithCache
    (adversary : Adversary Concrete.singleAttemptScheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    ProbComp (GameOutcome × QueryCache HashSpec) := do
  let (forgery, adversaryCache, signingLog) ←
    (fun result => (result.1.1, (result.2, result.1.2))) <$>
      (((simulateQ (mappedAdversaryImpl publicKey secretKey)
        (adversary.main publicKey)).run).run initialCache)
  let (verified, finalCache) ←
    (simulateQ xmssRomImpl
      (Concrete.singleAttemptScheme.verify publicKey forgery.epoch forgery.message
        forgery.signature)).run adversaryCache
  pure (⟨publicKey, secretKey, forgery, signingLog, verified⟩, finalCache)

theorem detailedGameAfterKeygenWithSigningTrace_cache_projection
    (adversary : Adversary Concrete.singleAttemptScheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    Prod.map id Prod.fst <$>
        detailedGameAfterKeygenWithSigningTrace adversary publicKey secretKey initialCache =
      mappedDetailedGameAfterKeygenWithCache adversary publicKey secretKey initialCache := by
  let finish : Forgery × (QueryCache HashSpec × QueryLog SigningSpec) →
      ProbComp (GameOutcome × QueryCache HashSpec) := fun result => do
    let (verified, finalCache) ←
      (simulateQ xmssRomImpl
        (Concrete.singleAttemptScheme.verify publicKey result.1.epoch result.1.message
          result.1.signature)).run result.2.1
    pure (⟨publicKey, secretKey, result.1, result.2.2, verified⟩, finalCache)
  have hbridge := congrArg (fun computation => computation >>= finish)
    (cacheTracedMappedAdversaryImpl_log_projection_eq_mapped publicKey secretKey
      (adversary.main publicKey) initialCache)
  simpa [detailedGameAfterKeygenWithSigningTrace,
    mappedDetailedGameAfterKeygenWithCache, finish, bind_map_left,
    map_bind, bind_assoc, Prod.map] using hbridge

theorem mappedDetailedGameAfterKeygenWithCache_eq_detailed
    (adversary : Adversary Concrete.singleAttemptScheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    mappedDetailedGameAfterKeygenWithCache adversary publicKey secretKey initialCache =
      (simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary publicKey secretKey)).run
          initialCache := by
  unfold mappedDetailedGameAfterKeygenWithCache detailedGameAfterKeygen
  rw [mappedAdversaryImpl]
  rw [← QueryImpl.simulateQ_writerTMapBase_run]
  simp [simulateQ_bind, StateT.run_bind, bind_map_left]

noncomputable def detailedGameWithSigningTrace
    (adversary : Adversary Concrete.singleAttemptScheme) :
    ProbComp (GameOutcome × (QueryCache HashSpec × SigningCacheTrace)) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅
  detailedGameAfterKeygenWithSigningTrace adversary keyResult.1.1 keyResult.1.2
    keyResult.2

theorem detailedGameWithSigningTrace_cache_projection
    (adversary : Adversary Concrete.singleAttemptScheme) :
    Prod.map id Prod.fst <$> detailedGameWithSigningTrace adversary =
      detailedGameWithCache Concrete.singleAttemptScheme adversary := by
  unfold detailedGameWithSigningTrace detailedGameWithCache detailedGameCore
  rw [simulateQ_bind, StateT.run_bind]
  simp only [map_bind]
  apply bind_congr
  intro keyResult
  rw [detailedGameAfterKeygenWithSigningTrace_cache_projection,
    mappedDetailedGameAfterKeygenWithCache_eq_detailed]

theorem detailedGameAfterKeygenWithSigningTrace_invariants
    (adversary : Adversary Concrete.singleAttemptScheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support
      (detailedGameAfterKeygenWithSigningTrace adversary publicKey secretKey
        initialCache)) :
    result.1.secretKey = secretKey ∧
      result.2.2.toSigningLog = result.1.signingLog ∧
      result.2.2.CachesLe result.2.1 ∧
      result.2.2.SuccessfulEncodingsCached secretKey := by
  unfold detailedGameAfterKeygenWithSigningTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, adversaryCache, trace⟩, hadversary, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  refine ⟨rfl, rfl, ?_, ?_⟩
  · have htrace := cacheTracedMappedAdversaryImpl_cachesLe publicKey secretKey
      (adversary.main publicKey) initialCache []
      (forgery, (adversaryCache, trace)) (by simp [SigningCacheTrace.CachesLe])
      hadversary
    exact htrace.mono (xmssRom_cache_le
      (Concrete.singleAttemptScheme.verify publicKey forgery.epoch forgery.message forgery.signature)
      adversaryCache (verified, finalCache) hverify)
  · exact cacheTracedMappedAdversaryImpl_successfulEncodingsCached publicKey secretKey
      (adversary.main publicKey) initialCache []
      (forgery, (adversaryCache, trace))
      (by simp [SigningCacheTrace.SuccessfulEncodingsCached]) hadversary

theorem detailedGameAfterKeygenWithSigningTrace_preservesOtherEncodingInputs
    (adversary : Adversary Concrete.singleAttemptScheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support
      (detailedGameAfterKeygenWithSigningTrace adversary publicKey secretKey
        initialCache)) :
    result.2.2.PreservesOtherEncodingInputs secretKey := by
  unfold detailedGameAfterKeygenWithSigningTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, adversaryCache, trace⟩, hadversary, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact cacheTracedMappedAdversaryImpl_preservesOtherEncodingInputs
    publicKey secretKey (adversary.main publicKey) initialCache []
    (forgery, (adversaryCache, trace))
    (by simp [SigningCacheTrace.PreservesOtherEncodingInputs]) hadversary

theorem detailedGameAfterKeygenWithSigningTrace_chronological
    (adversary : Adversary Concrete.singleAttemptScheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support
      (detailedGameAfterKeygenWithSigningTrace adversary publicKey secretKey
        initialCache)) :
    result.2.2.Chronological := by
  unfold detailedGameAfterKeygenWithSigningTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, adversaryCache, trace⟩, hadversary, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact (cacheTracedMappedAdversaryImpl_cacheOrder publicKey secretKey
    (adversary.main publicKey) initialCache []
    (forgery, (adversaryCache, trace))
    (by simp [SigningCacheTrace.Chronological])
    (by simp [SigningCacheTrace.CachesLe]) hadversary).1

theorem detailedGameWithSigningTrace_invariants
    (adversary : Adversary Concrete.singleAttemptScheme)
    (result : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support (detailedGameWithSigningTrace adversary)) :
    result.2.2.toSigningLog = result.1.signingLog ∧
      result.2.2.CachesLe result.2.1 ∧
      result.2.2.SuccessfulEncodingsCached result.1.secretKey := by
  unfold detailedGameWithSigningTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  obtain ⟨hsecretKey, hlog, hcaches, hcached⟩ :=
    detailedGameAfterKeygenWithSigningTrace_invariants adversary
      publicKey secretKey keyCache result hrest
  exact ⟨hlog, hcaches, by simpa [hsecretKey] using hcached⟩

theorem detailedGameWithSigningTrace_preservesOtherEncodingInputs
    (adversary : Adversary Concrete.singleAttemptScheme)
    (result : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support (detailedGameWithSigningTrace adversary)) :
    result.2.2.PreservesOtherEncodingInputs result.1.secretKey := by
  unfold detailedGameWithSigningTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  have hpreserves :=
    detailedGameAfterKeygenWithSigningTrace_preservesOtherEncodingInputs adversary
      publicKey secretKey keyCache result hrest
  have hsecretKey :=
    (detailedGameAfterKeygenWithSigningTrace_invariants adversary publicKey secretKey
      keyCache result hrest).1
  simpa [hsecretKey] using hpreserves

theorem detailedGameWithSigningTrace_chronological
    (adversary : Adversary Concrete.singleAttemptScheme)
    (result : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support (detailedGameWithSigningTrace adversary)) :
    result.2.2.Chronological := by
  unfold detailedGameWithSigningTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  exact detailedGameAfterKeygenWithSigningTrace_chronological adversary publicKey
    secretKey keyCache result hrest

theorem SigningCacheEntry.freshForgedEncodingCollision_finalCache_none
    (secretKey : SecretKey) (forgery : Forgery)
    (gameCache : QueryCache HashSpec) (entry : SigningCacheEntry)
    (hpreserves : entry.PreservesOtherEncodingInputs secretKey)
    (hevent : entry.FreshForgedEncodingCollision secretKey forgery gameCache) :
    entry.finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness)) = none := by
  obtain ⟨signature, _signedOutput, _forgedOutput, hsignature, hepoch,
    hinitial, _hsigned, _hforged, hne, _hdigest⟩ := hevent
  exact hpreserves signature hsignature forgery.epoch
    (forgery.message, forgery.signature.randomness) hne hinitial

theorem SigningCacheEntry.postSigningFreshForgedEncodingCollision_of_fresh
    (secretKey : SecretKey) (forgery : Forgery)
    (gameCache : QueryCache HashSpec) (entry : SigningCacheEntry)
    (hpreserves : entry.PreservesOtherEncodingInputs secretKey)
    (hevent : entry.FreshForgedEncodingCollision secretKey forgery gameCache)
    (signature : Signature) (hsignature : entry.signature = some signature)
    (hsignedFresh : entry.initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.epoch
        (entry.request.message, signature.randomness)) = none) :
    entry.PostSigningFreshForgedEncodingCollision secretKey forgery gameCache :=
  ⟨hevent, entry.freshForgedEncodingCollision_finalCache_none secretKey forgery
    gameCache hpreserves hevent, signature, hsignature, hsignedFresh⟩

theorem detailedGameWithSigningTrace_cache_enncard_le_of_mem_support
    (adversary : Adversary Concrete.singleAttemptScheme) (q : Nat)
    (hbound : HasHashQueryBound Concrete.singleAttemptScheme adversary q)
    (result : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support (detailedGameWithSigningTrace adversary)) :
    QueryCache.enncard result.2.1 ≤ (q : ℝ≥0∞) := by
  have hprojected : (result.1, result.2.1) ∈
      support (detailedGameWithCache Concrete.singleAttemptScheme adversary) := by
    rw [← detailedGameWithSigningTrace_cache_projection, support_map]
    exact ⟨result, hmem, rfl⟩
  exact Rom.detailedGame_cache_enncard_le_of_mem_support Concrete.singleAttemptScheme adversary
    q hbound (result.1, result.2.1) hprojected

theorem detailedGameWithSigningTrace_cache_finite_of_mem_support
    (adversary : Adversary Concrete.singleAttemptScheme) (q : Nat)
    (hbound : HasHashQueryBound Concrete.singleAttemptScheme adversary q)
    (result : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support (detailedGameWithSigningTrace adversary)) :
    result.2.1.toSet.Finite := by
  rw [← Set.encard_ne_top_iff]
  intro htop
  have hcard := detailedGameWithSigningTrace_cache_enncard_le_of_mem_support
    adversary q hbound result hmem
  have henncard : QueryCache.enncard result.2.1 = ∞ := by
    simp [QueryCache.enncard, htop]
  rw [henncard] at hcard
  exact ENNReal.not_top_le_coe hcard

theorem signingCacheTrace_unchanged_map_eq
    (computation : ProbComp (α × QueryCache HashSpec))
    (trace : SigningCacheTrace) :
    (fun result => ((result.1, result.2.2.toSigningLog), result.2.1)) <$>
        ((fun result => (result.1, (result.2, trace))) <$> computation) =
      (fun result =>
        ((result.1.1, trace.toSigningLog ++ result.1.2), result.2)) <$>
        ((fun result => ((result.1, ([] : QueryLog SigningSpec)), result.2)) <$>
          computation) := by
  simp only [Functor.map_map]
  apply congrArg (fun transform => transform <$> computation)
  funext result
  simp

theorem signingCacheTrace_append_map_eq
    (computation : ProbComp (Option Signature × QueryCache HashSpec))
    (trace : SigningCacheTrace) (request : SignRequest)
    (initialCache : QueryCache HashSpec) :
    (fun result => ((result.1, result.2.2.toSigningLog), result.2.1)) <$>
        ((fun result =>
          (result.1, (result.2,
            trace ++ [SigningCacheEntry.mk request result.1 initialCache result.2]))) <$>
          computation) =
      (fun result =>
        ((result.1.1, trace.toSigningLog ++ result.1.2), result.2)) <$>
        ((fun result =>
          ((result.1, [⟨request, result.1⟩]), result.2)) <$> computation) := by
  simp only [Functor.map_map]
  apply congrArg (fun transform => transform <$> computation)
  funext result
  simp [SigningCacheTrace.toSigningLog]

end XmssSecurity
