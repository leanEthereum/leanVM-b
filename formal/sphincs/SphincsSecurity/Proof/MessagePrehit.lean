import SphincsSecurity.Proof.Replay
import SphincsSecurity.Proof.NoMessage
import SphincsSecurity.Proof.StatementLemmas
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Cached message inputs

A uniformly sampled signer randomizer addresses an input already in a fixed cache with probability
at most the number of matching cache entries divided by the randomizer space. This is used only
while retaining the few-time coverage event that the cached answer must also satisfy.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

def cachedMessageInputSet (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (root : Digest) (message : Message) :
    Set ((t : HashSpec.Domain) × HashSpec.Range t) :=
  {entry ∈ cache.toSet | ∃ randomness,
    entry.1 = tweakableHashInput parameter .message
      (Concrete.messageDigestPayload root message randomness)}

noncomputable def cachedMessageEntryCount (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (root : Digest) (message : Message) : ℝ≥0∞ :=
  (((cachedMessageInputSet cache parameter root message).encard : ENat) : ℝ≥0∞)

theorem card_randomness : Fintype.card Randomness = 2 ^ randomnessBits := by
  simp

noncomputable def Concrete.signDigestLoopContinuation
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (randomness : Randomness)
    (result : Option (Index × (DigestTree → FtsLeaf)) × QueryCache HashSpec) :
    ProbComp (Option (Randomness × Index × (DigestTree → FtsLeaf)) ×
      QueryCache HashSpec) :=
  match result.1 with
  | some (index, leaves) => pure (some (randomness, index, leaves), result.2)
  | none => (simulateQ romImpl
      (Concrete.signDigestLoop attempts secretKey message)).run result.2

attribute [irreducible] Concrete.signDigestLoopContinuation

theorem Concrete.signDigestLoop_run_succ_eq
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl
      (Concrete.signDigestLoop (attempts + 1) secretKey message)).run cache =
      (($ᵗ Randomness) >>= fun randomness =>
        (simulateQ randomOracle
          (Concrete.signAttempt secretKey message randomness :
            OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf))))).run cache >>=
          Concrete.signDigestLoopContinuation attempts secretKey message randomness) := by
  rw [Concrete.signDigestLoop, simulateQ_bind, StateT.run_bind]
  have hsampleRun :
      (simulateQ romImpl (liftM Concrete.sampleRandomness)).run cache =
        (fun randomness => (randomness, cache)) <$> Concrete.sampleRandomness := by
    change (simulateQ (unifFwdImpl HashSpec +
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp)))
      (liftM Concrete.sampleRandomness)).run cache = _
    exact roSim.run_liftM
      (hashSpec := HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      Concrete.sampleRandomness cache
  rw [hsampleRun, Concrete.sampleRandomness_eq]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr
  intro randomness
  rw [simulateQ_bind, StateT.run_bind]
  have hroute :
      simulateQ romImpl
          (liftM (Concrete.signAttempt secretKey message randomness :
            OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf))))) =
        simulateQ randomOracle
          (Concrete.signAttempt secretKey message randomness :
            OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))) := by
    change simulateQ (unifFwdImpl HashSpec + randomOracle)
        (liftM (Concrete.signAttempt secretKey message randomness :
          OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf))))) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.signAttempt secretKey message randomness :
        OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf))))
  rw [hroute]
  apply bind_congr
  intro result
  rcases result with ⟨result, resultCache⟩
  cases result with
  | none => simp [Concrete.signDigestLoopContinuation]
  | some selected =>
      rcases selected with ⟨index, leaves⟩
      simp [Concrete.signDigestLoopContinuation]

set_option maxRecDepth 100000 in
theorem uniform_randomness_messageInput_cacheHit_le_cachedMessageEntryCount
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) :
    Pr[fun randomness : Randomness => ∃ output,
      cache (tweakableHashInput parameter .message
        (Concrete.messageDigestPayload root message randomness)) = some output |
      $ᵗ Randomness] ≤
      cachedMessageEntryCount cache parameter root message *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  let hit : Randomness → Prop := fun randomness => ∃ output,
    cache (tweakableHashInput parameter .message
      (Concrete.messageDigestPayload root message randomness)) = some output
  let targets : Finset Randomness := Finset.univ.filter hit
  let fiber := cachedMessageInputSet cache parameter root message
  have hcard : (targets.card : ℝ≥0∞) ≤
      cachedMessageEntryCount cache parameter root message := by
    let embedding : (targets : Set Randomness) ↪ fiber :=
      ⟨fun randomness =>
          ⟨⟨tweakableHashInput parameter .message
                (Concrete.messageDigestPayload root message randomness.1),
              Classical.choose (Finset.mem_filter.mp randomness.2).2⟩,
            ⟨Classical.choose_spec (Finset.mem_filter.mp randomness.2).2,
              ⟨randomness.1, rfl⟩⟩⟩,
        fun left right heq => Subtype.ext <|
          (Concrete.messageDigestPayload_injective root <|
            (tweakableHashInput_injective parameter (by trivial) (by trivial) <|
              congrArg (fun entry : fiber => entry.1.1) heq).2).2⟩
    simpa only [cachedMessageEntryCount, fiber,
      Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe] using
      ENat.toENNReal_mono embedding.encard_le
  rw [probEvent_uniformSample, card_randomness, div_eq_mul_inv]
  change (targets.card : ℝ≥0∞) *
      ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ ≤ _
  exact mul_le_mul' hcard le_rfl

set_option linter.constructorNameAsVariable false in
theorem Concrete.signDigestLoop_messageInput_referenceCache_hit_le_cachedCount
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) :
    Pr[fun result : Option (Randomness × Index × (DigestTree → FtsLeaf)) ×
        QueryCache HashSpec =>
      ∃ randomness index leaves, result.1 = some (randomness, index, leaves) ∧
        ∃ output, referenceCache
          (tweakableHashInput secretKey.parameter .message
            (Concrete.messageDigestPayload secretKey.root message randomness)) = some output |
      (simulateQ romImpl
        (Concrete.signDigestLoop attempts secretKey message)).run workingCache] ≤
      (attempts : ℝ≥0∞) *
        cachedMessageEntryCount referenceCache secretKey.parameter secretKey.root message *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction attempts generalizing workingCache with
  | zero =>
      simp [Concrete.signDigestLoop]
  | succ attempts ih =>
      rw [Concrete.signDigestLoop_run_succ_eq]
      refine (probEvent_bind_le_probEvent_add
        (p := fun randomness : Randomness => ∃ output,
          referenceCache
            (tweakableHashInput secretKey.parameter .message
              (Concrete.messageDigestPayload secretKey.root message randomness)) = some output)
        (ε := (attempts : ℝ≥0∞) *
          cachedMessageEntryCount referenceCache secretKey.parameter secretKey.root message *
          ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
      · intro randomness _hrandomness hmiss
        refine probEvent_bind_le_of_forall_le fun attemptResult _hattempt => ?_
        cases hresult : attemptResult.1 with
        | none =>
            simpa [Concrete.signDigestLoopContinuation, hresult] using
              ih attemptResult.2
        | some selected =>
            rcases selected with ⟨selectedIndex, selectedLeaves⟩
            refine le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
            intro result hsupport hevent
            have hsupport' : result ∈ support
                (pure (some (randomness, selectedIndex, selectedLeaves), attemptResult.2) :
                  ProbComp (Option (Randomness × Index × (DigestTree → FtsLeaf)) ×
                    QueryCache HashSpec)) := by
              simpa [Concrete.signDigestLoopContinuation, hresult] using hsupport
            obtain ⟨foundRandomness, foundIndex, foundLeaves, hfound, output, hhit⟩ := hevent
            have hreturned : result.1 =
                some (randomness, selectedIndex, selectedLeaves) := by
              simpa only [support_pure, Set.mem_singleton_iff] using
                congrArg Prod.fst hsupport'
            have hrandomness : randomness = foundRandomness := congrArg Prod.fst <|
              Option.some.inj (hreturned.symm.trans hfound)
            apply hmiss
            refine ⟨output, ?_⟩
            rw [hrandomness]
            exact hhit
      · calc
          _ ≤ cachedMessageEntryCount referenceCache secretKey.parameter secretKey.root message *
                ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ +
              (attempts : ℝ≥0∞) *
                cachedMessageEntryCount referenceCache secretKey.parameter secretKey.root message *
                ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ :=
            add_le_add
              (uniform_randomness_messageInput_cacheHit_le_cachedMessageEntryCount
                secretKey.parameter secretKey.root message referenceCache) le_rfl
          _ = _ := by
            push_cast
            ring

theorem Concrete.signAfterDigest_some_randomness (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : DigestTree → FtsLeaf) (signature : Signature)
    (heval : evalWithAnswerFn f
      (Concrete.signAfterDigest secretKey randomness index leaves) = some signature) :
    signature.randomness = randomness := by
  simp only [Concrete.signAfterDigest, evalWithAnswerFn_bind] at heval
  split at heval
  · simp only [evalWithAnswerFn_pure, reduceCtorEq] at heval
  · simp only [evalWithAnswerFn_pure, Option.some.injEq] at heval
    subst signature
    rfl

theorem Concrete.signAfterDigest_support_some_randomness
    (secretKey : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : DigestTree → FtsLeaf) (beforeCache afterCache : QueryCache HashSpec)
    (signature : Signature)
    (hmem : (some signature, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (Concrete.signAfterDigest secretKey randomness index leaves)).run beforeCache)) :
    signature.randomness = randomness := by
  obtain ⟨_, answerFn, _, heval⟩ :=
    exists_answerFn_agrees_final_of_mem_support
      (Concrete.signAfterDigest secretKey randomness index leaves)
      beforeCache (some signature) afterCache hmem
  exact Concrete.signAfterDigest_some_randomness answerFn secretKey randomness index leaves
    signature heval

set_option linter.constructorNameAsVariable false in
theorem Concrete.sign_messageInput_initialCache_hit_le_cachedCount
    (secretKey : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    Pr[fun result : Option Signature × QueryCache HashSpec =>
      ∃ signature, result.1 = some signature ∧ ∃ output,
        cache (tweakableHashInput secretKey.parameter .message
          (Concrete.messageDigestPayload secretKey.root message signature.randomness)) =
            some output |
      (simulateQ romImpl (Concrete.sign secretKey message)).run cache] ≤
      (digestAttemptLimit : ℝ≥0∞) *
        cachedMessageEntryCount cache secretKey.parameter secretKey.root message *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [Concrete.sign_eq_digestLoop_afterDigest, simulateQ_bind, StateT.run_bind]
  refine (probEvent_bind_le_probEvent
    (p := fun loopResult : Option (Randomness × Index × (DigestTree → FtsLeaf)) ×
        QueryCache HashSpec =>
      ∃ randomness index leaves, loopResult.1 = some (randomness, index, leaves) ∧
        ∃ output, cache
          (tweakableHashInput secretKey.parameter .message
            (Concrete.messageDigestPayload secretKey.root message randomness)) = some output)
    ?_).trans
      (Concrete.signDigestLoop_messageInput_referenceCache_hit_le_cachedCount
        digestAttemptLimit secretKey message cache cache)
  intro loopResult _hloop hmiss
  refine probEvent_eq_zero ?_
  intro result hresult hevent
  cases hloopResult : loopResult.1 with
  | none =>
      have hresult' : result ∈ support
          (pure (none, loopResult.2) :
            ProbComp (Option Signature × QueryCache HashSpec)) := by
        simpa [hloopResult] using hresult
      obtain ⟨signature, hsignature, _⟩ := hevent
      have hnone : result.1 = none := by
        simpa only [support_pure, Set.mem_singleton_iff] using
          congrArg Prod.fst hresult'
      simp [hnone] at hsignature
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      obtain ⟨signature, hsignature, output, hhit⟩ := hevent
      have hresult' : (some signature, result.2) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec _)
            (Concrete.signAfterDigest secretKey randomness index leaves)).run loopResult.2) := by
        have hpair : result = (some signature, result.2) := Prod.ext hsignature rfl
        rw [← hpair]
        simpa only [hloopResult, simulateQ_romImpl_liftM] using hresult
      have hrandomness := Concrete.signAfterDigest_support_some_randomness secretKey randomness
        index leaves loopResult.2 result.2 signature hresult'
      apply hmiss
      refine ⟨randomness, index, leaves, hloopResult, output, ?_⟩
      rw [← hrandomness]
      exact hhit

end SphincsSecurity
