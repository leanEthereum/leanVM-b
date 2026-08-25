import SphincsSecurity.Proof.FewTimeLoop

/-!
# Signer digest views

This proof-only signer exposes the few-time view selected by the digest loop alongside the ordinary
signature result. Forgetting the extra component recovers the concrete signer exactly.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def selectedFewTimeView (index : Index) (leaves : DigestTree → FtsLeaf) : FewTimeView :=
  (index, fun tree => leaves (ftsIndexOf tree))

noncomputable def signWithView (secretKey : SecretKey) (message : Message) :
    OracleComp OracleWorld (Option Signature × Option FewTimeView) := do
  match ← signDigestLoop digestAttemptLimit secretKey message with
  | none => pure (none, none)
  | some (randomness, index, leaves) => do
      let signature ← liftM (signAfterDigest secretKey randomness index leaves)
      pure (signature, some (selectedFewTimeView index leaves))

theorem signWithView_fst (secretKey : SecretKey) (message : Message) :
    Prod.fst <$> signWithView secretKey message = sign secretKey message := by
  rw [sign_eq_digestLoop_afterDigest]
  simp only [signWithView, map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro loopResult
  cases loopResult with
  | none => simp
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      simp

theorem simulateQ_signWithView_fst_run (secretKey : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    (fun result => (result.1.1, result.2)) <$>
        (simulateQ romImpl (signWithView secretKey message)).run cache =
      (simulateQ romImpl (sign secretKey message)).run cache := by
  calc
    _ = (simulateQ romImpl (Prod.fst <$> signWithView secretKey message)).run cache := by
      rw [simulateQ_map, StateT.run_map]
    _ = _ := by rw [signWithView_fst]

def verifyWithView (publicKey : PublicKey) (message : Message) (signature : Signature) :
    OracleComp HashSpec (Bool × FewTimeView) := do
  let output ← oracleHash (tweakableHashInput publicKey.parameter .message
    (messageDigestPayload publicKey.root message signature.randomness))
  let digest := truncateMessageDigest output
  let view := hashOutputFewTimeView output
  if ¬ Admissible digest then
    pure (false, view)
  else
    let ftsPublicKey ← ftsRecover publicKey.parameter (digestIndex digest)
      (digestLeaves digest) signature.ftsSecret signature.ftsPath
    match ← verifyLayers publicKey.parameter (digestIndex digest) signature numLayers
        ftsPublicKey with
    | none => pure (false, view)
    | some root => pure (decide (root = publicKey.root), view)

set_option maxHeartbeats 1000000 in
theorem verifyWithView_fst (publicKey : PublicKey) (message : Message)
    (signature : Signature) :
    Prod.fst <$> verifyWithView publicKey message signature =
      verify publicKey message signature := by
  rw [verify_eq]
  simp only [verifyWithView, messageDigest, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  apply bind_congr
  intro output
  let digest := truncateMessageDigest output
  by_cases hadmissible : Admissible digest
  · change Admissible (truncateMessageDigest output) at hadmissible
    simp only [hadmissible, not_true_eq_false, ↓reduceIte]
    simp only [bind_assoc]
    apply bind_congr
    intro ftsPublicKey
    apply bind_congr
    intro root
    cases root <;> simp
  · change ¬ Admissible (truncateMessageDigest output) at hadmissible
    simp [hadmissible]

theorem simulateQ_verifyWithView_fst_run (publicKey : PublicKey) (message : Message)
    (signature : Signature) (cache : QueryCache HashSpec) :
    (fun result => (result.1.1, result.2)) <$>
        (simulateQ romImpl
          (liftM (verifyWithView publicKey message signature) :
            OracleComp OracleWorld (Bool × FewTimeView))).run cache =
      (simulateQ romImpl
        (Concrete.scheme.verify publicKey message signature)).run cache := by
  rw [show Concrete.scheme.verify publicKey message signature =
    (liftM (verify publicKey message signature) : OracleComp OracleWorld Bool) from rfl]
  simp only [simulateQ_romImpl_liftM]
  calc
    _ = (simulateQ (randomOracle : QueryImpl HashSpec _)
        (Prod.fst <$> verifyWithView publicKey message signature)).run cache := by
      rw [simulateQ_map, StateT.run_map]
    _ = _ := by rw [verifyWithView_fst]

theorem verifyWithView_support_view (publicKey : PublicKey) (message : Message)
    (signature : Signature) (initialCache finalCache : QueryCache HashSpec)
    (verified : Bool) (view : FewTimeView)
    (hmem : ((verified, view), finalCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (verifyWithView publicKey message signature)).run initialCache)) :
    ∃ (output : HashOutput) (digestCache : QueryCache HashSpec),
      (output, digestCache) ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (oracleHash (tweakableHashInput publicKey.parameter .message
            (messageDigestPayload publicKey.root message signature.randomness)))).run initialCache)
        ∧ digestCache ≤ finalCache
        ∧ view = hashOutputFewTimeView output := by
  rw [verifyWithView, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨output, digestCache⟩, houtput, hrest⟩ := hmem
  let rest : OracleComp HashSpec (Bool × FewTimeView) :=
    let digest := truncateMessageDigest output
    let view := hashOutputFewTimeView output
    if ¬ Admissible digest then
      pure (false, view)
    else do
      let ftsPublicKey ← ftsRecover publicKey.parameter (digestIndex digest)
        (digestLeaves digest) signature.ftsSecret signature.ftsPath
      match ← verifyLayers publicKey.parameter (digestIndex digest) signature numLayers
          ftsPublicKey with
      | none => pure (false, view)
      | some root => pure (decide (root = publicKey.root), view)
  change ((verified, view), finalCache) ∈ support
    ((simulateQ (randomOracle : QueryImpl HashSpec _) rest).run digestCache) at hrest
  have hrest' : ((verified, view), finalCache) ∈ support
      ((simulateQ romImpl (liftM rest : OracleComp OracleWorld _)).run digestCache) := by
    simpa only [simulateQ_romImpl_liftM] using hrest
  have hcacheLe : digestCache ≤ finalCache :=
    simulateQ_romImpl_cache_le (liftM rest : OracleComp OracleWorld _)
      digestCache ((verified, view), finalCache) hrest'
  refine ⟨output, digestCache, ?_, hcacheLe, ?_⟩
  · exact houtput
  · by_cases hadmissible : Admissible (truncateMessageDigest output)
    · simp only [rest, hadmissible, not_true_eq_false, ↓reduceIte, simulateQ_bind,
        StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨ftsPublicKey, ftsCache⟩, _, hrest⟩ := hrest
      obtain ⟨⟨root, rootCache⟩, _, hresult⟩ := hrest
      cases root with
      | none =>
          have heq : ((verified, view), finalCache) =
              ((false, hashOutputFewTimeView output), rootCache) := by
            simpa only [simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] using hresult
          exact congrArg (fun result => result.1.2) heq
      | some root =>
          have heq : ((verified, view), finalCache) =
              ((decide (root = publicKey.root), hashOutputFewTimeView output), rootCache) := by
            simpa only [simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] using hresult
          exact congrArg (fun result => result.1.2) heq
    · simp only [rest, hadmissible, not_false_eq_true, ↓reduceIte,
        simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
      exact congrArg (fun result => result.1.2) hrest

set_option linter.constructorNameAsVariable false in
theorem signWithView_support_some
    (secretKey : SecretKey) (message : Message)
    (initialCache finalCache : QueryCache HashSpec)
    (signature : Signature) (view : Option FewTimeView)
    (hmem : ((some signature, view), finalCache) ∈ support
      ((simulateQ romImpl (signWithView secretKey message)).run initialCache)) :
    ∃ (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
        (loopCache : QueryCache HashSpec),
      (some (randomness, index, leaves), loopCache) ∈ support
          ((simulateQ romImpl
            (signDigestLoop digestAttemptLimit secretKey message)).run initialCache)
        ∧ (some signature, finalCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec
            (StateT (QueryCache HashSpec) ProbComp))
            (signAfterDigest secretKey randomness index leaves)).run loopCache)
        ∧ view = some (selectedFewTimeView index leaves) := by
  rw [signWithView, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨loopResult, loopCache⟩, hloop, hfinish⟩ := hmem
  cases loopResult with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, reduceCtorEq, false_and] at hfinish
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hfinish
      obtain ⟨⟨signatureResult, signatureCache⟩, hsignature, hpure⟩ := hfinish
      have hpureEq : ((some signature, view), finalCache) =
          ((signatureResult, some (selectedFewTimeView index leaves)), signatureCache) := by
        simpa only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hpure
      have hresult : some signature = signatureResult :=
        congrArg (fun result => result.1.1) hpureEq
      have hview : view = some (selectedFewTimeView index leaves) :=
        congrArg (fun result => result.1.2) hpureEq
      have hcache : finalCache = signatureCache := congrArg Prod.snd hpureEq
      rw [← hresult, ← hcache] at hsignature
      refine ⟨randomness, index, leaves, loopCache, hloop, ?_, hview⟩
      simpa only [simulateQ_romImpl_liftM] using hsignature

end SphincsSecurity.Concrete
