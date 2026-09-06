import SphincsSecurity.Proof.SigningSettlingTrace
import SphincsSecurity.Proof.HashQueryCut

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

attribute [local irreducible] instFintypePosition

theorem signDigestLoop_cache_structural_none (attempts : Nat) (secretKey : SecretKey)
    (message : Message) (beforeCache afterCache : QueryCache HashSpec)
    (result : Option (Randomness × Index × (DigestTree → FtsLeaf)))
    (hmem : (result, afterCache) ∈ support
      ((simulateQ romImpl (signDigestLoop attempts secretKey message)).run beforeCache))
    (target : HashInput) (position : Position)
    (hposition : AtPosition secretKey.parameter target position)
    (hbefore : beforeCache target = none) : afterCache target = none := by
  induction attempts generalizing beforeCache afterCache result with
  | zero =>
      simp only [signDigestLoop, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact hbefore
  | succ attempts ih =>
      rw [signDigestLoop, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨randomness, sampleCache⟩, hsample, hrest⟩ := hmem
      have hsampleRun : (randomness, sampleCache) ∈ support
          ((simulateQ (unifFwdImpl HashSpec) sampleRandomness).run beforeCache) := by
        simpa only [romImpl, QueryImpl.simulateQ_add_liftM_left] using hsample
      rw [unifFwdImpl.simulateQ_run, support_map] at hsampleRun
      obtain ⟨sampledRandomness, _, heq⟩ := hsampleRun
      obtain ⟨rfl, rfl⟩ := heq
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨attempt, attemptCache⟩, hattempt, hfinish⟩ := hrest
      have hattempt' : (attempt, attemptCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec _)
            (signAttempt secretKey message randomness)).run beforeCache) := by
        simpa only [simulateQ_romImpl_liftM] using hattempt
      have hne : target ≠ tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness) := by
        intro heq
        obtain ⟨payload, htarget⟩ := hposition
        have hdomain := (tweakableHashInput_injective secretKey.parameter (Position.domain_inRange position)
          (by trivial) (htarget.symm.trans heq)).1
        cases position <;> simp [Position.domain] at hdomain
      have hattemptNone : attemptCache target = none :=
        signAttempt_cache_other_none secretKey message randomness beforeCache attemptCache
          attempt hattempt' target hbefore hne
      cases attempt with
      | none => exact ih attemptCache afterCache result hfinish hattemptNone
      | some selected =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hfinish
          obtain ⟨rfl, rfl⟩ := hfinish
          exact hattemptNone

theorem signAfterDigest_parentSettlement_input_cached_signingEntry
    (secretKey : SecretKey) (message : Message) (randomness : Randomness)
    (index : Index) (leaves : DigestTree → FtsLeaf) (ordinal : Nat)
    {initialCache loopCache middleCache finalCache : QueryCache HashSpec}
    (hloop : (some (randomness, index, leaves), loopCache) ∈ support
      ((simulateQ romImpl (signDigestLoop digestAttemptLimit secretKey message)).run initialCache))
    {cut : HashQueryCut (Option Signature)}
    (hcut : (cut, middleCache) ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (hashQueryCutAt (signAfterDigest secretKey randomness index leaves) ordinal)).run loopCache))
    {f : QueryImpl HashSpec Id} (hf : middleCache.AgreesWithFn f)
    {input : HashInput} {answer : HashOutput}
    (hparent : ParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret middleCache input answer)
    (hle : middleCache.cacheQuery input answer ≤ finalCache) :
    ∃ child parent,
      AtPosition secretKey.parameter input child ∧ child.parentOf = some parent ∧
      ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret initialCache child ∧
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret finalCache parent ∧
      initialCache (cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret finalCache parent) ≠ none := by
  obtain ⟨child, parent, hat, hparentOf, hunsettled, hsettled, hcached⟩ :=
    (settlingRun_signAfterDigest f secretKey randomness index leaves).parentSettlement_input_cached_initial
      ordinal hcut hf hparent hle
  have hloopLe := simulateQ_romImpl_cache_le _ _ _ hloop
  have hcutLe := (replay_of_mem_support _ _ _ _ hcut f hf).1
  refine ⟨child, parent, hat, hparentOf, ?_, hsettled, ?_⟩
  · exact fun hs => hunsettled (hs.mono (hloopLe.trans hcutLe))
  · intro hnone
    exact hcached (signDigestLoop_cache_structural_none digestAttemptLimit secretKey message initialCache loopCache
      _ hloop _ parent (atPosition_cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret finalCache parent)
      hnone)

theorem treeRoot_no_parentSettlement_at_cut
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (lay : Layer) (tree : TreeIndex) (ordinal : Nat)
    {middleCache : QueryCache HashSpec} {cut : HashQueryCut Digest}
    (hcut : (cut, middleCache) ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (hashQueryCutAt (treeRoot parameter lay tree (otsSecret lay tree)) ordinal)).run ∅))
    (input : HashInput) (answer : HashOutput) :
    ¬ ParentSettlement parameter otsSecret ftsSecret middleCache input answer := by
  intro hparent
  have hsettling := settlingRun_treeRoot parameter otsSecret ftsSecret (fromCache middleCache) lay tree
  have h := hsettling.parentSettlement_input_cached_initial ordinal hcut (agreesWithFn_fromCache middleCache) hparent le_rfl
  obtain ⟨child, parent, _, _, _, _, hcached⟩ := h
  exact hcached rfl

end SphincsSecurity.Concrete
