import SphincsSecurity.Proof.FirstExceptionHashCut
import SphincsSecurity.Proof.FirstExceptionPreservation
import SphincsSecurity.Proof.SigningParentSettlement

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

variable (secretKey : SecretKey)
  (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
  (hparent : ∀ cache input answer, exception cache input answer →
    ParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer)

include hparent

theorem preservesExceptionRecord_messageDigest (message : Message) (randomness : Randomness) :
    PreservesExceptionRecord exception
      (liftM (messageDigest secretKey.parameter secretKey.root message randomness : OracleComp HashSpec MessageDigest)) := by
  change PreservesExceptionRecord exception
    ((liftM (OracleWorld.query (.inr (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)))) : OracleComp OracleWorld HashOutput) >>=
      fun answer => pure (truncateMessageDigest answer))
  apply PreservesExceptionRecord.bind
  · apply PreservesExceptionRecord.query
    intro cache answer
    have hnot : ¬ exception cache (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)) answer := by
      intro hexception
      obtain ⟨_, child, _, ⟨payload, hinput⟩, _⟩ := hparent _ _ _ hexception
      have hdomain := (tweakableHashInput_injective secretKey.parameter (by trivial)
        (Position.domain_inRange child) hinput).1
      cases child <;> simp [Position.domain] at hdomain
    simp [queryException, hnot]
  · intro answer
    exact PreservesExceptionRecord.pure exception _

theorem preservesExceptionRecord_signAttempt (message : Message) (randomness : Randomness) :
    PreservesExceptionRecord exception
      (liftM (signAttempt secretKey message randomness : OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf))))) := by
  rw [signAttempt, liftM_bind]
  apply (preservesExceptionRecord_messageDigest secretKey exception hparent message randomness).bind
  intro digest
  split <;> exact PreservesExceptionRecord.pure exception _

theorem preservesExceptionRecord_signDigestLoop (message : Message) (attempts : Nat) :
    PreservesExceptionRecord exception (signDigestLoop attempts secretKey message) := by
  induction attempts with
  | zero => exact PreservesExceptionRecord.pure exception _
  | succ attempts ih =>
      rw [signDigestLoop]
      apply (PreservesExceptionRecord.lift_prob exception sampleRandomness).bind
      intro randomness
      apply (preservesExceptionRecord_signAttempt secretKey exception hparent message randomness).bind
      intro result
      cases result with
      | none => exact ih
      | some selected => exact PreservesExceptionRecord.pure exception _

theorem firstExceptionRecord_sign_hash_source
    (message : Message) (initialCache : QueryCache HashSpec)
    (result : Option Signature × QueryCache HashSpec) (record : ExceptionRecord)
    (hresult : (result, some record) ∈ support
      (runFirstException exception (sign secretKey message) initialCache none)) :
    ∃ randomness index leaves loopCache ordinal, ∃ next : HashOutput → OracleComp HashSpec (Option Signature),
      (some (randomness, index, leaves), loopCache) ∈ support
        ((simulateQ romImpl (signDigestLoop digestAttemptLimit secretKey message)).run initialCache) ∧
      (HashQueryCut.query record.input next, record.cache) ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (hashQueryCutAt (signAfterDigest secretKey randomness index leaves) ordinal)).run loopCache) := by
  rw [sign_eq_digestLoop_afterDigest, runFirstException_bind,
    preservesExceptionRecord_signDigestLoop secretKey exception hparent message digestAttemptLimit initialCache none,
    bind_map_left, mem_support_bind_iff] at hresult
  obtain ⟨⟨loop, loopCache⟩, hloop, hrest⟩ := hresult
  cases loop with
  | none => simp [runFirstException] at hrest
  | some data =>
      rcases data with ⟨randomness, index, leaves⟩
      obtain ⟨ordinal, next, hcut⟩ := firstExceptionRecord_hash_cut exception
        (signAfterDigest secretKey randomness index leaves) loopCache result record hrest
      exact ⟨randomness, index, leaves, loopCache, ordinal, next, hloop, hcut⟩

theorem firstExceptionRecord_sign_parent_input_initial
    (message : Message) (initialCache : QueryCache HashSpec)
    (result : Option Signature × QueryCache HashSpec) (record : ExceptionRecord)
    (hresult : (result, some record) ∈ support
      (runFirstException exception (sign secretKey message) initialCache none))
    {finalCache : QueryCache HashSpec} (hle : result.2 ≤ finalCache) :
    ∃ child parent,
      AtPosition secretKey.parameter record.input child ∧ child.parentOf = some parent ∧
      ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret initialCache child ∧
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret finalCache parent ∧
      initialCache (cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret finalCache parent) ≠ none := by
  obtain ⟨randomness, index, leaves, loopCache, ordinal, next, hloop, hcut⟩ :=
    firstExceptionRecord_sign_hash_source secretKey exception hparent message initialCache result record hresult
  have hvalid := runFirstException_none_valid exception (sign secretKey message) initialCache hresult record (by simp)
  exact signAfterDigest_parentSettlement_input_cached_signingEntry secretKey message randomness index leaves ordinal
    hloop hcut (agreesWithFn_fromCache record.cache) (hparent _ _ _ hvalid.2.2.1) (hvalid.2.2.2.trans hle)

theorem runFirstException_treeRoot_no_record (lay : Layer) (tree : TreeIndex)
    {result : (Digest × QueryCache HashSpec) × Option ExceptionRecord}
    (hresult : result ∈ support (runFirstException exception
      (liftM (treeRoot secretKey.parameter lay tree (secretKey.otsSecret lay tree) : OracleComp HashSpec Digest)) ∅ none)) :
    result.2 = none := by
  rcases result with ⟨result, saved⟩
  cases saved with
  | none => rfl
  | some record =>
      obtain ⟨ordinal, next, hcut⟩ := firstExceptionRecord_hash_cut exception _ ∅ result record hresult
      have hvalid := runFirstException_none_valid exception _ ∅ hresult record (by simp)
      exact False.elim (treeRoot_no_parentSettlement_at_cut secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        lay tree ordinal hcut record.input record.answer (hparent _ _ _ hvalid.2.2.1))

end SphincsSecurity.Concrete
