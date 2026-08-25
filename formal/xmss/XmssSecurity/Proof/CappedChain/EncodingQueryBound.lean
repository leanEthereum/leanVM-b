import XmssSecurity.Proof.CappedEncodingQueryBound
import XmssSecurity.Proof.EncodingQueryAccounting

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable def unloggedMappedAdversaryImpl
    (_publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) ProbComp) := by
  classical
  intro input
  cases input with
  | inl worldInput =>
      exact romImpl worldInput
  | inr request =>
      exact simulateQ romImpl
        (Concrete.scheme.sign secretKey request.epoch request.message)

theorem unloggedMappedAdversaryImpl_apply_inl
    (publicKey : PublicKey) (secretKey : SecretKey)
    (worldInput : OracleWorld.Domain) :
    unloggedMappedAdversaryImpl publicKey secretKey (.inl worldInput) =
      romImpl worldInput := by
  rfl

theorem unloggedMappedAdversaryImpl_apply_inr
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) :
    unloggedMappedAdversaryImpl publicKey secretKey (.inr request) =
      (simulateQ romImpl
        (Concrete.scheme.sign secretKey request.epoch request.message) :
          StateT (QueryCache HashSpec) ProbComp (Option Signature)) := by
  rfl

noncomputable def sourceUnloggedMappedAdversaryImpl
    (_publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (OracleComp OracleWorld) := by
  intro input
  cases input with
  | inl worldInput => exact liftM (OracleWorld.query worldInput)
  | inr request =>
      exact Concrete.scheme.sign secretKey request.epoch request.message

theorem sourceUnloggedMappedAdversaryImpl_withTraceAppend_eq
    (publicKey : PublicKey) (secretKey : SecretKey) :
    (sourceUnloggedMappedAdversaryImpl publicKey secretKey).withTraceAppend
        signingLogFragment =
      (forwardOracles + signingOracle Concrete.scheme secretKey) := by
  funext input
  cases input with
  | inl worldInput =>
      apply WriterT.ext
      simp [sourceUnloggedMappedAdversaryImpl, signingLogFragment, forwardOracles]
      rfl
  | inr request =>
      simp [sourceUnloggedMappedAdversaryImpl, signingLogFragment, signingOracle]

noncomputable def sourceUnloggedDetailedGameAfterKeygen
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) :
    OracleComp OracleWorld (Forgery × Bool) := do
  let forgery ← simulateQ
    (sourceUnloggedMappedAdversaryImpl publicKey secretKey)
    (adversary.main publicKey)
  let verified ← Concrete.scheme.verify publicKey forgery.epoch forgery.message
    forgery.signature
  pure (forgery, verified)

theorem detailedGameAfterKeygen_unlogged_projection
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) :
    (fun outcome : GameOutcome => (outcome.forgery, outcome.verified)) <$>
        detailedGameAfterKeygen Concrete.scheme adversary publicKey secretKey =
      sourceUnloggedDetailedGameAfterKeygen adversary publicKey secretKey := by
  let loggedAdversary :=
    (simulateQ
      ((sourceUnloggedMappedAdversaryImpl publicKey secretKey).withTraceAppend
        signingLogFragment) (adversary.main publicKey)).run
  let unloggedAdversary := simulateQ
    (sourceUnloggedMappedAdversaryImpl publicKey secretKey)
    (adversary.main publicKey)
  let finish : Forgery → OracleComp OracleWorld (Forgery × Bool) := fun forgery => do
    let verified ← Concrete.scheme.verify publicKey forgery.epoch forgery.message
      forgery.signature
    pure (forgery, verified)
  have hprojection : Prod.fst <$> loggedAdversary = unloggedAdversary := by
    exact QueryImpl.fst_map_run_withTraceAppend
      (sourceUnloggedMappedAdversaryImpl publicKey secretKey)
      signingLogFragment (adversary.main publicKey)
  rw [detailedGameAfterKeygen, ←
    sourceUnloggedMappedAdversaryImpl_withTraceAppend_eq]
  change (fun outcome : GameOutcome => (outcome.forgery, outcome.verified)) <$>
      (loggedAdversary >>= fun result => do
        let verified ← Concrete.scheme.verify publicKey result.1.epoch
          result.1.message result.1.signature
        pure ⟨publicKey, secretKey, result.1, result.2, verified⟩) = _
  simp only [map_bind, map_pure]
  unfold sourceUnloggedDetailedGameAfterKeygen
  change (loggedAdversary >>= fun result => finish result.1) =
    unloggedAdversary >>= finish
  rw [← bind_map_left, hprojection]

theorem sourceUnloggedDetailedGameAfterKeygen_hashQueryBound
    (q : Nat) (adversary : Adversary)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    (sourceUnloggedDetailedGameAfterKeygen adversary keyResult.1.1 keyResult.1.2)
      |>.IsQueryBoundP (· matches .inr _) q := by
  have hdetailed :=
    (hasHashQueryBound_iff_detailedGameCore Concrete.scheme adversary q).mp hbound
  have hkeySupport : keyResult.1 ∈ support Concrete.scheme.keygen := by
    apply support_simulateQ_run'_subset romImpl Concrete.scheme.keygen ∅
    rw [StateT.run'_eq, support_map]
    exact ⟨keyResult, hkeyResult, rfl⟩
  have hcontinuation :
      (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1
        keyResult.1.2).IsQueryBoundP (· matches .inr _) q := by
    apply OracleComp.IsQueryBoundP.bind_right_of_mem_support
      (head := Concrete.scheme.keygen)
      (next := fun key => detailedGameAfterKeygen Concrete.scheme adversary key.1 key.2)
      hdetailed keyResult.1 hkeySupport
  exact (OracleComp.isQueryBoundP_iff_of_map_eq
    (detailedGameAfterKeygen_unlogged_projection adversary keyResult.1.1
      keyResult.1.2)).mp hcontinuation

end XmssSecurity.CappedChain
