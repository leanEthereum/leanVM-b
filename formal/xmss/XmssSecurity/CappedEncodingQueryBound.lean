import XmssSecurity.CappedEncodingOracleSimulation
import XmssSecurity.EncodingQueryBound

open OracleComp OracleSpec

namespace XmssSecurity

set_option maxRecDepth 100000

noncomputable def cappedNormalizedSplitUnloggedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey)
    (kind : EncodingSampleKind) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) (OracleComp EncodingSamplingWorld)) := by
  intro input
  cases input with
  | inl worldInput =>
      exact splitXmssRomImpl secretKey.parameter kind worldInput
  | inr request =>
      exact simulateQ (splitXmssRomImpl secretKey.parameter kind)
        (Concrete.scheme.sign publicKey secretKey request.epoch request.message)

noncomputable def cappedSourceUnloggedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (OracleComp OracleWorld) := by
  intro input
  cases input with
  | inl worldInput => exact liftM (OracleWorld.query worldInput)
  | inr request =>
      exact Concrete.scheme.sign publicKey secretKey request.epoch request.message

theorem cappedNormalizedSplitUnloggedMappedAdversaryImpl_eq_compose
    (publicKey : PublicKey) (secretKey : SecretKey)
    (kind : EncodingSampleKind) :
    cappedNormalizedSplitUnloggedMappedAdversaryImpl publicKey secretKey kind =
      splitXmssRomImpl secretKey.parameter kind ∘ₛ
        cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey := by
  funext input
  cases input with
  | inl worldInput =>
      simp [cappedNormalizedSplitUnloggedMappedAdversaryImpl,
        cappedSourceUnloggedMappedAdversaryImpl]
  | inr request => rfl

theorem cappedNormalizedSplitUnloggedMappedAdversary_simulateQ_run_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (kind : EncodingSampleKind)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) :
    (simulateQ (cappedNormalizedSplitUnloggedMappedAdversaryImpl publicKey secretKey kind)
        computation).run cache =
      (simulateQ (splitXmssRomImpl secretKey.parameter kind)
        (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
          computation)).run cache := by
  rw [cappedNormalizedSplitUnloggedMappedAdversaryImpl_eq_compose,
    QueryImpl.simulateQ_compose]

theorem cappedSourceUnloggedMappedAdversaryImpl_withTraceAppend_eq
    (publicKey : PublicKey) (secretKey : SecretKey) :
    (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey).withTraceAppend
        signingLogFragment =
      ((HasQuery.toQueryImpl
          (spec := OracleWorld) (m := OracleComp OracleWorld)).liftTarget
            (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
        signingOracle Concrete.scheme publicKey secretKey) := by
  funext input
  cases input with
  | inl worldInput =>
      apply WriterT.ext
      simp [cappedSourceUnloggedMappedAdversaryImpl, signingLogFragment,
        HasQuery.toQueryImpl]
  | inr request =>
      simp [cappedSourceUnloggedMappedAdversaryImpl, signingLogFragment, signingOracle]

noncomputable def cappedSourceUnloggedDetailedGameAfterKeygen
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) :
    OracleComp OracleWorld (Forgery × Bool) := do
  let forgery ← simulateQ
    (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
    (adversary.main publicKey)
  let verified ← Concrete.scheme.verify publicKey forgery.epoch forgery.message
    forgery.signature
  pure (forgery, verified)

theorem cappedDetailedGameAfterKeygen_unloggedProjection
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) :
    (fun outcome : GameOutcome => (outcome.forgery, outcome.verified)) <$>
        detailedGameAfterKeygen Concrete.scheme adversary publicKey secretKey =
      cappedSourceUnloggedDetailedGameAfterKeygen adversary publicKey secretKey := by
  let loggedAdversary :=
    (simulateQ
      ((cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey).withTraceAppend
        signingLogFragment) (adversary.main publicKey)).run
  let unloggedAdversary := simulateQ
    (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
    (adversary.main publicKey)
  let finish : Forgery → OracleComp OracleWorld (Forgery × Bool) := fun forgery => do
    let verified ← Concrete.scheme.verify publicKey forgery.epoch forgery.message
      forgery.signature
    pure (forgery, verified)
  have hprojection : Prod.fst <$> loggedAdversary = unloggedAdversary := by
    exact QueryImpl.fst_map_run_withTraceAppend
      (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
      signingLogFragment (adversary.main publicKey)
  rw [detailedGameAfterKeygen, ←
    cappedSourceUnloggedMappedAdversaryImpl_withTraceAppend_eq]
  change (fun outcome : GameOutcome => (outcome.forgery, outcome.verified)) <$>
      (loggedAdversary >>= fun result => do
        let verified ← Concrete.scheme.verify publicKey result.1.epoch
          result.1.message result.1.signature
        pure ⟨publicKey, secretKey, result.1, result.2, verified⟩) = _
  simp only [map_bind, map_pure]
  unfold cappedSourceUnloggedDetailedGameAfterKeygen
  change (loggedAdversary >>= fun result => finish result.1) =
    unloggedAdversary >>= finish
  rw [← bind_map_left, hprojection]

theorem cappedSourceUnloggedDetailedGameAfterKeygen_hashQueryBound
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅)) :
    (cappedSourceUnloggedDetailedGameAfterKeygen adversary keyResult.1.1 keyResult.1.2)
      |>.IsQueryBoundP (· matches .inr _) q := by
  have hdetailed :=
    (hasHashQueryBound_iff_detailedGameCore Concrete.scheme adversary q).mp hbound
  have hkeySupport : keyResult.1 ∈ support Concrete.scheme.keygen := by
    apply support_simulateQ_run'_subset xmssRomImpl Concrete.scheme.keygen ∅
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
    (cappedDetailedGameAfterKeygen_unloggedProjection adversary keyResult.1.1
      keyResult.1.2)).mp hcontinuation

theorem cappedSplitUnloggedMappedAdversaryImpl_bind_normalized_isQueryBoundP_iff
    (publicKey : PublicKey) (secretKey : SecretKey)
    (kind : EncodingSampleKind)
    (input : (OracleWorld + SigningSpec).Domain)
    (cache : QueryCache HashSpec)
    (leftNext rightNext :
      (OracleWorld + SigningSpec).Range input × QueryCache HashSpec →
        OracleComp EncodingSamplingWorld α)
    (hnext : ∀ result fuel,
      (leftNext result).IsQueryBoundP (· matches .inr _) fuel ↔
        (rightNext result).IsQueryBoundP (· matches .inr _) fuel)
    (fuel : Nat) :
    (((cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey input).run cache >>=
        leftNext) |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      (((cappedNormalizedSplitUnloggedMappedAdversaryImpl publicKey secretKey kind input).run
        cache >>= rightNext) |>.IsQueryBoundP (· matches .inr _) fuel) := by
  cases input with
  | inl worldInput =>
      simp only [cappedSplitUnloggedMappedAdversaryImpl,
        cappedNormalizedSplitUnloggedMappedAdversaryImpl]
      exact splitXmssRom_bind_kind_isQueryBoundP_iff secretKey.parameter .query
        kind worldInput cache leftNext rightNext hnext fuel
  | inr request =>
      simp only [cappedSplitUnloggedMappedAdversaryImpl,
        cappedNormalizedSplitUnloggedMappedAdversaryImpl]
      exact splitXmssRom_simulateQ_bind_kind_isQueryBoundP_iff
        secretKey.parameter .sign kind
        (Concrete.scheme.sign publicKey secretKey request.epoch request.message)
        cache leftNext rightNext hnext fuel

theorem cappedSplitUnloggedMappedAdversary_normalized_isQueryBoundP_iff
    (publicKey : PublicKey) (secretKey : SecretKey)
    (kind : EncodingSampleKind)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (fuel : Nat) :
    (((simulateQ (cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey)
        computation).run cache) |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      (((simulateQ (cappedNormalizedSplitUnloggedMappedAdversaryImpl publicKey secretKey kind)
        computation).run cache) |>.IsQueryBoundP (· matches .inr _) fuel) := by
  induction computation using OracleComp.inductionOn generalizing cache fuel with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind,
        simulateQ_query_bind, StateT.run_bind]
      simp only [OracleQuery.input_query, monadLift_self]
      exact cappedSplitUnloggedMappedAdversaryImpl_bind_normalized_isQueryBoundP_iff
        publicKey secretKey kind input cache
          (fun result =>
            (simulateQ (cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey)
              (next result.1)).run result.2)
          (fun result =>
            (simulateQ
              (cappedNormalizedSplitUnloggedMappedAdversaryImpl publicKey secretKey kind)
              (next result.1)).run result.2)
          (fun result remaining => ih result.1 result.2 remaining) fuel

theorem cappedSplitUnloggedMappedAdversary_bind_normalized_isQueryBoundP_iff
    (publicKey : PublicKey) (secretKey : SecretKey)
    (kind : EncodingSampleKind)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec)
    (leftNext rightNext : α × QueryCache HashSpec →
      OracleComp EncodingSamplingWorld β)
    (hnext : ∀ result fuel,
      (leftNext result).IsQueryBoundP (· matches .inr _) fuel ↔
        (rightNext result).IsQueryBoundP (· matches .inr _) fuel)
    (fuel : Nat) :
    ((((simulateQ (cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey)
        computation).run cache) >>= leftNext)
      |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      ((((simulateQ
        (cappedNormalizedSplitUnloggedMappedAdversaryImpl publicKey secretKey kind)
          computation).run cache) >>= rightNext)
      |>.IsQueryBoundP (· matches .inr _) fuel) := by
  induction computation using OracleComp.inductionOn generalizing cache fuel with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact hnext (value, cache) fuel
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, bind_assoc,
        simulateQ_query_bind, StateT.run_bind, bind_assoc]
      simp only [OracleQuery.input_query, monadLift_self]
      exact cappedSplitUnloggedMappedAdversaryImpl_bind_normalized_isQueryBoundP_iff
        publicKey secretKey kind input cache
          (fun result =>
            (simulateQ (cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey)
              (next result.1)).run result.2 >>= leftNext)
          (fun result =>
            (simulateQ
              (cappedNormalizedSplitUnloggedMappedAdversaryImpl publicKey secretKey kind)
              (next result.1)).run result.2 >>= rightNext)
          (fun result remaining => ih result.1 result.2 remaining) fuel

theorem cappedSplitEncodingTracedMappedAdversary_isQueryBoundP_iff_unlogged
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialSigningTrace : SigningCacheTrace)
    (initialEncodingTrace : EncodingActionTrace) (fuel : Nat) :
    (((simulateQ (cappedSplitEncodingTracedMappedAdversaryImpl publicKey secretKey)
        computation).run ((initialCache, initialSigningTrace), initialEncodingTrace))
      |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      (((simulateQ (cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey)
        computation).run initialCache) |>.IsQueryBoundP (· matches .inr _) fuel) := by
  have hencoding := OracleComp.extendState_run_proj_eq
    (cappedSplitCacheTracedMappedAdversaryImpl publicKey secretKey)
    (encodingActionTraceUpdate secretKey) computation
    (initialCache, initialSigningTrace) initialEncodingTrace
  have hsigning := OracleComp.extendState_run_proj_eq
    (cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey)
    signingCacheTraceUpdate computation initialCache initialSigningTrace
  exact (OracleComp.isQueryBoundP_iff_of_map_eq hencoding).trans
    (OracleComp.isQueryBoundP_iff_of_map_eq hsigning)

noncomputable def cappedSplitUnloggedDetailedGameAfterKeygen
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    OracleComp EncodingSamplingWorld ((Forgery × Bool) × QueryCache HashSpec) := do
  let (forgery, adversaryCache) ←
    (simulateQ (cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run initialCache
  let (verified, finalCache) ←
    (simulateQ (splitXmssRomImpl secretKey.parameter .query)
      (Concrete.scheme.verify publicKey forgery.epoch forgery.message
        forgery.signature)).run adversaryCache
  pure ((forgery, verified), finalCache)

noncomputable def cappedNormalizedSplitUnloggedDetailedGameAfterKeygen
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (kind : EncodingSampleKind) (initialCache : QueryCache HashSpec) :
    OracleComp EncodingSamplingWorld ((Forgery × Bool) × QueryCache HashSpec) := do
  let (forgery, adversaryCache) ←
    (simulateQ
      (cappedNormalizedSplitUnloggedMappedAdversaryImpl publicKey secretKey kind)
      (adversary.main publicKey)).run initialCache
  let (verified, finalCache) ←
    (simulateQ (splitXmssRomImpl secretKey.parameter kind)
      (Concrete.scheme.verify publicKey forgery.epoch forgery.message
        forgery.signature)).run adversaryCache
  pure ((forgery, verified), finalCache)

theorem cappedSplitDetailedGameAfterKeygenWithEncodingTrace_unlogged_projection
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    (fun result : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      ((result.1.forgery, result.1.verified), result.2.1.1)) <$>
        cappedSplitDetailedGameAfterKeygenWithEncodingTrace adversary publicKey secretKey
          initialCache =
      cappedSplitUnloggedDetailedGameAfterKeygen adversary publicKey secretKey
        initialCache := by
  let encodedAdversary :=
    (simulateQ (cappedSplitEncodingTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run ((initialCache, []), [])
  let cacheTracedAdversary :=
    (simulateQ (cappedSplitCacheTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run (initialCache, [])
  let unloggedAdversary :=
    (simulateQ (cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run initialCache
  have hencoding : Prod.map id Prod.fst <$> encodedAdversary =
      cacheTracedAdversary := by
    exact OracleComp.extendState_run_proj_eq
      (cappedSplitCacheTracedMappedAdversaryImpl publicKey secretKey)
      (encodingActionTraceUpdate secretKey) (adversary.main publicKey)
      (initialCache, []) []
  have hsigning : Prod.map id Prod.fst <$> cacheTracedAdversary =
      unloggedAdversary := by
    exact OracleComp.extendState_run_proj_eq
      (cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey)
      signingCacheTraceUpdate (adversary.main publicKey) initialCache []
  have hadversary :
      (fun result => (result.1, result.2.1.1)) <$> encodedAdversary =
        unloggedAdversary := by
    calc
      _ = Prod.map id Prod.fst <$>
          (Prod.map id Prod.fst <$> encodedAdversary) := by
        simp [Functor.map_map, Prod.map]
      _ = Prod.map id Prod.fst <$> cacheTracedAdversary := by rw [hencoding]
      _ = unloggedAdversary := hsigning
  let finish : Forgery × QueryCache HashSpec →
      OracleComp EncodingSamplingWorld ((Forgery × Bool) × QueryCache HashSpec) :=
    fun result => do
      let (verified, finalCache) ←
        (simulateQ (splitXmssRomImpl secretKey.parameter .query)
          (Concrete.scheme.verify publicKey result.1.epoch result.1.message
            result.1.signature)).run result.2
      pure ((result.1, verified), finalCache)
  unfold cappedSplitDetailedGameAfterKeygenWithEncodingTrace
    cappedSplitUnloggedDetailedGameAfterKeygen
  change (fun result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
    ((result.1.forgery, result.1.verified), result.2.1.1)) <$>
      (encodedAdversary >>= fun result => do
        let (verified, finalCache) ←
          (simulateQ (splitXmssRomImpl secretKey.parameter .query)
            (Concrete.scheme.verify publicKey result.1.epoch result.1.message
              result.1.signature)).run result.2.1.1
        let finalEncodingTrace := appendVerificationEncodingObservation secretKey
          result.1 result.2.1.1 finalCache result.2.2
        pure (⟨publicKey, secretKey, result.1, result.2.1.2.toSigningLog,
          verified⟩, ((finalCache, result.2.1.2), finalEncodingTrace))) = _
  simp only [map_bind, map_pure]
  change (encodedAdversary >>= fun result =>
      finish (result.1, result.2.1.1)) =
    unloggedAdversary >>= finish
  rw [← hadversary, bind_map_left]

theorem cappedSplitUnloggedDetailedGameAfterKeygen_normalized_isQueryBoundP_iff
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (kind : EncodingSampleKind) (initialCache : QueryCache HashSpec)
    (fuel : Nat) :
    (cappedSplitUnloggedDetailedGameAfterKeygen adversary publicKey secretKey initialCache
      |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      (cappedNormalizedSplitUnloggedDetailedGameAfterKeygen adversary publicKey secretKey
        kind initialCache |>.IsQueryBoundP (· matches .inr _) fuel) := by
  unfold cappedSplitUnloggedDetailedGameAfterKeygen
    cappedNormalizedSplitUnloggedDetailedGameAfterKeygen
  exact cappedSplitUnloggedMappedAdversary_bind_normalized_isQueryBoundP_iff
    publicKey secretKey kind (adversary.main publicKey) initialCache
      (fun result =>
        (simulateQ (splitXmssRomImpl secretKey.parameter .query)
          (Concrete.scheme.verify publicKey result.1.epoch result.1.message
            result.1.signature)).run result.2 >>= fun verifiedResult =>
              pure ((result.1, verifiedResult.1), verifiedResult.2))
      (fun result =>
        (simulateQ (splitXmssRomImpl secretKey.parameter kind)
          (Concrete.scheme.verify publicKey result.1.epoch result.1.message
            result.1.signature)).run result.2 >>= fun verifiedResult =>
              pure ((result.1, verifiedResult.1), verifiedResult.2))
      (fun result remaining =>
        splitXmssRom_simulateQ_bind_kind_isQueryBoundP_iff
          secretKey.parameter .query kind
          (Concrete.scheme.verify publicKey result.1.epoch result.1.message
            result.1.signature) result.2
          (fun verifiedResult => pure ((result.1, verifiedResult.1), verifiedResult.2))
          (fun verifiedResult => pure ((result.1, verifiedResult.1), verifiedResult.2))
          (fun _ _ => Iff.rfl) remaining)
      fuel

theorem cappedNormalizedSplitUnloggedDetailedGameAfterKeygen_eq_simulation
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (kind : EncodingSampleKind) (initialCache : QueryCache HashSpec) :
    cappedNormalizedSplitUnloggedDetailedGameAfterKeygen adversary publicKey secretKey
        kind initialCache =
      (simulateQ (splitXmssRomImpl secretKey.parameter kind)
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary publicKey secretKey)).run
          initialCache := by
  unfold cappedNormalizedSplitUnloggedDetailedGameAfterKeygen
    cappedSourceUnloggedDetailedGameAfterKeygen
  rw [simulateQ_bind, StateT.run_bind,
    cappedNormalizedSplitUnloggedMappedAdversary_simulateQ_run_eq]
  apply bind_congr
  intro result
  rw [simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro verifiedResult
  simp only [simulateQ_pure, StateT.run_pure]

theorem cappedSplitDetailedGameAfterKeygenWithEncodingTrace_encodingSample_bound
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅)) :
    (cappedSplitDetailedGameAfterKeygenWithEncodingTrace adversary keyResult.1.1
      keyResult.1.2 keyResult.2).IsQueryBoundP (· matches .inr _) q := by
  have hsource := cappedSourceUnloggedDetailedGameAfterKeygen_hashQueryBound
    q adversary hbound keyResult hkeyResult
  have hnormalized := splitXmssRom_encodingSample_bound keyResult.1.2.parameter
    .side (cappedSourceUnloggedDetailedGameAfterKeygen adversary keyResult.1.1
      keyResult.1.2) q hsource keyResult.2
  rw [← cappedNormalizedSplitUnloggedDetailedGameAfterKeygen_eq_simulation] at hnormalized
  have hunlogged :=
    (cappedSplitUnloggedDetailedGameAfterKeygen_normalized_isQueryBoundP_iff
      adversary keyResult.1.1 keyResult.1.2 .side keyResult.2 q).mpr hnormalized
  exact (OracleComp.isQueryBoundP_iff_of_map_eq
    (cappedSplitDetailedGameAfterKeygenWithEncodingTrace_unlogged_projection
      adversary keyResult.1.1 keyResult.1.2 keyResult.2)).mpr hunlogged
