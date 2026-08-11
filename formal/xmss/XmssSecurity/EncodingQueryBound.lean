import XmssSecurity.EncodingTraceBridge

open OracleComp OracleSpec

namespace XmssSecurity

set_option maxRecDepth 100000

theorem isQueryBoundP_lifted_query_bind_iff
    {sourceIndex targetIndex : Type}
    {sourceSpec : OracleSpec sourceIndex} {targetSpec : OracleSpec targetIndex}
    [inclusion : sourceSpec ⊂ₒ targetSpec]
    (input : sourceSpec.Domain)
    (next : sourceSpec.Range input → OracleComp targetSpec α)
    (predicate : targetSpec.Domain → Prop) [DecidablePred predicate]
    (fuel : Nat) :
    ((OracleComp.liftComp
        (liftM (sourceSpec.query input) :
          OracleComp sourceSpec (sourceSpec.Range input)) targetSpec >>= next)
      |>.IsQueryBoundP predicate fuel) ↔
      (¬ predicate (inclusion.onQuery input) ∨ 0 < fuel) ∧
        ∀ response, (next (inclusion.onResponse input response)).IsQueryBoundP
          predicate (if predicate (inclusion.onQuery input) then fuel - 1 else fuel) := by
  rw [show
      OracleComp.liftComp
          (liftM (sourceSpec.query input) :
            OracleComp sourceSpec (sourceSpec.Range input)) targetSpec =
        liftM (targetSpec.query (inclusion.onQuery input)) >>= fun response =>
          pure (inclusion.onResponse input response) by
    rw [OracleComp.liftComp_query]
    simp only [OracleQuery.cont_query]
    change
      ((liftM (sourceSpec.query input) :
        OracleQuery targetSpec (sourceSpec.Range input)) :
          OracleComp targetSpec (sourceSpec.Range input)) = _
    rw [show
        (liftM (sourceSpec.query input) :
          OracleQuery targetSpec (sourceSpec.Range input)) =
            ⟨inclusion.onQuery input, inclusion.onResponse input⟩
      from inclusion.liftM_eq_lift _]
    rfl]
  rw [bind_assoc, OracleComp.isQueryBoundP_query_bind_iff]
  simp only [pure_bind]

theorem isQueryBoundP_bind_congr_right
    {index : Type} {spec : OracleSpec index} {α β : Type}
    (head : OracleComp spec α)
    (leftNext rightNext : α → OracleComp spec β)
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (hnext : ∀ result fuel,
      (leftNext result).IsQueryBoundP predicate fuel ↔
        (rightNext result).IsQueryBoundP predicate fuel)
    (fuel : Nat) :
    (head >>= leftNext).IsQueryBoundP predicate fuel ↔
      (head >>= rightNext).IsQueryBoundP predicate fuel := by
  induction head using OracleComp.inductionOn generalizing fuel with
  | pure result =>
      simpa only [pure_bind] using hnext result fuel
  | query_bind input next ih =>
      rw [bind_assoc, bind_assoc,
        OracleComp.isQueryBoundP_query_bind_iff,
        OracleComp.isQueryBoundP_query_bind_iff]
      constructor
      · rintro ⟨hpositive, hrest⟩
        exact ⟨hpositive, fun response =>
          (ih response (if predicate input then fuel - 1 else fuel)).mp
            (hrest response)⟩
      · rintro ⟨hpositive, hrest⟩
        exact ⟨hpositive, fun response =>
          (ih response (if predicate input then fuel - 1 else fuel)).mpr
            (hrest response)⟩

theorem OracleComp.IsQueryBoundP.bind_right_of_mem_support
    {index : Type} {spec : OracleSpec index} {α β : Type}
    {predicate : spec.Domain → Prop} [DecidablePred predicate]
    {head : OracleComp spec α} {next : α → OracleComp spec β}
    {fuel : Nat}
    (hbound : (head >>= next).IsQueryBoundP predicate fuel)
    (result : α) (hresult : result ∈ support head) :
    (next result).IsQueryBoundP predicate fuel := by
  induction head using OracleComp.inductionOn generalizing fuel result with
  | pure value =>
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      simpa only [pure_bind] using hbound
  | query_bind input rest ih =>
      rw [bind_assoc, OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [mem_support_bind_iff] at hresult
      obtain ⟨response, _hquery, hrest⟩ := hresult
      exact (ih response (hbound.2 response) result hrest).mono (by
        split <;> omega)

theorem splitRandomOracle_kind_isQueryBoundP_iff
    (parameter : PublicParameter) (leftKind rightKind : EncodingSampleKind)
    (input : HashInput) (cache : QueryCache HashSpec) (fuel : Nat) :
    ((splitRandomOracle parameter leftKind input).run cache).IsQueryBoundP
        (· matches .inr _) fuel ↔
      ((splitRandomOracle parameter rightKind input).run cache).IsQueryBoundP
        (· matches .inr _) fuel := by
  unfold splitRandomOracle
  cases hcache : cache input with
  | some output =>
      rw [QueryImpl.withCaching_run_some _ hcache,
        QueryImpl.withCaching_run_some _ hcache]
  | none =>
      rw [QueryImpl.withCaching_run_none _ hcache,
        QueryImpl.withCaching_run_none _ hcache,
        OracleComp.isQueryBoundP_map_iff,
        OracleComp.isQueryBoundP_map_iff]
      unfold freshEncodingSampleImpl encodingSampleAddress
      cases hepoch : encodingInputEpoch? parameter input with
      | none => simp only [encodingSampleAddressFromEpoch]
      | some epoch =>
          simp only [encodingSampleAddressFromEpoch]
          unfold encodingSampleQuery
          rw [OracleComp.liftComp_query, OracleComp.liftComp_query,
            OracleComp.isQueryBoundP_map_iff,
            OracleComp.isQueryBoundP_map_iff]
          cases leftKind <;> cases rightKind <;> rfl

theorem splitRandomOracle_bind_kind_isQueryBoundP_iff
    (parameter : PublicParameter) (leftKind rightKind : EncodingSampleKind)
    (input : HashInput) (cache : QueryCache HashSpec)
    (leftNext rightNext : HashOutput × QueryCache HashSpec →
      OracleComp EncodingSamplingWorld α)
    (hnext : ∀ result fuel,
      (leftNext result).IsQueryBoundP (· matches .inr _) fuel ↔
        (rightNext result).IsQueryBoundP (· matches .inr _) fuel)
    (fuel : Nat) :
    (((splitRandomOracle parameter leftKind input).run cache >>= leftNext)
        |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      (((splitRandomOracle parameter rightKind input).run cache >>= rightNext)
        |>.IsQueryBoundP (· matches .inr _) fuel) := by
  unfold splitRandomOracle
  cases hcache : cache input with
  | some output =>
      rw [QueryImpl.withCaching_run_some _ hcache,
        QueryImpl.withCaching_run_some _ hcache]
      simp only [pure_bind]
      exact hnext (output, cache) fuel
  | none =>
      rw [QueryImpl.withCaching_run_none _ hcache,
        QueryImpl.withCaching_run_none _ hcache]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
      unfold freshEncodingSampleImpl encodingSampleAddress
      cases hepoch : encodingInputEpoch? parameter input with
      | none =>
          simp only [encodingSampleAddressFromEpoch]
          unfold encodingSampleQuery
          rw [isQueryBoundP_lifted_query_bind_iff,
            isQueryBoundP_lifted_query_bind_iff]
          constructor
          · rintro ⟨hpositive, hrest⟩
            exact ⟨hpositive, fun output =>
              (hnext (output, cache.cacheQuery input output) (fuel - 1)).mp
                (hrest output)⟩
          · rintro ⟨hpositive, hrest⟩
            exact ⟨hpositive, fun output =>
              (hnext (output, cache.cacheQuery input output) (fuel - 1)).mpr
                (hrest output)⟩
      | some epoch =>
          simp only [encodingSampleAddressFromEpoch]
          unfold encodingSampleQuery
          rw [isQueryBoundP_lifted_query_bind_iff,
            isQueryBoundP_lifted_query_bind_iff]
          constructor
          · rintro ⟨hpositive, hrest⟩
            exact ⟨hpositive, fun output =>
              (hnext (output, cache.cacheQuery input output) (fuel - 1)).mp
                (hrest output)⟩
          · rintro ⟨hpositive, hrest⟩
            exact ⟨hpositive, fun output =>
              (hnext (output, cache.cacheQuery input output) (fuel - 1)).mpr
                (hrest output)⟩

theorem splitRandomOracle_simulateQ_kind_isQueryBoundP_iff
    (parameter : PublicParameter) (leftKind rightKind : EncodingSampleKind)
    (computation : OracleComp HashSpec α) (cache : QueryCache HashSpec)
    (fuel : Nat) :
    (((simulateQ (splitRandomOracle parameter leftKind) computation).run cache)
        |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      (((simulateQ (splitRandomOracle parameter rightKind) computation).run cache)
        |>.IsQueryBoundP (· matches .inr _) fuel) := by
  induction computation using OracleComp.inductionOn generalizing cache fuel with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind,
        simulateQ_query_bind, StateT.run_bind]
      simp only [OracleQuery.input_query, monadLift_self]
      exact splitRandomOracle_bind_kind_isQueryBoundP_iff parameter leftKind
        rightKind input cache
          (fun result =>
            (simulateQ (splitRandomOracle parameter leftKind) (next result.1)).run
              result.2)
          (fun result =>
            (simulateQ (splitRandomOracle parameter rightKind) (next result.1)).run
              result.2)
          (fun result remaining => ih result.1 result.2 remaining) fuel

theorem splitXmssRom_bind_kind_isQueryBoundP_iff
    (parameter : PublicParameter) (leftKind rightKind : EncodingSampleKind)
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (leftNext rightNext : OracleWorld.Range input × QueryCache HashSpec →
      OracleComp EncodingSamplingWorld α)
    (hnext : ∀ result fuel,
      (leftNext result).IsQueryBoundP (· matches .inr _) fuel ↔
        (rightNext result).IsQueryBoundP (· matches .inr _) fuel)
    (fuel : Nat) :
    (((splitXmssRomImpl parameter leftKind input).run cache >>= leftNext)
        |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      (((splitXmssRomImpl parameter rightKind input).run cache >>= rightNext)
        |>.IsQueryBoundP (· matches .inr _) fuel) := by
  cases input with
  | inl uniformInput =>
      simp only [splitXmssRomImpl, QueryImpl.add_apply_inl]
      exact isQueryBoundP_bind_congr_right
        ((splitUniformOracle uniformInput).run cache) leftNext rightNext
        (· matches .inr _) hnext fuel
  | inr hashInput =>
      simp only [splitXmssRomImpl, QueryImpl.add_apply_inr]
      exact splitRandomOracle_bind_kind_isQueryBoundP_iff parameter leftKind
        rightKind hashInput cache leftNext rightNext hnext fuel

theorem splitXmssRom_simulateQ_kind_isQueryBoundP_iff
    (parameter : PublicParameter) (leftKind rightKind : EncodingSampleKind)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (fuel : Nat) :
    (((simulateQ (splitXmssRomImpl parameter leftKind) computation).run cache)
        |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      (((simulateQ (splitXmssRomImpl parameter rightKind) computation).run cache)
        |>.IsQueryBoundP (· matches .inr _) fuel) := by
  induction computation using OracleComp.inductionOn generalizing cache fuel with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind,
        simulateQ_query_bind, StateT.run_bind]
      simp only [OracleQuery.input_query, monadLift_self]
      exact splitXmssRom_bind_kind_isQueryBoundP_iff parameter leftKind
        rightKind input cache
          (fun result =>
            (simulateQ (splitXmssRomImpl parameter leftKind) (next result.1)).run
              result.2)
          (fun result =>
            (simulateQ (splitXmssRomImpl parameter rightKind) (next result.1)).run
              result.2)
          (fun result remaining => ih result.1 result.2 remaining) fuel

theorem splitXmssRom_simulateQ_bind_kind_isQueryBoundP_iff
    (parameter : PublicParameter) (leftKind rightKind : EncodingSampleKind)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (leftNext rightNext : α × QueryCache HashSpec →
      OracleComp EncodingSamplingWorld β)
    (hnext : ∀ result fuel,
      (leftNext result).IsQueryBoundP (· matches .inr _) fuel ↔
        (rightNext result).IsQueryBoundP (· matches .inr _) fuel)
    (fuel : Nat) :
    ((((simulateQ (splitXmssRomImpl parameter leftKind) computation).run cache) >>=
        leftNext) |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      ((((simulateQ (splitXmssRomImpl parameter rightKind) computation).run cache) >>=
        rightNext) |>.IsQueryBoundP (· matches .inr _) fuel) := by
  induction computation using OracleComp.inductionOn generalizing cache fuel with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact hnext (value, cache) fuel
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, bind_assoc,
        simulateQ_query_bind, StateT.run_bind, bind_assoc]
      simp only [OracleQuery.input_query, monadLift_self]
      exact splitXmssRom_bind_kind_isQueryBoundP_iff parameter leftKind
        rightKind input cache
          (fun result =>
            (simulateQ (splitXmssRomImpl parameter leftKind) (next result.1)).run
              result.2 >>= leftNext)
          (fun result =>
            (simulateQ (splitXmssRomImpl parameter rightKind) (next result.1)).run
              result.2 >>= rightNext)
          (fun result remaining =>
            ih result.1 result.2 remaining) fuel

noncomputable def normalizedSplitUnloggedMappedAdversaryImpl
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

noncomputable def sourceUnloggedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (OracleComp OracleWorld) := by
  intro input
  cases input with
  | inl worldInput => exact liftM (OracleWorld.query worldInput)
  | inr request =>
      exact Concrete.scheme.sign publicKey secretKey request.epoch request.message

theorem normalizedSplitUnloggedMappedAdversaryImpl_eq_compose
    (publicKey : PublicKey) (secretKey : SecretKey)
    (kind : EncodingSampleKind) :
    normalizedSplitUnloggedMappedAdversaryImpl publicKey secretKey kind =
      splitXmssRomImpl secretKey.parameter kind ∘ₛ
        sourceUnloggedMappedAdversaryImpl publicKey secretKey := by
  funext input
  cases input with
  | inl worldInput =>
      simp [normalizedSplitUnloggedMappedAdversaryImpl,
        sourceUnloggedMappedAdversaryImpl]
  | inr request => rfl

theorem normalizedSplitUnloggedMappedAdversary_simulateQ_run_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (kind : EncodingSampleKind)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) :
    (simulateQ (normalizedSplitUnloggedMappedAdversaryImpl publicKey secretKey kind)
        computation).run cache =
      (simulateQ (splitXmssRomImpl secretKey.parameter kind)
        (simulateQ (sourceUnloggedMappedAdversaryImpl publicKey secretKey)
          computation)).run cache := by
  rw [normalizedSplitUnloggedMappedAdversaryImpl_eq_compose,
    QueryImpl.simulateQ_compose]

theorem sourceUnloggedMappedAdversaryImpl_withTraceAppend_eq
    (publicKey : PublicKey) (secretKey : SecretKey) :
    (sourceUnloggedMappedAdversaryImpl publicKey secretKey).withTraceAppend
        signingLogFragment =
      ((HasQuery.toQueryImpl
          (spec := OracleWorld) (m := OracleComp OracleWorld)).liftTarget
            (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
        signingOracle Concrete.scheme publicKey secretKey) := by
  funext input
  cases input with
  | inl worldInput =>
      apply WriterT.ext
      simp [sourceUnloggedMappedAdversaryImpl, signingLogFragment,
        HasQuery.toQueryImpl]
  | inr request =>
      simp [sourceUnloggedMappedAdversaryImpl, signingLogFragment, signingOracle]

noncomputable def sourceUnloggedDetailedGameAfterKeygen
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey) :
    OracleComp OracleWorld (Forgery × Bool) := do
  let forgery ← simulateQ
    (sourceUnloggedMappedAdversaryImpl publicKey secretKey)
    (adversary.main publicKey)
  let verified ← Concrete.scheme.verify publicKey forgery.epoch forgery.message
    forgery.signature
  pure (forgery, verified)

theorem detailedGameAfterKeygen_unlogged_projection
    (adversary : Adversary Concrete.scheme)
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
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅)) :
    (sourceUnloggedDetailedGameAfterKeygen adversary keyResult.1.1 keyResult.1.2)
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
    (detailedGameAfterKeygen_unlogged_projection adversary keyResult.1.1
      keyResult.1.2)).mp hcontinuation

theorem splitUnloggedMappedAdversaryImpl_bind_normalized_isQueryBoundP_iff
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
    (((splitUnloggedMappedAdversaryImpl publicKey secretKey input).run cache >>=
        leftNext) |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      (((normalizedSplitUnloggedMappedAdversaryImpl publicKey secretKey kind input).run
        cache >>= rightNext) |>.IsQueryBoundP (· matches .inr _) fuel) := by
  cases input with
  | inl worldInput =>
      simp only [splitUnloggedMappedAdversaryImpl,
        normalizedSplitUnloggedMappedAdversaryImpl]
      exact splitXmssRom_bind_kind_isQueryBoundP_iff secretKey.parameter .query
        kind worldInput cache leftNext rightNext hnext fuel
  | inr request =>
      simp only [splitUnloggedMappedAdversaryImpl,
        normalizedSplitUnloggedMappedAdversaryImpl]
      exact splitXmssRom_simulateQ_bind_kind_isQueryBoundP_iff
        secretKey.parameter .sign kind
        (Concrete.scheme.sign publicKey secretKey request.epoch request.message)
        cache leftNext rightNext hnext fuel

theorem splitUnloggedMappedAdversary_normalized_isQueryBoundP_iff
    (publicKey : PublicKey) (secretKey : SecretKey)
    (kind : EncodingSampleKind)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (fuel : Nat) :
    (((simulateQ (splitUnloggedMappedAdversaryImpl publicKey secretKey)
        computation).run cache) |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      (((simulateQ (normalizedSplitUnloggedMappedAdversaryImpl publicKey secretKey kind)
        computation).run cache) |>.IsQueryBoundP (· matches .inr _) fuel) := by
  induction computation using OracleComp.inductionOn generalizing cache fuel with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind,
        simulateQ_query_bind, StateT.run_bind]
      simp only [OracleQuery.input_query, monadLift_self]
      exact splitUnloggedMappedAdversaryImpl_bind_normalized_isQueryBoundP_iff
        publicKey secretKey kind input cache
          (fun result =>
            (simulateQ (splitUnloggedMappedAdversaryImpl publicKey secretKey)
              (next result.1)).run result.2)
          (fun result =>
            (simulateQ
              (normalizedSplitUnloggedMappedAdversaryImpl publicKey secretKey kind)
              (next result.1)).run result.2)
          (fun result remaining => ih result.1 result.2 remaining) fuel

theorem splitUnloggedMappedAdversary_bind_normalized_isQueryBoundP_iff
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
    ((((simulateQ (splitUnloggedMappedAdversaryImpl publicKey secretKey)
        computation).run cache) >>= leftNext)
      |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      ((((simulateQ
        (normalizedSplitUnloggedMappedAdversaryImpl publicKey secretKey kind)
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
      exact splitUnloggedMappedAdversaryImpl_bind_normalized_isQueryBoundP_iff
        publicKey secretKey kind input cache
          (fun result =>
            (simulateQ (splitUnloggedMappedAdversaryImpl publicKey secretKey)
              (next result.1)).run result.2 >>= leftNext)
          (fun result =>
            (simulateQ
              (normalizedSplitUnloggedMappedAdversaryImpl publicKey secretKey kind)
              (next result.1)).run result.2 >>= rightNext)
          (fun result remaining => ih result.1 result.2 remaining) fuel

theorem splitEncodingTracedMappedAdversary_isQueryBoundP_iff_unlogged
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialSigningTrace : SigningCacheTrace)
    (initialEncodingTrace : EncodingActionTrace) (fuel : Nat) :
    (((simulateQ (splitEncodingTracedMappedAdversaryImpl publicKey secretKey)
        computation).run ((initialCache, initialSigningTrace), initialEncodingTrace))
      |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      (((simulateQ (splitUnloggedMappedAdversaryImpl publicKey secretKey)
        computation).run initialCache) |>.IsQueryBoundP (· matches .inr _) fuel) := by
  have hencoding := OracleComp.extendState_run_proj_eq
    (splitCacheTracedMappedAdversaryImpl publicKey secretKey)
    (encodingActionTraceUpdate secretKey) computation
    (initialCache, initialSigningTrace) initialEncodingTrace
  have hsigning := OracleComp.extendState_run_proj_eq
    (splitUnloggedMappedAdversaryImpl publicKey secretKey)
    signingCacheTraceUpdate computation initialCache initialSigningTrace
  exact (OracleComp.isQueryBoundP_iff_of_map_eq hencoding).trans
    (OracleComp.isQueryBoundP_iff_of_map_eq hsigning)

noncomputable def splitUnloggedDetailedGameAfterKeygen
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    OracleComp EncodingSamplingWorld ((Forgery × Bool) × QueryCache HashSpec) := do
  let (forgery, adversaryCache) ←
    (simulateQ (splitUnloggedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run initialCache
  let (verified, finalCache) ←
    (simulateQ (splitXmssRomImpl secretKey.parameter .query)
      (Concrete.scheme.verify publicKey forgery.epoch forgery.message
        forgery.signature)).run adversaryCache
  pure ((forgery, verified), finalCache)

noncomputable def normalizedSplitUnloggedDetailedGameAfterKeygen
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (kind : EncodingSampleKind) (initialCache : QueryCache HashSpec) :
    OracleComp EncodingSamplingWorld ((Forgery × Bool) × QueryCache HashSpec) := do
  let (forgery, adversaryCache) ←
    (simulateQ
      (normalizedSplitUnloggedMappedAdversaryImpl publicKey secretKey kind)
      (adversary.main publicKey)).run initialCache
  let (verified, finalCache) ←
    (simulateQ (splitXmssRomImpl secretKey.parameter kind)
      (Concrete.scheme.verify publicKey forgery.epoch forgery.message
        forgery.signature)).run adversaryCache
  pure ((forgery, verified), finalCache)

theorem splitDetailedGameAfterKeygenWithEncodingTrace_unlogged_projection
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    (fun result : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      ((result.1.forgery, result.1.verified), result.2.1.1)) <$>
        splitDetailedGameAfterKeygenWithEncodingTrace adversary publicKey secretKey
          initialCache =
      splitUnloggedDetailedGameAfterKeygen adversary publicKey secretKey
        initialCache := by
  let encodedAdversary :=
    (simulateQ (splitEncodingTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run ((initialCache, []), [])
  let cacheTracedAdversary :=
    (simulateQ (splitCacheTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run (initialCache, [])
  let unloggedAdversary :=
    (simulateQ (splitUnloggedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run initialCache
  have hencoding : Prod.map id Prod.fst <$> encodedAdversary =
      cacheTracedAdversary := by
    exact OracleComp.extendState_run_proj_eq
      (splitCacheTracedMappedAdversaryImpl publicKey secretKey)
      (encodingActionTraceUpdate secretKey) (adversary.main publicKey)
      (initialCache, []) []
  have hsigning : Prod.map id Prod.fst <$> cacheTracedAdversary =
      unloggedAdversary := by
    exact OracleComp.extendState_run_proj_eq
      (splitUnloggedMappedAdversaryImpl publicKey secretKey)
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
  unfold splitDetailedGameAfterKeygenWithEncodingTrace
    splitUnloggedDetailedGameAfterKeygen
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

theorem splitUnloggedDetailedGameAfterKeygen_normalized_isQueryBoundP_iff
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (kind : EncodingSampleKind) (initialCache : QueryCache HashSpec)
    (fuel : Nat) :
    (splitUnloggedDetailedGameAfterKeygen adversary publicKey secretKey initialCache
      |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      (normalizedSplitUnloggedDetailedGameAfterKeygen adversary publicKey secretKey
        kind initialCache |>.IsQueryBoundP (· matches .inr _) fuel) := by
  unfold splitUnloggedDetailedGameAfterKeygen
    normalizedSplitUnloggedDetailedGameAfterKeygen
  exact splitUnloggedMappedAdversary_bind_normalized_isQueryBoundP_iff
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

theorem normalizedSplitUnloggedDetailedGameAfterKeygen_eq_simulation
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (kind : EncodingSampleKind) (initialCache : QueryCache HashSpec) :
    normalizedSplitUnloggedDetailedGameAfterKeygen adversary publicKey secretKey
        kind initialCache =
      (simulateQ (splitXmssRomImpl secretKey.parameter kind)
        (sourceUnloggedDetailedGameAfterKeygen adversary publicKey secretKey)).run
          initialCache := by
  unfold normalizedSplitUnloggedDetailedGameAfterKeygen
    sourceUnloggedDetailedGameAfterKeygen
  rw [simulateQ_bind, StateT.run_bind,
    normalizedSplitUnloggedMappedAdversary_simulateQ_run_eq]
  apply bind_congr
  intro result
  rw [simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro verifiedResult
  simp only [simulateQ_pure, StateT.run_pure]

theorem splitDetailedGameAfterKeygenWithEncodingTrace_encodingSample_bound
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅)) :
    (splitDetailedGameAfterKeygenWithEncodingTrace adversary keyResult.1.1
      keyResult.1.2 keyResult.2).IsQueryBoundP (· matches .inr _) q := by
  have hsource := sourceUnloggedDetailedGameAfterKeygen_hashQueryBound
    q adversary hbound keyResult hkeyResult
  have hnormalized := splitXmssRom_encodingSample_bound keyResult.1.2.parameter
    .side (sourceUnloggedDetailedGameAfterKeygen adversary keyResult.1.1
      keyResult.1.2) q hsource keyResult.2
  rw [← normalizedSplitUnloggedDetailedGameAfterKeygen_eq_simulation] at hnormalized
  have hunlogged :=
    (splitUnloggedDetailedGameAfterKeygen_normalized_isQueryBoundP_iff
      adversary keyResult.1.1 keyResult.1.2 .side keyResult.2 q).mpr hnormalized
  exact (OracleComp.isQueryBoundP_iff_of_map_eq
    (splitDetailedGameAfterKeygenWithEncodingTrace_unlogged_projection
      adversary keyResult.1.1 keyResult.1.2 keyResult.2)).mpr hunlogged

end XmssSecurity
