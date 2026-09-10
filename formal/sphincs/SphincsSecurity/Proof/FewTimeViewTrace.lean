import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeSignerView
import SphincsSecurity.Proof.FewTimeTrace
import SphincsSecurity.Proof.FullTrace
import SphincsSecurity.Proof.MessagePrehit

/-!
# Full adversary trace with signer views

The viewed trace augments the existing full cache trace with one optional digest view per signing
invocation. Its projection is exactly the existing trace, so all deterministic source and cache
invariants remain available unchanged.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

theorem randomOracle_output_cached (input : HashInput)
    (initialCache finalCache : QueryCache HashSpec) (output : HashOutput)
    (hmem : (output, finalCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (Concrete.oracleHash input)).run initialCache)) :
    finalCache input = some output := by
  have hquery : simulateQ (randomOracle : QueryImpl HashSpec _)
      (Concrete.oracleHash input) = randomOracle input := by
    change simulateQ (randomOracle : QueryImpl HashSpec _)
      (liftM (HashSpec.query input)) = _
    exact simulateQ_spec_query
      (impl := (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp))) input
  rw [hquery] at hmem
  cases hcache : initialCache input with
  | none =>
      rw [OracleSpec.randomOracle,
        QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map] at hmem
      obtain ⟨sampledOutput, _, heq⟩ := hmem
      obtain ⟨rfl, rfl⟩ := heq
      exact QueryCache.cacheQuery_self initialCache input output
  | some cachedOutput =>
      rw [OracleSpec.randomOracle,
        QueryImpl.withCaching_run_some uniformSampleImpl hcache,
        support_pure, Set.mem_singleton_iff] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact hcache

structure ViewedFullTraceState where
  cache : QueryCache HashSpec
  trace : FullAdversaryTrace
  views : List (Option Concrete.FewTimeView)
  targetView : Option Concrete.FewTimeView

def ViewedFullTraceState.base (state : ViewedFullTraceState) :
    QueryCache HashSpec × FullAdversaryTrace :=
  (state.cache, state.trace)

def SigningCacheEntry.ValidView (secretKey : SecretKey) (entry : SigningCacheEntry)
    (view : Option Concrete.FewTimeView) : Prop :=
  ((entry.signature, view), entry.finalCache) ∈ support
    ((simulateQ romImpl (Concrete.signWithView secretKey entry.request)).run entry.initialCache)

def ViewedFullTraceState.ValidViews (secretKey : SecretKey)
    (state : ViewedFullTraceState) : Prop :=
  List.Forall₂ (SigningCacheEntry.ValidView secretKey) state.trace.signing state.views

theorem ViewedFullTraceState.ValidViews.length_eq {secretKey : SecretKey}
    {state : ViewedFullTraceState} (hvalid : state.ValidViews secretKey) :
    state.trace.signing.length = state.views.length :=
  List.Forall₂.length_eq hvalid

noncomputable def ViewedFullTraceState.ValidViews.signingViews {secretKey : SecretKey}
    {state : ViewedFullTraceState} (hvalid : state.ValidViews secretKey) :
    Fin state.trace.signing.length → Concrete.FewTimeView :=
  fun position =>
    (state.views.get ⟨position.val, by rw [← hvalid.length_eq]; exact position.isLt⟩).getD default

noncomputable def ViewedFullTraceState.ValidViews.signingOptionViews {secretKey : SecretKey}
    {state : ViewedFullTraceState} (hvalid : state.ValidViews secretKey) :
    Fin state.trace.signing.length → Option Concrete.FewTimeView :=
  fun position =>
    state.views.get ⟨position.val, by rw [← hvalid.length_eq]; exact position.isLt⟩

theorem ViewedFullTraceState.ValidViews.successful_get {secretKey : SecretKey}
    {state : ViewedFullTraceState} (hvalid : state.ValidViews secretKey)
    (position : Fin state.trace.signing.length) (signature : Signature)
    (hresponse : (state.trace.signing.get position).signature = some signature) :
    ∃ (viewPosition : Fin state.views.length) (randomness : Randomness) (index : Index)
        (leaves : DigestTree → FtsLeaf) (loopCache : QueryCache HashSpec),
      viewPosition.val = position.val
        ∧ (some (randomness, index, leaves), loopCache) ∈ support
          ((simulateQ romImpl (Concrete.signDigestLoop digestAttemptLimit secretKey
            (state.trace.signing.get position).request)).run
              (state.trace.signing.get position).initialCache)
        ∧ (some signature, (state.trace.signing.get position).finalCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec
            (StateT (QueryCache HashSpec) ProbComp))
            (Concrete.signAfterDigest secretKey randomness index leaves)).run loopCache)
        ∧ state.views.get viewPosition =
          some (Concrete.selectedFewTimeView index leaves) := by
  let viewPosition : Fin state.views.length :=
    ⟨position.val, by rw [← hvalid.length_eq]; exact position.isLt⟩
  have hviewRun := hvalid.get position.isLt viewPosition.isLt
  change (((state.trace.signing.get position).signature, state.views.get viewPosition),
      (state.trace.signing.get position).finalCache) ∈ support
    ((simulateQ romImpl (Concrete.signWithView secretKey
      (state.trace.signing.get position).request)).run
        (state.trace.signing.get position).initialCache) at hviewRun
  rw [hresponse] at hviewRun
  obtain ⟨randomness, index, leaves, loopCache, hloop, hfinish, hview⟩ :=
    Concrete.signWithView_support_some secretKey
      (state.trace.signing.get position).request
      (state.trace.signing.get position).initialCache
      (state.trace.signing.get position).finalCache signature
      (state.views.get viewPosition) hviewRun
  exact ⟨viewPosition, randomness, index, leaves, loopCache, rfl,
    hloop, hfinish, hview⟩

theorem ViewedFullTraceState.ValidViews.successful_get_eq_honest_view
    {f : QueryImpl HashSpec Id} {secretKey : SecretKey} {state : ViewedFullTraceState}
    {finalCache : QueryCache HashSpec} (hvalid : state.ValidViews secretKey)
    (position : Fin state.trace.signing.length) (signature : Signature)
    (hresponse : (state.trace.signing.get position).signature = some signature)
    (hle : (state.trace.signing.get position).finalCache ≤ finalCache)
    (hf : finalCache.AgreesWithFn f) (index : Index) (leaves : DigestTree → FtsLeaf)
    (hhonest : Concrete.HonestFtsSignAt f finalCache secretKey
      (state.trace.signing.get position).request signature index leaves) :
    ∃ viewPosition : Fin state.views.length,
      viewPosition.val = position.val
        ∧ state.views.get viewPosition =
          some (Concrete.selectedFewTimeView index leaves) := by
  obtain ⟨viewPosition, randomness, actualIndex, actualLeaves, loopCache, hposition,
      hloop, hfinish, hview⟩ := hvalid.successful_get position signature hresponse
  have hrandomness : signature.randomness = randomness :=
    Concrete.signAfterDigest_support_some_randomness secretKey randomness actualIndex actualLeaves
      loopCache (state.trace.signing.get position).finalCache signature hfinish
  have hloopLeEntry : loopCache ≤ (state.trace.signing.get position).finalCache :=
    simulateQ_romImpl_cache_le
      (liftM (Concrete.signAfterDigest secretKey randomness actualIndex actualLeaves) :
        OracleComp OracleWorld (Option Signature)) loopCache
      (some signature, (state.trace.signing.get position).finalCache)
      (by simpa only [simulateQ_romImpl_liftM] using hfinish)
  have hloopLeFinal : loopCache ≤ finalCache := hloopLeEntry.trans hle
  have hloopAgree : loopCache.AgreesWithFn f :=
    fun _ _ hcached => hf (hloopLeFinal hcached)
  have hloopReplay := replayRom_of_mem_support
    (Concrete.signDigestLoop digestAttemptLimit secretKey
      (state.trace.signing.get position).request)
    (state.trace.signing.get position).initialCache
    (some (randomness, actualIndex, actualLeaves)) loopCache hloop f hloopAgree
  have hdigest := Concrete.successfulDigestLoop_of_mem_support f secretKey
    (state.trace.signing.get position).request digestAttemptLimit randomness actualIndex
    actualLeaves (state.trace.signing.get position).initialCache loopCache finalCache
    hloopReplay hloopLeFinal hf
  rw [← hrandomness] at hdigest
  have hpairs : (actualIndex, actualLeaves) = (index, leaves) :=
    Option.some.inj (hdigest.2.1.symm.trans hhonest.1.2.1)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpairs
  exact ⟨viewPosition, hposition, hview⟩

theorem ViewedFullTraceState.ValidViews.signingOptionViews_eq_honest_view
    {f : QueryImpl HashSpec Id} {secretKey : SecretKey} {state : ViewedFullTraceState}
    {finalCache : QueryCache HashSpec} (hvalid : state.ValidViews secretKey)
    (position : Fin state.trace.signing.length) (signature : Signature)
    (hresponse : (state.trace.signing.get position).signature = some signature)
    (hle : (state.trace.signing.get position).finalCache ≤ finalCache)
    (hf : finalCache.AgreesWithFn f) (index : Index) (leaves : DigestTree → FtsLeaf)
    (hhonest : Concrete.HonestFtsSignAt f finalCache secretKey
      (state.trace.signing.get position).request signature index leaves) :
    hvalid.signingOptionViews position =
      some (Concrete.selectedFewTimeView index leaves) := by
  obtain ⟨viewPosition, hposition, hview⟩ :=
    hvalid.successful_get_eq_honest_view position signature hresponse hle hf index leaves hhonest
  unfold ViewedFullTraceState.ValidViews.signingOptionViews
  have heq : (⟨position.val, by rw [← hvalid.length_eq]; exact position.isLt⟩ :
      Fin state.views.length) = viewPosition := Fin.ext hposition.symm
  rw [heq]
  exact hview

private theorem forall₂_append_singleton {R : α → β → Prop}
    {left : List α} {right : List β} {a : α} {b : β}
    (h : List.Forall₂ R left right) (hab : R a b) :
    List.Forall₂ R (left ++ [a]) (right ++ [b]) := by
  induction left generalizing right with
  | nil =>
      cases h
      exact .cons hab .nil
  | cons head tail ih =>
      cases h with
      | cons hhead htail => exact .cons hhead (ih htail)

noncomputable def viewedFullTracedMappedAdversaryImpl (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT ViewedFullTraceState ProbComp) := by
  intro input
  cases input with
  | inl worldInput =>
      exact fun state => do
        let (output, finalCache) ← (romImpl worldInput).run state.cache
        let trace := fullAdversaryTraceUpdate (.inl worldInput) state.cache output
          finalCache state.trace
        pure (output, ⟨finalCache, trace, state.views, state.targetView⟩)
  | inr request =>
      exact fun state => do
        let ((signature, view), finalCache) ←
          (simulateQ romImpl (Concrete.signWithView secretKey request)).run state.cache
        let trace := fullAdversaryTraceUpdate (.inr request) state.cache signature
          finalCache state.trace
        pure (signature, ⟨finalCache, trace, state.views ++ [view], state.targetView⟩)

theorem viewedFullTracedMappedAdversaryImpl_query_validViews
    (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : ViewedFullTraceState)
    (result : (OracleWorld + SigningSpec).Range input × ViewedFullTraceState)
    (hvalid : state.ValidViews secretKey)
    (hmem : result ∈ support
      ((viewedFullTracedMappedAdversaryImpl secretKey input).run state)) :
    result.2.ValidViews secretKey := by
  cases input with
  | inl worldInput =>
      rw [viewedFullTracedMappedAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, finalCache⟩, hquery, hpure⟩ := hmem
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      simpa [ViewedFullTraceState.ValidViews, fullAdversaryTraceUpdate,
        signingCacheTraceUpdate] using hvalid
  | inr request =>
      rw [viewedFullTracedMappedAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨signature, view⟩, finalCache⟩, hquery, hpure⟩ := hmem
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      apply forall₂_append_singleton hvalid
      exact hquery

theorem viewedFullTracedMappedAdversaryImpl_validViews
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : ViewedFullTraceState)
    (result : α × ViewedFullTraceState)
    (hvalid : initialState.ValidViews secretKey)
    (hmem : result ∈ support
      ((simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run initialState)) :
    result.2.ValidViews secretKey := by
  exact OracleComp.simulateQ_run_preservesInv
    (viewedFullTracedMappedAdversaryImpl secretKey)
    (ViewedFullTraceState.ValidViews secretKey)
    (by
      intro input state hstate queryResult hquery
      exact viewedFullTracedMappedAdversaryImpl_query_validViews secretKey input state
        queryResult hstate hquery)
    computation initialState hvalid result hmem

theorem viewedFullTracedMappedAdversaryImpl_query_projection
    (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : ViewedFullTraceState) :
    (fun result => (result.1, result.2.base)) <$>
        ((viewedFullTracedMappedAdversaryImpl secretKey input).run state) =
      (fullTracedMappedAdversaryImpl secretKey input).run state.base := by
  cases input with
  | inl worldInput =>
      rw [viewedFullTracedMappedAdversaryImpl, fullTracedMappedAdversaryImpl,
        QueryImpl.extendState_apply, unloggedMappedAdversaryImpl]
      simp only [map_eq_bind_pure_comp, ViewedFullTraceState.base]
      unfold StateT.run
      simp only [Function.comp_apply, bind_assoc, pure_bind]
      change (romImpl worldInput state.cache >>= fun result =>
          pure (result.1, (result.2, fullAdversaryTraceUpdate (.inl worldInput)
            state.cache result.1 result.2 state.trace))) =
        (romImpl worldInput state.cache >>= fun result =>
          pure (result.1, (result.2, fullAdversaryTraceUpdate (.inl worldInput)
            state.cache result.1 result.2 state.trace)))
      rfl
  | inr request =>
      rw [viewedFullTracedMappedAdversaryImpl, fullTracedMappedAdversaryImpl,
        QueryImpl.extendState_apply, unloggedMappedAdversaryImpl]
      simp only [map_eq_bind_pure_comp, ViewedFullTraceState.base]
      unfold StateT.run
      simp only [Function.comp_apply, bind_assoc, pure_bind]
      change (simulateQ romImpl (Concrete.signWithView secretKey request) state.cache >>=
          fun result => pure (result.1.1,
            (result.2, fullAdversaryTraceUpdate (.inr request) state.cache result.1.1
              result.2 state.trace))) =
        (simulateQ romImpl (Concrete.scheme.sign secretKey request) state.cache >>=
          fun result => pure (result.1,
            (result.2, fullAdversaryTraceUpdate (.inr request) state.cache result.1
              result.2 state.trace)))
      have hrun := Concrete.simulateQ_signWithView_fst_run secretKey request state.cache
      change (fun result => (result.1.1, result.2)) <$>
          simulateQ romImpl (Concrete.signWithView secretKey request) state.cache =
        simulateQ romImpl (Concrete.sign secretKey request) state.cache at hrun
      rw [show Concrete.scheme.sign secretKey request = Concrete.sign secretKey request from rfl]
      rw [← hrun]
      simp [map_eq_bind_pure_comp, bind_assoc]

theorem viewedFullTracedMappedAdversaryImpl_projection
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : ViewedFullTraceState) :
    Prod.map id ViewedFullTraceState.base <$>
        (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
          computation).run initialState =
      (simulateQ (fullTracedMappedAdversaryImpl secretKey)
        computation).run initialState.base := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (viewedFullTracedMappedAdversaryImpl secretKey)
    (fullTracedMappedAdversaryImpl secretKey)
    ViewedFullTraceState.base
  intro input state
  exact viewedFullTracedMappedAdversaryImpl_query_projection secretKey input state

noncomputable def gameRestWithViewTrace (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (initialCache : QueryCache HashSpec) :
    ProbComp ((Forgery × Bool) × ViewedFullTraceState) := do
  let (forgery, state) ←
    (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
      (adversary.main publicKey)).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩
  let ((verified, targetView), finalCache) ←
    (simulateQ romImpl
      (liftM (Concrete.verifyWithView publicKey forgery.message forgery.signature) :
        OracleComp OracleWorld (Bool × Concrete.FewTimeView))).run state.cache
  let log := state.trace.signing.toSigningLog
  let verdict := decide (SigningTranscript.Valid log ∧
    ¬ SigningTranscript.Contains log forgery) && verified
  pure ((forgery, verdict), ⟨finalCache, state.trace, state.views, some targetView⟩)

theorem gameRestWithViewTrace_support_validViews (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (initialCache : QueryCache HashSpec)
    (result : (Forgery × Bool) × ViewedFullTraceState)
    (hmem : result ∈ support
      (gameRestWithViewTrace adversary publicKey secretKey initialCache)) :
    result.2.ValidViews secretKey := by
  rw [gameRestWithViewTrace, mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, state⟩, hadversary, hfinish⟩ := hmem
  rw [mem_support_bind_iff] at hfinish
  obtain ⟨⟨verified, finalCache⟩, _, hpure⟩ := hfinish
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact viewedFullTracedMappedAdversaryImpl_validViews secretKey
    (adversary.main publicKey) ⟨initialCache, ⟨[], [], []⟩, [], none⟩
    (forgery, state) (by simp [ViewedFullTraceState.ValidViews]) hadversary

theorem gameRestWithViewTrace_projection (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (initialCache : QueryCache HashSpec) :
    (fun result => (result.1, result.2.base)) <$>
        gameRestWithViewTrace adversary publicKey secretKey initialCache =
      gameRestWithFullTrace adversary publicKey secretKey initialCache := by
  let initialState : ViewedFullTraceState := ⟨initialCache, ⟨[], [], []⟩, [], none⟩
  let viewedRun := (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
    (adversary.main publicKey)).run initialState
  let baseRun := (simulateQ (fullTracedMappedAdversaryImpl secretKey)
    (adversary.main publicKey)).run initialState.base
  have hprojection : Prod.map id ViewedFullTraceState.base <$> viewedRun = baseRun :=
    viewedFullTracedMappedAdversaryImpl_projection secretKey
      (adversary.main publicKey) initialState
  let finishBase : Forgery × (QueryCache HashSpec × FullAdversaryTrace) →
      ProbComp ((Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace)) :=
    fun result => do
      let (verified, finalCache) ←
        (simulateQ romImpl
          (Concrete.scheme.verify publicKey result.1.message result.1.signature)).run result.2.1
      let log := result.2.2.signing.toSigningLog
      let verdict := decide (SigningTranscript.Valid log ∧
        ¬ SigningTranscript.Contains log result.1) && verified
      pure ((result.1, verdict), (finalCache, result.2.2))
  calc
    (fun result => (result.1, result.2.base)) <$>
        gameRestWithViewTrace adversary publicKey secretKey initialCache =
      (Prod.map id ViewedFullTraceState.base <$> viewedRun) >>= finishBase := by
        simp [gameRestWithViewTrace, viewedRun, finishBase, initialState,
          map_eq_bind_pure_comp, bind_assoc, ViewedFullTraceState.base]
        apply bind_congr
        intro result
        rw [← Concrete.simulateQ_verifyWithView_fst_run publicKey result.1.message
          result.1.signature result.2.cache]
        simp [map_eq_bind_pure_comp, bind_assoc]
        rfl
    _ = baseRun >>= finishBase := by rw [hprojection]
    _ = gameRestWithFullTrace adversary publicKey secretKey initialCache := by
      simp [gameRestWithFullTrace, baseRun, finishBase, initialState,
        ViewedFullTraceState.base]

namespace Concrete

noncomputable def FewTimeCover.traceIndex {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (entry : cover.entries) : Fin trace.length :=
  ⟨(cover.logIndex entry).val, by
    have hlength := congrArg List.length hlog
    simpa only [SigningCacheTrace.toSigningLog, List.length_map] using
      (show (cover.logIndex entry).val < trace.toSigningLog.length by
        rw [hlength]
        exact (cover.logIndex entry).isLt)⟩

theorem FewTimeCover.get_traceIndex {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (entry : cover.entries) :
    trace.get (cover.traceIndex trace hlog entry) = cover.cacheEntry trace hlog entry := by
  rfl

theorem FewTimeCover.signingOptionViews_traceIndex_eq_entryView
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (state : ViewedFullTraceState) (hlog : state.trace.signing.toSigningLog = signingLog)
    (hvalid : state.ValidViews secretKey)
    (hcaches : state.trace.signing.CachesLe cache) (hf : cache.AgreesWithFn f)
    (entry : cover.entries) :
    hvalid.signingOptionViews (cover.traceIndex state.trace.signing hlog entry) =
      some (cover.entryView entry) := by
  let selected := cover.select (cover.representativeTree entry)
  let position := cover.traceIndex state.trace.signing hlog entry
  have hget : state.trace.signing.get position = cover.cacheEntry state.trace.signing hlog entry :=
    cover.get_traceIndex state.trace.signing hlog entry
  have hfields := cover.cacheEntry_request_signature state.trace.signing hlog entry
  have hresponse : (state.trace.signing.get position).signature = some selected.signature := by
    rw [hget]
    exact hfields.2
  have hrequest : (state.trace.signing.get position).request = selected.entry.1 := by
    rw [hget]
    exact hfields.1
  have hle : (state.trace.signing.get position).finalCache ≤ cache := by
    rw [hget]
    exact (cover.cacheEntry_cachesLe state.trace.signing hlog hcaches entry).2
  have hhonest : HonestFtsSignAt f cache secretKey
      (state.trace.signing.get position).request selected.signature index
        selected.signedLeaves := by
    rw [hrequest]
    exact selected.honest
  rw [hvalid.signingOptionViews_eq_honest_view position selected.signature hresponse hle hf
    index selected.signedLeaves hhonest]
  congr 1
  apply Prod.ext
  · exact (cover.entryDigest_spec entry).2.2.1
  · funext tree
    exact congrFun (cover.entryDigest_spec entry).2.2.2 (ftsIndexOf tree)

noncomputable def gameAfterSecretsWithViewTrace (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ProbComp ((Digest × Forgery × Bool) × ViewedFullTraceState) := do
  let (root, rootCache) ← (simulateQ romImpl
    (liftM ((treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) :
      OracleComp HashSpec Digest)) : OracleComp OracleWorld Digest)).run ∅
  let result ← gameRestWithViewTrace adversary ⟨root, parameter⟩
    ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache
  pure ((root, result.1.1, result.1.2), result.2)

theorem gameAfterSecretsWithViewTrace_projection (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (fun result => (result.1, result.2.base)) <$>
        gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret =
      gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret := by
  rw [gameAfterSecretsWithViewTrace, gameAfterSecretsWithFullTrace]
  simp only [map_bind]
  apply bind_congr
  intro rootResult
  rw [← gameRestWithViewTrace_projection adversary
    (⟨rootResult.1, parameter⟩ : PublicKey)
    (⟨parameter, rootResult.1, otsSecret, ftsSecret⟩ : SecretKey) rootResult.2]
  simp

theorem gameAfterSecretsWithViewTrace_support_validViews (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hmem : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret)) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    result.2.ValidViews secretKey := by
  rw [gameAfterSecretsWithViewTrace, mem_support_bind_iff] at hmem
  obtain ⟨⟨root, rootCache⟩, _, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨restResult, hrest, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  simpa using gameRestWithViewTrace_support_validViews adversary
    (⟨root, parameter⟩ : PublicKey)
    (⟨parameter, root, otsSecret, ftsSecret⟩ : SecretKey) rootCache restResult hrest

end Concrete

end SphincsSecurity
