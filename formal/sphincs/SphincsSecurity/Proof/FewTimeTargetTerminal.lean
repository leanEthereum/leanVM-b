import SphincsSecurity.Proof.FewTimeTargetInvariant
import SphincsSecurity.Proof.FewTimeTargetView
import SphincsSecurity.Proof.FewTimeOriginLift

/-!
# Terminal alignment for one adaptive few-time target

The filtered chronological candidate count is exactly the ordinal consumed by the target monitor.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

theorem originTargetMonitoredAdversaryImpl_viewed_projection
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration) :
    (fun result => (result.1, result.2.origin.viewed)) <$>
        (simulateQ
          (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState =
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run initialState.origin.viewed := by
  calc
    _ = Prod.map id OriginMonitorState.viewed <$>
        (Prod.map id OriginTargetMonitorState.origin <$>
          (simulateQ
            (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
            computation).run initialState) := by
      simp only [map_eq_bind_pure_comp, bind_assoc]
      apply bind_congr
      intro result
      rfl
    _ = Prod.map id OriginMonitorState.viewed <$>
        (simulateQ (originMonitoredAdversaryImpl configuration secretKey)
          computation).run initialState.origin := by
      rw [originTargetMonitoredAdversaryImpl_projection]
    _ = _ := originMonitoredAdversaryImpl_projection configuration secretKey
      computation initialState.origin

theorem exists_originTargetMonitored_of_viewed_support
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (result : α × ViewedFullTraceState)
    (hmem : result ∈ support
      ((simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run initialState.origin.viewed)) :
    ∃ monitored ∈ support
        ((simulateQ
          (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState),
      monitored.1 = result.1 ∧ monitored.2.origin.viewed = result.2 := by
  rw [← originTargetMonitoredAdversaryImpl_viewed_projection configuration secretKey
    targetOrdinal computation initialState, support_map] at hmem
  obtain ⟨monitored, hmonitored, heq⟩ := hmem
  refine ⟨monitored, hmonitored, ?_⟩
  exact Prod.mk.inj heq

theorem probEvent_viewed_le_originTargetMonitoredAdversaryImpl
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (viewedEvent : α × ViewedFullTraceState → Prop)
    (monitoredEvent : α × OriginTargetMonitorState configuration → Prop)
    (himp : ∀ result ∈ support
      ((simulateQ
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState),
      viewedEvent (result.1, result.2.origin.viewed) → monitoredEvent result) :
    Pr[viewedEvent |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run initialState.origin.viewed] ≤
      Pr[monitoredEvent |
        (simulateQ
          (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
          computation).run initialState] := by
  classical
  rw [← originTargetMonitoredAdversaryImpl_viewed_projection configuration secretKey
    targetOrdinal computation initialState, probEvent_map]
  exact probEvent_mono himp

theorem gameAfterSecretsWithViewTrace_support_adversary_state
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hmem : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret)) :
    ∃ (rootCache : QueryCache HashSpec) (state : ViewedFullTraceState),
      (result.1.1, rootCache) ∈ support
        ((simulateQ romImpl
          (liftM ((treeRoot parameter topLayer rootTree
            (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
              OracleComp OracleWorld Digest)).run ∅)
        ∧ (result.1.2.1, state) ∈ support
          ((simulateQ
            (viewedFullTracedMappedAdversaryImpl
              ⟨parameter, result.1.1, otsSecret, ftsSecret⟩)
            (adversary.main ⟨result.1.1, parameter⟩)).run
              ⟨rootCache, ⟨[], [], []⟩, [], none⟩)
        ∧ result.2.trace = state.trace
        ∧ result.2.views = state.views
        ∧ state.cache ≤ result.2.cache := by
  rw [gameAfterSecretsWithViewTrace, mem_support_bind_iff] at hmem
  obtain ⟨⟨root, rootCache⟩, hroot, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨restResult, hrest, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  rw [gameRestWithViewTrace, mem_support_bind_iff] at hrest
  obtain ⟨⟨forgery, state⟩, hadversary, hfinish⟩ := hrest
  rw [mem_support_bind_iff] at hfinish
  obtain ⟨⟨⟨verified, targetView⟩, finalCache⟩, hverify, hpure⟩ := hfinish
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst restResult
  refine ⟨rootCache, state, hroot, hadversary, rfl, rfl, ?_⟩
  exact simulateQ_romImpl_cache_le
    (liftM (verifyWithView (⟨root, parameter⟩ : PublicKey)
      forgery.message forgery.signature) :
        OracleComp OracleWorld (Bool × FewTimeView))
    state.cache ((verified, targetView), finalCache) hverify

theorem gameAfterSecretsWithViewTrace_support_target_monitored_state
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (targetOrdinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hmem : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret)) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    ∃ (rootCache : QueryCache HashSpec)
        (monitored : Forgery × OriginTargetMonitorState configuration),
      (result.1.1, rootCache) ∈ support
        ((simulateQ romImpl
          (liftM ((treeRoot parameter topLayer rootTree
            (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
              OracleComp OracleWorld Digest)).run ∅)
        ∧ monitored ∈ support
          ((simulateQ
            (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
            (adversary.main ⟨result.1.1, parameter⟩)).run
              (OriginTargetMonitorState.initial configuration rootCache))
        ∧ monitored.1 = result.1.2.1
        ∧ result.2.trace = monitored.2.origin.viewed.trace
        ∧ result.2.views = monitored.2.origin.viewed.views
        ∧ monitored.2.origin.viewed.cache ≤ result.2.cache := by
  let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
  obtain ⟨rootCache, state, hroot, hadversary, htrace, hviews, hcache⟩ :=
    gameAfterSecretsWithViewTrace_support_adversary_state adversary parameter otsSecret
      ftsSecret result hmem
  have hadversary' : (result.1.2.1, state) ∈ support
      ((simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        (adversary.main ⟨result.1.1, parameter⟩)).run
          (OriginTargetMonitorState.initial configuration rootCache).origin.viewed) := by
    simpa only [secretKey, OriginTargetMonitorState.initial,
      OriginMonitorState.initial] using hadversary
  obtain ⟨monitored, hmonitored, hforgery, hstate⟩ :=
    exists_originTargetMonitored_of_viewed_support configuration secretKey targetOrdinal
      (adversary.main ⟨result.1.1, parameter⟩)
      (OriginTargetMonitorState.initial configuration rootCache)
      (result.1.2.1, state) hadversary'
  refine ⟨rootCache, monitored, hroot, hmonitored, hforgery, ?_, ?_, ?_⟩
  · rw [hstate]
    exact htrace
  · rw [hstate]
    exact hviews
  · rw [hstate]
    exact hcache

theorem freshTargetCandidate_uniform_false
    (secretKey : SecretKey) (input : unifSpec.Domain)
    (output : unifSpec.Range input) (initialCache finalCache : QueryCache HashSpec) :
    ¬FreshTargetCandidate secretKey
      ⟨.inl (.inl input), output, initialCache, finalCache⟩ := by
  rintro ⟨candidateInput, candidateOutput, hkind, _, _⟩
  rcases hkind with hdirect | ⟨request, randomness, hrequest, _⟩ <;> simp at *

theorem freshTargetCandidate_direct_iff
    (secretKey : SecretKey) (input : HashInput) (output : HashOutput)
    (initialCache finalCache : QueryCache HashSpec)
    (hmem : (output, finalCache) ∈ support ((randomOracle input).run initialCache)) :
    FreshTargetCandidate secretKey
        ⟨.inl (.inr input), output, initialCache, finalCache⟩ ↔
      initialCache input = none := by
  constructor
  · rintro ⟨candidateInput, candidateOutput, hkind, hinitial, _⟩
    rcases hkind with hdirect | ⟨request, randomness, hrequest, _⟩
    · have hworld : Sum.inr input = Sum.inr candidateInput := Sum.inl.inj hdirect
      have hinput : candidateInput = input := (Sum.inr.inj hworld).symm
      rwa [hinput] at hinitial
    · simp at hrequest
  · intro hinitial
    refine ⟨input, output, Or.inl rfl, hinitial, ?_⟩
    exact randomOracle_run_output_cached input initialCache finalCache output hmem

set_option linter.constructorNameAsVariable false in
theorem freshTargetCandidate_signer_iff
    (secretKey : SecretKey) (request : SignRequest)
    (initialCache : QueryCache HashSpec)
    (targetRun : TargetSignerResult × QueryCache HashSpec)
    (hmem : targetRun ∈ support
      ((simulateQ romImpl (signWithTargetView secretKey request)).run initialCache)) :
    FreshTargetCandidate secretKey
        ⟨.inr request, targetRun.1.1, initialCache, targetRun.2⟩ ↔
      ∃ input view, targetRun.1.2 = some (input, view) ∧ initialCache input = none := by
  rw [signWithTargetView, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨loopResult, loopCache⟩, hloop, hfinish⟩ := hmem
  cases hloopResult : loopResult with
  | none =>
      have htargetRun : targetRun = ((none, none), loopCache) := by
        simpa only [hloopResult, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hfinish
      subst targetRun
      constructor
      · rintro ⟨input, output, hkind, hinitial, hfinal⟩
        rcases hkind with hdirect | ⟨sourceRequest, randomness, hrequest, hinput,
          hadmissible⟩
        · simp at hdirect
        · have hrequestEq : request = sourceRequest := by injection hrequest
          subst sourceRequest
          obtain ⟨indexLeaves, hindexLeaves⟩ := Option.ne_none_iff_exists'.mp hadmissible
          rcases indexLeaves with ⟨index, leaves⟩
          obtain ⟨_, _, _, _, hselected⟩ :=
            signDigestLoop_successful_source_is_selected digestAttemptLimit secretKey request
              initialCache loopCache loopResult hloop
              (messageDigestPayload secretKey.root request randomness) output index leaves
              (by rw [← hinput]; exact hinitial)
              (by rw [← hinput]; exact hfinal) hindexLeaves
          rw [hloopResult] at hselected
          simp at hselected
      · rintro ⟨input, view, hselection, _⟩
        simp at hselection
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      rw [hloopResult] at hfinish
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hfinish
      obtain ⟨⟨signature, signatureCache⟩, hsignature, hpure⟩ := hfinish
      have htargetRun : targetRun =
          ((signature, some
            (tweakableHashInput secretKey.parameter .message
              (messageDigestPayload secretKey.root request randomness),
              selectedFewTimeView index leaves)), signatureCache) := by
        simpa only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hpure
      subst targetRun
      let selectedInput := tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root request randomness)
      constructor
      · rintro ⟨input, output, hkind, hinitial, hfinal⟩
        change initialCache input = none at hinitial
        change signatureCache input = some output at hfinal
        rcases hkind with hdirect | ⟨sourceRequest, sourceRandomness, hrequest, hinput,
          hadmissible⟩
        · simp at hdirect
        · have hrequestEq : request = sourceRequest := by injection hrequest
          subst sourceRequest
          have hsignature' : (signature, signatureCache) ∈ support
              ((simulateQ (randomOracle : QueryImpl HashSpec _)
                (signAfterDigest secretKey randomness index leaves)).run loopCache) := by
            simpa only [simulateQ_romImpl_liftM] using hsignature
          have hloopCached : loopCache input ≠ none := by
            intro hnone
            have hsignatureNone := signAfterDigest_cache_message_none secretKey randomness
              index leaves loopCache signatureCache signature hsignature'
              (messageDigestPayload secretKey.root request sourceRandomness)
              (by rw [← hinput]; exact hnone)
            rw [hinput] at hfinal
            rw [hfinal] at hsignatureNone
            simp at hsignatureNone
          obtain ⟨loopOutput, hloopOutput⟩ := Option.ne_none_iff_exists'.mp hloopCached
          have hloopLe := simulateQ_romImpl_cache_le
            (liftM (signAfterDigest secretKey randomness index leaves) :
              OracleComp OracleWorld (Option Signature)) loopCache
                (signature, signatureCache) (by simpa only [simulateQ_romImpl_liftM] using hsignature)
          have houtputEq : loopOutput = output := by
            have hcached := hloopLe hloopOutput
            change signatureCache input = some loopOutput at hcached
            rw [hfinal] at hcached
            exact (Option.some.inj hcached).symm
          obtain ⟨indexLeaves, hindexLeaves⟩ := Option.ne_none_iff_exists'.mp hadmissible
          rcases indexLeaves with ⟨sourceIndex, sourceLeaves⟩
          have hloopOutput' : loopCache input = some output := by
            simpa only [houtputEq] using hloopOutput
          obtain ⟨_, selectedRandomness, _, hpayload, hselected⟩ :=
            signDigestLoop_successful_source_is_selected digestAttemptLimit secretKey request
              initialCache loopCache loopResult hloop
              (messageDigestPayload secretKey.root request sourceRandomness) output
              sourceIndex sourceLeaves (by rw [← hinput]; exact hinitial)
              (by rw [← hinput]; exact hloopOutput') hindexLeaves
          have hfields := Prod.mk.inj (Option.some.inj (hloopResult.symm.trans hselected))
          have hrandomness : randomness = selectedRandomness := hfields.1
          refine ⟨selectedInput, selectedFewTimeView index leaves, rfl, ?_⟩
          change initialCache (tweakableHashInput secretKey.parameter .message
            (messageDigestPayload secretKey.root request randomness)) = none
          rw [hrandomness, ← hpayload, ← hinput]
          exact hinitial
      · rintro ⟨input, view, hselection, hinitial⟩
        have hfields := Prod.mk.inj (Option.some.inj hselection)
        rw [← hfields.1] at hinitial
        obtain ⟨_, _, attemptCache, output, hattemptMiss, hattemptOutput, hloopCache⟩ :=
          signDigestLoop_fresh_selected_attempt digestAttemptLimit secretKey request
            randomness index leaves initialCache loopCache hinitial
            (by simpa only [hloopResult] using hloop)
        have hloopCached : loopCache selectedInput = some output := by
          rw [hloopCache]
          simp [selectedInput]
        have hsignatureLe := simulateQ_romImpl_cache_le
          (liftM (signAfterDigest secretKey randomness index leaves) :
            OracleComp OracleWorld (Option Signature)) loopCache
              (signature, signatureCache) (by simpa only [simulateQ_romImpl_liftM] using hsignature)
        refine ⟨selectedInput, output, Or.inr ⟨request, randomness, rfl, rfl, ?_⟩,
          hinitial, hsignatureLe hloopCached⟩
        rw [hattemptOutput]
        simp

def OriginTargetMonitorState.CandidateCountCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (state : OriginTargetMonitorState configuration) : Prop :=
  state.candidateOrdinal = freshTargetCandidateCount secretKey state.origin.viewed.trace

theorem OriginTargetMonitorState.candidateCountCoherent_initial
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (cache : QueryCache HashSpec) :
    (OriginTargetMonitorState.initial configuration cache).CandidateCountCoherent
      secretKey := by
  rfl

theorem originTargetMonitoredAdversaryImpl_query_candidateCountCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (result : (OracleWorld + SigningSpec).Range input ×
      OriginTargetMonitorState configuration)
    (hcoherent : state.CandidateCountCoherent secretKey)
    (hmem : result ∈ support
      ((originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
        state)) : result.2.CandidateCountCoherent secretKey := by
  classical
  change state.candidateOrdinal =
    freshTargetCandidateCount secretKey state.origin.viewed.trace at hcoherent
  cases input with
  | inl worldInput =>
      rw [originTargetMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, origin⟩, horiginMem, hpure⟩ := hmem
      rw [originMonitoredAdversaryImpl] at horiginMem
      simp only [StateT.run, mem_support_bind_iff] at horiginMem
      obtain ⟨⟨originOutput, finalCache⟩, hquery, horiginPure⟩ := horiginMem
      cases worldInput with
      | inl uniformInput =>
          simp only [support_pure, Set.mem_singleton_iff] at horiginPure hpure
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj horiginPure
          have hstateEq := congrArg Prod.snd hpure
          rw [hstateEq]
          simp only [OriginTargetMonitorState.advanceOrigin]
          rw [OriginTargetMonitorState.CandidateCountCoherent,
            freshTargetCandidateCount_update]
          rw [if_neg (freshTargetCandidate_uniform_false secretKey uniformInput output
            state.origin.viewed.cache finalCache)]
          exact hcoherent
      | inr hashInput =>
          simp only [support_pure, Set.mem_singleton_iff] at horiginPure
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj horiginPure
          have hquery' : (output, finalCache) ∈
              support ((randomOracle hashInput).run state.origin.viewed.cache) := by
            exact hquery
          by_cases hfresh : state.origin.viewed.cache hashInput = none
          · simp only [hfresh, if_true, support_pure, Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            simp only [OriginTargetMonitorState.advanceOrigin,
              OriginTargetMonitorState.recordCandidate]
            rw [OriginTargetMonitorState.CandidateCountCoherent,
              freshTargetCandidateCount_update]
            rw [if_pos ((freshTargetCandidate_direct_iff secretKey hashInput output
              state.origin.viewed.cache finalCache hquery').mpr hfresh)]
            change state.candidateOrdinal + 1 =
              freshTargetCandidateCount secretKey state.origin.viewed.trace + 1
            rw [hcoherent]
          · simp only [hfresh, if_false, support_pure, Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            simp only [OriginTargetMonitorState.advanceOrigin]
            rw [OriginTargetMonitorState.CandidateCountCoherent,
              freshTargetCandidateCount_update]
            rw [if_neg (fun hcandidate => hfresh
              ((freshTargetCandidate_direct_iff secretKey hashInput output
                state.origin.viewed.cache finalCache hquery').mp hcandidate))]
            exact hcoherent

  | inr request =>
      rw [originTargetMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨targetRun, htargetRun, hpure⟩ := hmem
      have hcand := freshTargetCandidate_signer_iff secretKey request
        state.origin.viewed.cache targetRun htargetRun
      cases hselection : targetRun.1.2 with
      | none =>
          simp only [hselection, support_pure, Set.mem_singleton_iff] at hpure
          have hstateEq := congrArg Prod.snd hpure
          rw [hstateEq]
          simp only [OriginTargetMonitorState.advanceOrigin]
          simp only [targetSignerResultView]
          rw [OriginTargetMonitorState.CandidateCountCoherent,
            freshTargetCandidateCount_update]
          rw [if_neg (fun hcandidate => by
            obtain ⟨input, view, hsome, _⟩ := hcand.mp hcandidate
            rw [hselection] at hsome
            simp at hsome)]
          exact hcoherent
      | some selection =>
          rcases selection with ⟨selectedInput, view⟩
          by_cases hfresh : state.origin.viewed.cache selectedInput = none
          · simp only [hselection, hfresh, if_true, support_pure,
              Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            simp only [OriginTargetMonitorState.advanceOrigin,
              OriginTargetMonitorState.recordCandidate]
            simp only [targetSignerResultView]
            rw [OriginTargetMonitorState.CandidateCountCoherent,
              freshTargetCandidateCount_update]
            rw [if_pos (hcand.mpr ⟨selectedInput, view, hselection, hfresh⟩)]
            change state.candidateOrdinal + 1 =
              freshTargetCandidateCount secretKey state.origin.viewed.trace + 1
            rw [hcoherent]
          · simp only [hselection, hfresh, if_false, support_pure,
              Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            simp only [OriginTargetMonitorState.advanceOrigin]
            simp only [targetSignerResultView]
            rw [OriginTargetMonitorState.CandidateCountCoherent,
              freshTargetCandidateCount_update]
            rw [if_neg (fun hcandidate => by
              obtain ⟨input, foundView, hsome, hmiss⟩ := hcand.mp hcandidate
              have hfields := Prod.mk.inj (Option.some.inj (hselection.symm.trans hsome))
              apply hfresh
              rw [hfields.1]
              exact hmiss)]
            exact hcoherent

theorem originTargetMonitoredAdversaryImpl_candidateCountCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (result : α × OriginTargetMonitorState configuration)
    (hcoherent : initialState.CandidateCountCoherent secretKey)
    (hmem : result ∈ support
      ((simulateQ
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState)) : result.2.CandidateCountCoherent secretKey := by
  exact OracleComp.simulateQ_run_preservesInv
    (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
    (OriginTargetMonitorState.CandidateCountCoherent secretKey)
    (by
      intro input state hstate queryResult hquery
      exact originTargetMonitoredAdversaryImpl_query_candidateCountCoherent
        configuration secretKey targetOrdinal input state queryResult hstate hquery)
    computation initialState hcoherent result hmem

theorem originTargetMonitoredAdversaryImpl_query_candidateViewsCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (result : (OracleWorld + SigningSpec).Range input ×
      OriginTargetMonitorState configuration)
    (hcoherent : state.CandidateViewsCoherent targetOrdinal)
    (hmem : result ∈ support
      ((originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
        state)) : result.2.CandidateViewsCoherent targetOrdinal := by
  classical
  cases input with
  | inl worldInput =>
      rw [originTargetMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, origin⟩, _, hpure⟩ := hmem
      cases worldInput with
      | inl uniformInput =>
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          have hstateEq := congrArg Prod.snd hpure
          rw [hstateEq]
          exact state.candidateViewsCoherent_advanceOrigin targetOrdinal origin hcoherent
      | inr hashInput =>
          by_cases hfresh : state.origin.viewed.cache hashInput = none
          · simp only [hfresh, if_true, support_pure, Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            exact OriginTargetMonitorState.candidateViewsCoherent_recordCandidate
              targetOrdinal (state.advanceOrigin origin) _ _
                (state.candidateViewsCoherent_advanceOrigin targetOrdinal origin hcoherent)
          · simp only [hfresh, if_false, support_pure, Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            exact state.candidateViewsCoherent_advanceOrigin targetOrdinal origin hcoherent
  | inr request =>
      rw [originTargetMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨targetRun, _, hpure⟩ := hmem
      cases hselection : targetRun.1.2 with
      | none =>
          simp only [hselection, support_pure, Set.mem_singleton_iff] at hpure
          have hstateEq := congrArg Prod.snd hpure
          rw [hstateEq]
          exact state.candidateViewsCoherent_advanceOrigin targetOrdinal _ hcoherent
      | some selection =>
          rcases selection with ⟨selectedInput, view⟩
          by_cases hfresh : state.origin.viewed.cache selectedInput = none
          · simp only [hselection, hfresh, if_true, support_pure,
              Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            exact OriginTargetMonitorState.candidateViewsCoherent_recordCandidate
              targetOrdinal _ _ _
                (state.candidateViewsCoherent_advanceOrigin targetOrdinal _ hcoherent)
          · simp only [hselection, hfresh, if_false, support_pure,
              Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            exact state.candidateViewsCoherent_advanceOrigin targetOrdinal _ hcoherent

theorem originTargetMonitoredAdversaryImpl_candidateViewsCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (result : α × OriginTargetMonitorState configuration)
    (hcoherent : initialState.CandidateViewsCoherent targetOrdinal)
    (hmem : result ∈ support
      ((simulateQ
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState)) : result.2.CandidateViewsCoherent targetOrdinal := by
  exact OracleComp.simulateQ_run_preservesInv
    (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
    (OriginTargetMonitorState.CandidateViewsCoherent targetOrdinal)
    (by
      intro input state hstate queryResult hquery
      exact originTargetMonitoredAdversaryImpl_query_candidateViewsCoherent
        configuration secretKey targetOrdinal input state queryResult hstate hquery)
    computation initialState hcoherent result hmem

theorem originTargetMonitoredAdversaryImpl_query_candidateAllowedCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (result : (OracleWorld + SigningSpec).Range input ×
      OriginTargetMonitorState configuration)
    (hcoherent : state.CandidateAllowedCoherent targetOrdinal)
    (hmem : result ∈ support
      ((originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
        state)) : result.2.CandidateAllowedCoherent targetOrdinal := by
  classical
  cases input with
  | inl worldInput =>
      rw [originTargetMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, origin⟩, _, hpure⟩ := hmem
      cases worldInput with
      | inl uniformInput =>
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          have hstateEq := congrArg Prod.snd hpure
          rw [hstateEq]
          exact state.candidateAllowedCoherent_advanceOrigin targetOrdinal origin hcoherent
      | inr hashInput =>
          by_cases hfresh : state.origin.viewed.cache hashInput = none
          · simp only [hfresh, if_true, support_pure, Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            exact OriginTargetMonitorState.candidateAllowedCoherent_recordCandidate
              targetOrdinal (state.advanceOrigin origin) _ _
                (state.candidateAllowedCoherent_advanceOrigin targetOrdinal origin hcoherent)
          · simp only [hfresh, if_false, support_pure, Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            exact state.candidateAllowedCoherent_advanceOrigin targetOrdinal origin hcoherent
  | inr request =>
      rw [originTargetMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨targetRun, _, hpure⟩ := hmem
      cases hselection : targetRun.1.2 with
      | none =>
          simp only [hselection, support_pure, Set.mem_singleton_iff] at hpure
          have hstateEq := congrArg Prod.snd hpure
          rw [hstateEq]
          exact state.candidateAllowedCoherent_advanceOrigin targetOrdinal _ hcoherent
      | some selection =>
          rcases selection with ⟨selectedInput, view⟩
          by_cases hfresh : state.origin.viewed.cache selectedInput = none
          · simp only [hselection, hfresh, if_true, support_pure,
              Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            exact OriginTargetMonitorState.candidateAllowedCoherent_recordCandidate
              targetOrdinal _ _ _
                (state.candidateAllowedCoherent_advanceOrigin targetOrdinal _ hcoherent)
          · simp only [hselection, hfresh, if_false, support_pure,
              Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            exact state.candidateAllowedCoherent_advanceOrigin targetOrdinal _ hcoherent

theorem originTargetMonitoredAdversaryImpl_candidateAllowedCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (result : α × OriginTargetMonitorState configuration)
    (hcoherent : initialState.CandidateAllowedCoherent targetOrdinal)
    (hmem : result ∈ support
      ((simulateQ
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState)) : result.2.CandidateAllowedCoherent targetOrdinal := by
  exact OracleComp.simulateQ_run_preservesInv
    (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
    (OriginTargetMonitorState.CandidateAllowedCoherent targetOrdinal)
    (by
      intro input state hstate queryResult hquery
      exact originTargetMonitoredAdversaryImpl_query_candidateAllowedCoherent
        configuration secretKey targetOrdinal input state queryResult hstate hquery)
    computation initialState hcoherent result hmem

def appendTargetViewedState
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (view : Option FewTimeView)
    (state : ViewedFullTraceState) : ViewedFullTraceState :=
  let entry : AdversaryCacheEntry := ⟨input, output, initialCache, finalCache⟩
  ⟨finalCache, fullAdversaryTraceUpdate input initialCache output finalCache state.trace,
    appendOriginReplayView entry state.views view, state.targetView⟩

theorem targetCandidateIntervalView_appendTargetViewedState_old
    (secretKey : SecretKey) (state : ViewedFullTraceState)
    (hvalid : state.ValidViews secretKey) (hconsistent : state.trace.Consistent)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (view : Option FewTimeView)
    (position : Fin state.trace.intervals.length) :
    targetCandidateIntervalView
        (appendTargetViewedState input initialCache output finalCache view state)
        ⟨position.val, by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ =
      targetCandidateIntervalView state position := by
  let oldEntry := state.trace.intervals.get position
  have hentry : state.trace.intervals.get position = oldEntry := rfl
  rcases oldEntry with ⟨entryInput, entryOutput, entryInitial, entryFinal⟩
  have hentryElem : state.trace.intervals[position.val] =
      ⟨entryInput, entryOutput, entryInitial, entryFinal⟩ := by
    simpa only [List.get_eq_getElem] using hentry
  cases entryInput with
  | inl worldInput =>
      cases worldInput <;>
        simp [targetCandidateIntervalView, appendTargetViewedState,
          fullAdversaryTraceUpdate, List.getElem_append_left position.isLt, hentryElem]
  | inr request =>
      obtain ⟨_, viewPosition, _, hviewRank, _, _⟩ :=
        ViewedFullTraceState.ValidViews.signer_interval hvalid hconsistent position request
          entryOutput entryInitial entryFinal hentry
      have hrankLt : signerIntervalCount
          (state.trace.intervals.take position.val) < state.views.length := by
        rw [← hviewRank]
        exact viewPosition.isLt
      have htake (newInput : (OracleWorld + SigningSpec).Domain)
          (newOutput : (OracleWorld + SigningSpec).Range newInput) :
          (state.trace.intervals ++
            [(⟨newInput, newOutput, initialCache, finalCache⟩ :
              AdversaryCacheEntry)]).take position.val =
              state.trace.intervals.take position.val := by
        rw [List.take_append_of_le_length]
        exact position.isLt.le
      cases input with
      | inl worldInput =>
          cases worldInput <;>
            simp [targetCandidateIntervalView, appendTargetViewedState,
              appendOriginReplayView, fullAdversaryTraceUpdate,
              List.getElem_append_left position.isLt, hentryElem, htake]
      | inr newRequest =>
          simp only [targetCandidateIntervalView, appendTargetViewedState,
            appendOriginReplayView, fullAdversaryTraceUpdate]
          simp only [List.get_eq_getElem]
          rw [List.getElem_append_left position.isLt, hentryElem,
            htake (.inr newRequest) output]
          rw [List.getElem?_append_left hrankLt]

theorem targetCandidateIntervalView_appendTargetViewedState_last
    (secretKey : SecretKey) (state : ViewedFullTraceState)
    (hvalid : state.ValidViews secretKey) (hconsistent : state.trace.Consistent)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (view : Option FewTimeView) :
    targetCandidateIntervalView
        (appendTargetViewedState input initialCache output finalCache view state)
        ⟨state.trace.intervals.length, by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ =
      match input with
      | .inl (.inl _) => default
      | .inl (.inr _) => hashOutputFewTimeView output
      | .inr _ => view.getD default := by
  have hrank : signerIntervalCount state.trace.intervals = state.views.length := by
    calc
      signerIntervalCount state.trace.intervals = state.trace.signing.length := by
        exact congrArg List.length hconsistent.2
      _ = state.views.length := hvalid.length_eq
  cases input with
  | inl worldInput =>
      cases worldInput <;>
        simp [targetCandidateIntervalView, appendTargetViewedState,
          fullAdversaryTraceUpdate]
  | inr request =>
      simp [targetCandidateIntervalView, appendTargetViewedState,
        appendOriginReplayView, fullAdversaryTraceUpdate, hrank]

noncomputable def targetCandidateIntervalAllowed
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (state : ViewedFullTraceState)
    (position : Fin state.trace.intervals.length) : Bool :=
  match (state.trace.intervals.get position).input with
  | .inl (.inl _) => true
  | .inl (.inr _) => decide (configuration.sourceAt?
      (directIntervalCount (state.trace.intervals.take position.val)) = none)
  | .inr _ => decide (pattern.selectedAt?
      (signerIntervalCount (state.trace.intervals.take position.val)) = none)

theorem targetCandidateIntervalAllowed_appendTargetViewedState_old
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (state : ViewedFullTraceState)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (view : Option FewTimeView)
    (position : Fin state.trace.intervals.length) :
    targetCandidateIntervalAllowed configuration
        (appendTargetViewedState input initialCache output finalCache view state)
        ⟨position.val, by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ =
      targetCandidateIntervalAllowed configuration state position := by
  have hentry :
      (appendTargetViewedState input initialCache output finalCache view state).trace.intervals.get
          ⟨position.val, by
            simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ =
        state.trace.intervals.get position := by
    have hget :
        (appendTargetViewedState input initialCache output finalCache view state).trace.intervals[
            position.val]? = state.trace.intervals[position.val]? := by
      simp [appendTargetViewedState, fullAdversaryTraceUpdate]
    rw [List.getElem?_eq_getElem (by
      simp [appendTargetViewedState, fullAdversaryTraceUpdate]),
      List.getElem?_eq_getElem position.isLt] at hget
    exact Option.some.inj hget
  have htake :
      (appendTargetViewedState input initialCache output finalCache view state).trace.intervals.take
          position.val = state.trace.intervals.take position.val := by
    change (state.trace.intervals ++
      [(⟨input, output, initialCache, finalCache⟩ : AdversaryCacheEntry)]).take position.val =
        state.trace.intervals.take position.val
    rw [List.take_append_of_le_length position.isLt.le]
  simp only [targetCandidateIntervalAllowed]
  rw [hentry, htake]

theorem targetCandidateIntervalAllowed_appendTargetViewedState_last
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (state : ViewedFullTraceState)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (view : Option FewTimeView) :
    targetCandidateIntervalAllowed configuration
        (appendTargetViewedState input initialCache output finalCache view state)
        ⟨state.trace.intervals.length, by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ =
      match input with
      | .inl (.inl _) => true
      | .inl (.inr _) => decide (configuration.sourceAt?
          (directIntervalCount state.trace.intervals) = none)
      | .inr _ => decide (pattern.selectedAt?
          (signerIntervalCount state.trace.intervals) = none) := by
  cases input with
  | inl worldInput =>
      cases worldInput <;>
        simp [targetCandidateIntervalAllowed, appendTargetViewedState,
          fullAdversaryTraceUpdate]
  | inr request =>
      simp [targetCandidateIntervalAllowed, appendTargetViewedState,
        fullAdversaryTraceUpdate]

def CandidateViewsCover (secretKey : SecretKey) (state : ViewedFullTraceState)
    (candidateViews : List FewTimeView) : Prop :=
  ∀ position, FreshTargetCandidate secretKey (state.trace.intervals.get position) →
    targetCandidateIntervalView state position ∈ candidateViews

theorem candidateViewsCover_nil (secretKey : SecretKey) (cache : QueryCache HashSpec) :
    CandidateViewsCover secretKey ⟨cache, ⟨[], [], []⟩, [], none⟩ [] := by
  intro position
  exact Fin.elim0 position

theorem candidateViewsCover_append_candidate
    (secretKey : SecretKey) (state : ViewedFullTraceState)
    (hvalid : state.ValidViews secretKey) (hconsistent : state.trace.Consistent)
    (candidateViews : List FewTimeView)
    (hcover : CandidateViewsCover secretKey state candidateViews)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (view : Option FewTimeView)
    (retained : FewTimeView)
    (hlast : targetCandidateIntervalView
        (appendTargetViewedState input initialCache output finalCache view state)
        ⟨state.trace.intervals.length, by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ = retained) :
    CandidateViewsCover secretKey
      (appendTargetViewedState input initialCache output finalCache view state)
      (candidateViews ++ [retained]) := by
  intro position hcandidate
  by_cases hold : position.val < state.trace.intervals.length
  · let oldPosition : Fin state.trace.intervals.length := ⟨position.val, hold⟩
    have hposition : position = ⟨oldPosition.val, by
        simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ := Fin.ext rfl
    have hentry :
        (appendTargetViewedState input initialCache output finalCache view state).trace.intervals.get
            position = state.trace.intervals.get oldPosition := by
      have hget :
          (appendTargetViewedState input initialCache output finalCache view state).trace.intervals[
              position.val]? = state.trace.intervals[position.val]? := by
        simp [appendTargetViewedState, fullAdversaryTraceUpdate,
          List.getElem?_append_left hold]
      rw [List.getElem?_eq_getElem position.isLt,
        List.getElem?_eq_getElem hold] at hget
      exact Option.some.inj hget
    have holdCandidate : FreshTargetCandidate secretKey
        (state.trace.intervals.get oldPosition) := by
      rw [← hentry]
      exact hcandidate
    have holdView := hcover oldPosition holdCandidate
    rw [hposition, targetCandidateIntervalView_appendTargetViewedState_old
      secretKey state hvalid hconsistent input initialCache output finalCache view oldPosition]
    exact List.mem_append_left _ holdView
  · have hlastValue : position.val = state.trace.intervals.length := by
      have hlt : position.val < state.trace.intervals.length + 1 := by
        simpa [appendTargetViewedState, fullAdversaryTraceUpdate] using position.isLt
      omega
    have hposition : position = ⟨state.trace.intervals.length, by
        simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ := Fin.ext hlastValue
    rw [hposition, hlast]
    simp

theorem candidateViewsCover_append_noncandidate
    (secretKey : SecretKey) (state : ViewedFullTraceState)
    (hvalid : state.ValidViews secretKey) (hconsistent : state.trace.Consistent)
    (candidateViews : List FewTimeView)
    (hcover : CandidateViewsCover secretKey state candidateViews)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (view : Option FewTimeView)
    (hnon : ¬ FreshTargetCandidate secretKey
      ⟨input, output, initialCache, finalCache⟩) :
    CandidateViewsCover secretKey
      (appendTargetViewedState input initialCache output finalCache view state)
      candidateViews := by
  intro position hcandidate
  by_cases hold : position.val < state.trace.intervals.length
  · let oldPosition : Fin state.trace.intervals.length := ⟨position.val, hold⟩
    have hposition : position = ⟨oldPosition.val, by
        simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ := Fin.ext rfl
    have hentry :
        (appendTargetViewedState input initialCache output finalCache view state).trace.intervals.get
            position = state.trace.intervals.get oldPosition := by
      have hget :
          (appendTargetViewedState input initialCache output finalCache view state).trace.intervals[
              position.val]? = state.trace.intervals[position.val]? := by
        simp [appendTargetViewedState, fullAdversaryTraceUpdate,
          List.getElem?_append_left hold]
      rw [List.getElem?_eq_getElem position.isLt,
        List.getElem?_eq_getElem hold] at hget
      exact Option.some.inj hget
    have holdCandidate : FreshTargetCandidate secretKey
        (state.trace.intervals.get oldPosition) := by
      rw [← hentry]
      exact hcandidate
    have holdView := hcover oldPosition holdCandidate
    rw [hposition, targetCandidateIntervalView_appendTargetViewedState_old
      secretKey state hvalid hconsistent input initialCache output finalCache view oldPosition]
    exact holdView
  · have hlastValue : position.val = state.trace.intervals.length := by
      have hlt : position.val < state.trace.intervals.length + 1 := by
        simpa [appendTargetViewedState, fullAdversaryTraceUpdate] using position.isLt
      omega
    have hposition : position = ⟨state.trace.intervals.length, by
        simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ := Fin.ext hlastValue
    exfalso
    apply hnon
    simpa [hposition, appendTargetViewedState, fullAdversaryTraceUpdate] using hcandidate

def CandidateViewsExact (secretKey : SecretKey) (state : ViewedFullTraceState)
    (candidateViews : List FewTimeView) : Prop :=
  CandidateViewsCover secretKey state candidateViews ∧
    candidateViews.length = freshTargetCandidateCount secretKey state.trace ∧
    ∀ position, FreshTargetCandidate secretKey (state.trace.intervals.get position) →
      candidateViews[state.trace.intervals.countPBefore
        (fun entry => decide (FreshTargetCandidate secretKey entry)) position.val]? =
          some (targetCandidateIntervalView state position)

theorem candidateViewsExact_nil (secretKey : SecretKey) (cache : QueryCache HashSpec) :
    CandidateViewsExact secretKey ⟨cache, ⟨[], [], []⟩, [], none⟩ [] := by
  refine ⟨candidateViewsCover_nil secretKey cache, rfl, ?_⟩
  intro position
  exact Fin.elim0 position

theorem candidateViewsExact_append_candidate
    (secretKey : SecretKey) (state : ViewedFullTraceState)
    (hvalid : state.ValidViews secretKey) (hconsistent : state.trace.Consistent)
    (candidateViews : List FewTimeView)
    (hexact : CandidateViewsExact secretKey state candidateViews)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (view : Option FewTimeView)
    (retained : FewTimeView)
    (hcandidate : FreshTargetCandidate secretKey
      ⟨input, output, initialCache, finalCache⟩)
    (hlast : targetCandidateIntervalView
        (appendTargetViewedState input initialCache output finalCache view state)
        ⟨state.trace.intervals.length, by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ = retained) :
    CandidateViewsExact secretKey
      (appendTargetViewedState input initialCache output finalCache view state)
      (candidateViews ++ [retained]) := by
  refine ⟨candidateViewsCover_append_candidate secretKey state hvalid hconsistent
    candidateViews hexact.1 input initialCache output finalCache view retained hlast, ?_, ?_⟩
  · simp [freshTargetCandidateCount, appendTargetViewedState, fullAdversaryTraceUpdate,
      hcandidate, hexact.2.1]
  · intro position hpositionCandidate
    by_cases hold : position.val < state.trace.intervals.length
    · let oldPosition : Fin state.trace.intervals.length := ⟨position.val, hold⟩
      have hentry :
          (appendTargetViewedState input initialCache output finalCache view state).trace.intervals.get
              position = state.trace.intervals.get oldPosition := by
        have hget :
            (appendTargetViewedState input initialCache output finalCache view state).trace.intervals[
                position.val]? = state.trace.intervals[position.val]? := by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate,
            List.getElem?_append_left hold]
        rw [List.getElem?_eq_getElem position.isLt,
          List.getElem?_eq_getElem hold] at hget
        exact Option.some.inj hget
      have holdCandidate : FreshTargetCandidate secretKey
          (state.trace.intervals.get oldPosition) := by
        rw [← hentry]
        exact hpositionCandidate
      have htake :
          (appendTargetViewedState input initialCache output finalCache view state).trace.intervals.take
              position.val = state.trace.intervals.take oldPosition.val := by
        change (state.trace.intervals ++
          [(⟨input, output, initialCache, finalCache⟩ : AdversaryCacheEntry)]).take position.val =
            state.trace.intervals.take position.val
        rw [List.take_append_of_le_length hold.le]
      rw [List.countPBefore_eq_countP_take, htake,
        ← List.countPBefore_eq_countP_take]
      rw [show position = ⟨oldPosition.val, by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ from Fin.ext rfl,
        targetCandidateIntervalView_appendTargetViewedState_old
          secretKey state hvalid hconsistent input initialCache output finalCache view oldPosition]
      have holdExact := hexact.2.2 oldPosition holdCandidate
      rw [List.getElem?_append_left
        (List.getElem?_eq_some_iff.mp holdExact).1]
      exact holdExact
    · have hlastValue : position.val = state.trace.intervals.length := by
        have hlt : position.val < state.trace.intervals.length + 1 := by
          simpa [appendTargetViewedState, fullAdversaryTraceUpdate] using position.isLt
        omega
      have hposition : position = ⟨state.trace.intervals.length, by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ := Fin.ext hlastValue
      have hviewLast : targetCandidateIntervalView
          (appendTargetViewedState input initialCache output finalCache view state) position =
            retained := by
        rw [hposition]
        exact hlast
      rw [hviewLast]
      rw [List.countPBefore_eq_countP_take, hlastValue]
      simp only [appendTargetViewedState, fullAdversaryTraceUpdate]
      rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
      change (candidateViews ++ [retained])[
        freshTargetCandidateCount secretKey state.trace]? = some retained
      rw [← hexact.2.1]
      simp

theorem candidateViewsExact_append_noncandidate
    (secretKey : SecretKey) (state : ViewedFullTraceState)
    (hvalid : state.ValidViews secretKey) (hconsistent : state.trace.Consistent)
    (candidateViews : List FewTimeView)
    (hexact : CandidateViewsExact secretKey state candidateViews)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (view : Option FewTimeView)
    (hnon : ¬FreshTargetCandidate secretKey
      ⟨input, output, initialCache, finalCache⟩) :
    CandidateViewsExact secretKey
      (appendTargetViewedState input initialCache output finalCache view state)
      candidateViews := by
  refine ⟨candidateViewsCover_append_noncandidate secretKey state hvalid hconsistent
    candidateViews hexact.1 input initialCache output finalCache view hnon, ?_, ?_⟩
  · simp [freshTargetCandidateCount, appendTargetViewedState, fullAdversaryTraceUpdate,
      hnon, hexact.2.1]
  · intro position hpositionCandidate
    by_cases hold : position.val < state.trace.intervals.length
    · let oldPosition : Fin state.trace.intervals.length := ⟨position.val, hold⟩
      have hentry :
          (appendTargetViewedState input initialCache output finalCache view state).trace.intervals.get
              position = state.trace.intervals.get oldPosition := by
        have hget :
            (appendTargetViewedState input initialCache output finalCache view state).trace.intervals[
                position.val]? = state.trace.intervals[position.val]? := by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate,
            List.getElem?_append_left hold]
        rw [List.getElem?_eq_getElem position.isLt,
          List.getElem?_eq_getElem hold] at hget
        exact Option.some.inj hget
      have holdCandidate : FreshTargetCandidate secretKey
          (state.trace.intervals.get oldPosition) := by
        rw [← hentry]
        exact hpositionCandidate
      have htake :
          (appendTargetViewedState input initialCache output finalCache view state).trace.intervals.take
              position.val = state.trace.intervals.take oldPosition.val := by
        change (state.trace.intervals ++
          [(⟨input, output, initialCache, finalCache⟩ : AdversaryCacheEntry)]).take position.val =
            state.trace.intervals.take position.val
        rw [List.take_append_of_le_length hold.le]
      rw [List.countPBefore_eq_countP_take, htake,
        ← List.countPBefore_eq_countP_take]
      rw [show position = ⟨oldPosition.val, by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ from Fin.ext rfl,
        targetCandidateIntervalView_appendTargetViewedState_old
          secretKey state hvalid hconsistent input initialCache output finalCache view oldPosition]
      exact hexact.2.2 oldPosition holdCandidate
    · have hlastValue : position.val = state.trace.intervals.length := by
        have hlt : position.val < state.trace.intervals.length + 1 := by
          simpa [appendTargetViewedState, fullAdversaryTraceUpdate] using position.isLt
        omega
      have hposition : position = ⟨state.trace.intervals.length, by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ := Fin.ext hlastValue
      exfalso
      apply hnon
      simpa [hposition, appendTargetViewedState, fullAdversaryTraceUpdate] using
        hpositionCandidate

def CandidateAllowedExact
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (state : ViewedFullTraceState) (candidateAllowed : List Bool) : Prop :=
  candidateAllowed.length = freshTargetCandidateCount secretKey state.trace ∧
    ∀ position, FreshTargetCandidate secretKey (state.trace.intervals.get position) →
      candidateAllowed[state.trace.intervals.countPBefore
        (fun entry => decide (FreshTargetCandidate secretKey entry)) position.val]? =
          some (targetCandidateIntervalAllowed configuration state position)

theorem candidateAllowedExact_nil
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (cache : QueryCache HashSpec) :
    CandidateAllowedExact configuration secretKey
      ⟨cache, ⟨[], [], []⟩, [], none⟩ [] := by
  refine ⟨rfl, ?_⟩
  intro position
  exact Fin.elim0 position

theorem candidateAllowedExact_append_candidate
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (state : ViewedFullTraceState) (candidateAllowed : List Bool)
    (hexact : CandidateAllowedExact configuration secretKey state candidateAllowed)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (view : Option FewTimeView)
    (allowed : Bool)
    (hcandidate : FreshTargetCandidate secretKey
      ⟨input, output, initialCache, finalCache⟩)
    (hlast : targetCandidateIntervalAllowed configuration
        (appendTargetViewedState input initialCache output finalCache view state)
        ⟨state.trace.intervals.length, by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ = allowed) :
    CandidateAllowedExact configuration secretKey
      (appendTargetViewedState input initialCache output finalCache view state)
      (candidateAllowed ++ [allowed]) := by
  constructor
  · simp [freshTargetCandidateCount, appendTargetViewedState, fullAdversaryTraceUpdate,
      hcandidate, hexact.1]
  · intro position hpositionCandidate
    by_cases hold : position.val < state.trace.intervals.length
    · let oldPosition : Fin state.trace.intervals.length := ⟨position.val, hold⟩
      have hentry :
          (appendTargetViewedState input initialCache output finalCache view state).trace.intervals.get
              position = state.trace.intervals.get oldPosition := by
        have hget :
            (appendTargetViewedState input initialCache output finalCache view state).trace.intervals[
                position.val]? = state.trace.intervals[position.val]? := by
          simp only [appendTargetViewedState, fullAdversaryTraceUpdate]
          rw [List.getElem?_append_left hold]
        rw [List.getElem?_eq_getElem position.isLt,
          List.getElem?_eq_getElem hold] at hget
        exact Option.some.inj hget
      have holdCandidate : FreshTargetCandidate secretKey
          (state.trace.intervals.get oldPosition) := by
        rw [← hentry]
        exact hpositionCandidate
      have htake :
          (appendTargetViewedState input initialCache output finalCache view state).trace.intervals.take
              position.val = state.trace.intervals.take oldPosition.val := by
        change (state.trace.intervals ++
          [(⟨input, output, initialCache, finalCache⟩ : AdversaryCacheEntry)]).take position.val =
            state.trace.intervals.take position.val
        rw [List.take_append_of_le_length hold.le]
      rw [List.countPBefore_eq_countP_take, htake,
        ← List.countPBefore_eq_countP_take]
      rw [show position = ⟨oldPosition.val, by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ from Fin.ext rfl,
        targetCandidateIntervalAllowed_appendTargetViewedState_old
          configuration state input initialCache output finalCache view oldPosition]
      have holdExact := hexact.2 oldPosition holdCandidate
      rw [List.getElem?_append_left
        (List.getElem?_eq_some_iff.mp holdExact).1]
      exact holdExact
    · have hlastValue : position.val = state.trace.intervals.length := by
        have hlt : position.val < state.trace.intervals.length + 1 := by
          simpa [appendTargetViewedState, fullAdversaryTraceUpdate] using position.isLt
        omega
      have hposition : position = ⟨state.trace.intervals.length, by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ := Fin.ext hlastValue
      have hallowedLast : targetCandidateIntervalAllowed configuration
          (appendTargetViewedState input initialCache output finalCache view state) position =
            allowed := by
        rw [hposition]
        exact hlast
      rw [hallowedLast, List.countPBefore_eq_countP_take, hlastValue]
      simp only [appendTargetViewedState, fullAdversaryTraceUpdate]
      rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
      change (candidateAllowed ++ [allowed])[
        freshTargetCandidateCount secretKey state.trace]? = some allowed
      rw [← hexact.1]
      simp

theorem candidateAllowedExact_append_noncandidate
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (state : ViewedFullTraceState) (candidateAllowed : List Bool)
    (hexact : CandidateAllowedExact configuration secretKey state candidateAllowed)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (view : Option FewTimeView)
    (hnon : ¬FreshTargetCandidate secretKey
      ⟨input, output, initialCache, finalCache⟩) :
    CandidateAllowedExact configuration secretKey
      (appendTargetViewedState input initialCache output finalCache view state)
      candidateAllowed := by
  constructor
  · simp [freshTargetCandidateCount, appendTargetViewedState, fullAdversaryTraceUpdate,
      hnon, hexact.1]
  · intro position hpositionCandidate
    by_cases hold : position.val < state.trace.intervals.length
    · let oldPosition : Fin state.trace.intervals.length := ⟨position.val, hold⟩
      have hentry :
          (appendTargetViewedState input initialCache output finalCache view state).trace.intervals.get
              position = state.trace.intervals.get oldPosition := by
        have hget :
            (appendTargetViewedState input initialCache output finalCache view state).trace.intervals[
                position.val]? = state.trace.intervals[position.val]? := by
          simp only [appendTargetViewedState, fullAdversaryTraceUpdate]
          rw [List.getElem?_append_left hold]
        rw [List.getElem?_eq_getElem position.isLt,
          List.getElem?_eq_getElem hold] at hget
        exact Option.some.inj hget
      have holdCandidate : FreshTargetCandidate secretKey
          (state.trace.intervals.get oldPosition) := by
        rw [← hentry]
        exact hpositionCandidate
      have htake :
          (appendTargetViewedState input initialCache output finalCache view state).trace.intervals.take
              position.val = state.trace.intervals.take oldPosition.val := by
        change (state.trace.intervals ++
          [(⟨input, output, initialCache, finalCache⟩ : AdversaryCacheEntry)]).take position.val =
            state.trace.intervals.take position.val
        rw [List.take_append_of_le_length hold.le]
      rw [List.countPBefore_eq_countP_take, htake,
        ← List.countPBefore_eq_countP_take]
      rw [show position = ⟨oldPosition.val, by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ from Fin.ext rfl,
        targetCandidateIntervalAllowed_appendTargetViewedState_old
          configuration state input initialCache output finalCache view oldPosition]
      exact hexact.2 oldPosition holdCandidate
    · have hlastValue : position.val = state.trace.intervals.length := by
        have hlt : position.val < state.trace.intervals.length + 1 := by
          simpa [appendTargetViewedState, fullAdversaryTraceUpdate] using position.isLt
        omega
      have hposition : position = ⟨state.trace.intervals.length, by
          simp [appendTargetViewedState, fullAdversaryTraceUpdate]⟩ := Fin.ext hlastValue
      exfalso
      apply hnon
      simpa [hposition, appendTargetViewedState, fullAdversaryTraceUpdate] using
        hpositionCandidate

theorem OriginMonitorState.ReplayConsistent.directOrdinal_eq
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    {secretKey : SecretKey} {state : OriginMonitorState configuration}
    (hconsistent : state.ReplayConsistent secretKey) :
    state.directOrdinal = directIntervalCount state.viewed.trace.intervals := by
  have hordinals := replayOriginEvents_ordinals configuration secretKey
    (originReplayEvents state.viewed.trace.intervals state.viewed.views)
  have hcounts := originReplayEvents_counts state.viewed.trace.intervals state.viewed.views
  calc
    state.directOrdinal = state.replayState.directOrdinal := rfl
    _ = (replayOriginEvents configuration secretKey
        (originReplayEvents state.viewed.trace.intervals state.viewed.views)).directOrdinal :=
      congrArg OriginReplayState.directOrdinal hconsistent.2.2
    _ = OriginReplayEvents.directCount
        (originReplayEvents state.viewed.trace.intervals state.viewed.views) := hordinals.1
    _ = directIntervalCount state.viewed.trace.intervals := hcounts.1

theorem OriginMonitorState.ReplayConsistent.signerOrdinal_eq
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    {secretKey : SecretKey} {state : OriginMonitorState configuration}
    (hconsistent : state.ReplayConsistent secretKey) :
    state.signerOrdinal = signerIntervalCount state.viewed.trace.intervals := by
  have hordinals := replayOriginEvents_ordinals configuration secretKey
    (originReplayEvents state.viewed.trace.intervals state.viewed.views)
  have hcounts := originReplayEvents_counts state.viewed.trace.intervals state.viewed.views
  calc
    state.signerOrdinal = state.replayState.signerOrdinal := rfl
    _ = (replayOriginEvents configuration secretKey
        (originReplayEvents state.viewed.trace.intervals state.viewed.views)).signerOrdinal :=
      congrArg OriginReplayState.signerOrdinal hconsistent.2.2
    _ = OriginReplayEvents.signerCount
        (originReplayEvents state.viewed.trace.intervals state.viewed.views) := hordinals.2
    _ = signerIntervalCount state.viewed.trace.intervals := hcounts.2

def OriginTargetMonitorState.CandidateAllowedTraceCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (state : OriginTargetMonitorState configuration) : Prop :=
  state.origin.ReplayConsistent secretKey ∧
    CandidateAllowedExact configuration secretKey state.origin.viewed state.candidateAllowed

theorem OriginTargetMonitorState.candidateAllowedTraceCoherent_initial
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (cache : QueryCache HashSpec) :
    (OriginTargetMonitorState.initial configuration cache).CandidateAllowedTraceCoherent
      secretKey := by
  constructor
  · exact OriginMonitorState.replayConsistent_initial configuration secretKey cache
  · exact candidateAllowedExact_nil configuration secretKey cache

def OriginTargetMonitorState.CandidateTraceCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (state : OriginTargetMonitorState configuration) : Prop :=
  state.origin.ReplayConsistent secretKey ∧
    CandidateViewsExact secretKey state.origin.viewed state.candidateViews

theorem OriginTargetMonitorState.candidateTraceCoherent_initial
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (cache : QueryCache HashSpec) :
    (OriginTargetMonitorState.initial configuration cache).CandidateTraceCoherent
      secretKey := by
  constructor
  · exact OriginMonitorState.replayConsistent_initial configuration secretKey cache
  · exact candidateViewsExact_nil secretKey cache

theorem originTargetMonitoredAdversaryImpl_query_candidateTraceCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (result : (OracleWorld + SigningSpec).Range input ×
      OriginTargetMonitorState configuration)
    (hcoherent : state.CandidateTraceCoherent secretKey)
    (hmem : result ∈ support
      ((originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
        state)) : result.2.CandidateTraceCoherent secretKey := by
  classical
  have horiginMem : (result.1, result.2.origin) ∈ support
      ((originMonitoredAdversaryImpl configuration secretKey input).run state.origin) := by
    rw [← originTargetMonitoredAdversaryImpl_query_projection
      configuration secretKey targetOrdinal input state, support_map]
    exact ⟨result, hmem, rfl⟩
  have hreplay := originMonitoredAdversaryImpl_query_replayConsistent
    configuration secretKey input state.origin (result.1, result.2.origin)
      hcoherent.1 horiginMem
  refine ⟨hreplay, ?_⟩
  have hvalid := hcoherent.1.1
  have hconsistent := hcoherent.1.2.1
  have hexact := hcoherent.2
  cases input with
  | inl worldInput =>
      rw [originTargetMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, origin⟩, horigin, hpure⟩ := hmem
      rw [originMonitoredAdversaryImpl] at horigin
      simp only [StateT.run, mem_support_bind_iff] at horigin
      obtain ⟨⟨originOutput, finalCache⟩, hquery, horiginPure⟩ := horigin
      cases worldInput with
      | inl uniformInput =>
          simp only [support_pure, Set.mem_singleton_iff] at horiginPure hpure
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj horiginPure
          have hstateEq := congrArg Prod.snd hpure
          rw [hstateEq]
          change CandidateViewsExact secretKey
            (appendTargetViewedState (.inl (.inl uniformInput))
              state.origin.viewed.cache output finalCache none state.origin.viewed)
            state.candidateViews
          exact candidateViewsExact_append_noncandidate secretKey state.origin.viewed
            hvalid hconsistent state.candidateViews hexact _ _ _ _ _
              (freshTargetCandidate_uniform_false secretKey uniformInput output
                state.origin.viewed.cache finalCache)
      | inr hashInput =>
          simp only [support_pure, Set.mem_singleton_iff] at horiginPure
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj horiginPure
          have hquery' : (output, finalCache) ∈
              support ((randomOracle hashInput).run state.origin.viewed.cache) := hquery
          by_cases hfresh : state.origin.viewed.cache hashInput = none
          · simp only [hfresh, if_true, support_pure, Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            change CandidateViewsExact secretKey
              (appendTargetViewedState (.inl (.inr hashInput))
                state.origin.viewed.cache output finalCache none state.origin.viewed)
              (state.candidateViews ++ [hashOutputFewTimeView output])
            apply candidateViewsExact_append_candidate secretKey state.origin.viewed
              hvalid hconsistent state.candidateViews hexact
            · exact (freshTargetCandidate_direct_iff secretKey hashInput output
                state.origin.viewed.cache finalCache hquery').mpr hfresh
            simpa using targetCandidateIntervalView_appendTargetViewedState_last
              secretKey state.origin.viewed hvalid hconsistent (.inl (.inr hashInput))
                state.origin.viewed.cache output finalCache none
          · simp only [hfresh, if_false, support_pure, Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            change CandidateViewsExact secretKey
              (appendTargetViewedState (.inl (.inr hashInput))
                state.origin.viewed.cache output finalCache none state.origin.viewed)
              state.candidateViews
            apply candidateViewsExact_append_noncandidate secretKey state.origin.viewed
              hvalid hconsistent state.candidateViews hexact
            exact fun hcandidate => hfresh
              ((freshTargetCandidate_direct_iff secretKey hashInput output
                state.origin.viewed.cache finalCache hquery').mp hcandidate)
  | inr request =>
      rw [originTargetMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨targetRun, htargetRun, hpure⟩ := hmem
      have hcand := freshTargetCandidate_signer_iff secretKey request
        state.origin.viewed.cache targetRun htargetRun
      cases hselection : targetRun.1.2 with
      | none =>
          simp only [hselection, targetSignerResultView, Option.map,
            support_pure, Set.mem_singleton_iff] at hpure
          have hstateEq := congrArg Prod.snd hpure
          rw [hstateEq]
          change CandidateViewsExact secretKey
            (appendTargetViewedState (.inr request) state.origin.viewed.cache
              targetRun.1.1 targetRun.2 none state.origin.viewed)
            state.candidateViews
          apply candidateViewsExact_append_noncandidate secretKey state.origin.viewed
            hvalid hconsistent state.candidateViews hexact
          intro hcandidate
          obtain ⟨selectedInput, view, hsome, _⟩ := hcand.mp hcandidate
          rw [hselection] at hsome
          simp at hsome
      | some selection =>
          rcases selection with ⟨selectedInput, view⟩
          by_cases hfresh : state.origin.viewed.cache selectedInput = none
          · simp only [hselection, targetSignerResultView, Option.map, hfresh,
              if_true, support_pure,
              Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            change CandidateViewsExact secretKey
              (appendTargetViewedState (.inr request) state.origin.viewed.cache
                targetRun.1.1 targetRun.2 (some view) state.origin.viewed)
              (state.candidateViews ++ [view])
            apply candidateViewsExact_append_candidate secretKey state.origin.viewed
              hvalid hconsistent state.candidateViews hexact
            · exact hcand.mpr ⟨selectedInput, view, hselection, hfresh⟩
            simpa using targetCandidateIntervalView_appendTargetViewedState_last
              secretKey state.origin.viewed hvalid hconsistent (.inr request)
                state.origin.viewed.cache targetRun.1.1 targetRun.2 (some view)
          · simp only [hselection, targetSignerResultView, Option.map, hfresh,
              if_false, support_pure,
              Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            change CandidateViewsExact secretKey
              (appendTargetViewedState (.inr request) state.origin.viewed.cache
                targetRun.1.1 targetRun.2 (some view) state.origin.viewed)
              state.candidateViews
            apply candidateViewsExact_append_noncandidate secretKey state.origin.viewed
              hvalid hconsistent state.candidateViews hexact
            intro hcandidate
            obtain ⟨input, foundView, hsome, hmiss⟩ := hcand.mp hcandidate
            have hfields := Prod.mk.inj (Option.some.inj (hselection.symm.trans hsome))
            apply hfresh
            rw [hfields.1]
            exact hmiss

theorem originTargetMonitoredAdversaryImpl_candidateTraceCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (result : α × OriginTargetMonitorState configuration)
    (hcoherent : initialState.CandidateTraceCoherent secretKey)
    (hmem : result ∈ support
      ((simulateQ
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState)) : result.2.CandidateTraceCoherent secretKey := by
  exact OracleComp.simulateQ_run_preservesInv
    (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
    (OriginTargetMonitorState.CandidateTraceCoherent secretKey)
    (by
      intro input state hstate queryResult hquery
      exact originTargetMonitoredAdversaryImpl_query_candidateTraceCoherent
        configuration secretKey targetOrdinal input state queryResult hstate hquery)
    computation initialState hcoherent result hmem

theorem originTargetMonitoredAdversaryImpl_query_candidateAllowedTraceCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (result : (OracleWorld + SigningSpec).Range input ×
      OriginTargetMonitorState configuration)
    (hcoherent : state.CandidateAllowedTraceCoherent secretKey)
    (hmem : result ∈ support
      ((originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run
        state)) : result.2.CandidateAllowedTraceCoherent secretKey := by
  classical
  have horiginMem : (result.1, result.2.origin) ∈ support
      ((originMonitoredAdversaryImpl configuration secretKey input).run state.origin) := by
    rw [← originTargetMonitoredAdversaryImpl_query_projection
      configuration secretKey targetOrdinal input state, support_map]
    exact ⟨result, hmem, rfl⟩
  have hreplay := originMonitoredAdversaryImpl_query_replayConsistent
    configuration secretKey input state.origin (result.1, result.2.origin)
      hcoherent.1 horiginMem
  refine ⟨hreplay, ?_⟩
  have hexact := hcoherent.2
  cases input with
  | inl worldInput =>
      rw [originTargetMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, origin⟩, horigin, hpure⟩ := hmem
      rw [originMonitoredAdversaryImpl] at horigin
      simp only [StateT.run, mem_support_bind_iff] at horigin
      obtain ⟨⟨originOutput, finalCache⟩, hquery, horiginPure⟩ := horigin
      cases worldInput with
      | inl uniformInput =>
          simp only [support_pure, Set.mem_singleton_iff] at horiginPure hpure
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj horiginPure
          have hstateEq := congrArg Prod.snd hpure
          rw [hstateEq]
          change CandidateAllowedExact configuration secretKey
            (appendTargetViewedState (.inl (.inl uniformInput))
              state.origin.viewed.cache output finalCache none state.origin.viewed)
            state.candidateAllowed
          exact candidateAllowedExact_append_noncandidate configuration secretKey
            state.origin.viewed state.candidateAllowed hexact _ _ _ _ _
              (freshTargetCandidate_uniform_false secretKey uniformInput output
                state.origin.viewed.cache finalCache)
      | inr hashInput =>
          simp only [support_pure, Set.mem_singleton_iff] at horiginPure
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj horiginPure
          have hquery' : (output, finalCache) ∈
              support ((randomOracle hashInput).run state.origin.viewed.cache) := hquery
          by_cases hfresh : state.origin.viewed.cache hashInput = none
          · simp only [hfresh, if_true, support_pure, Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            change CandidateAllowedExact configuration secretKey
              (appendTargetViewedState (.inl (.inr hashInput))
                state.origin.viewed.cache output finalCache none state.origin.viewed)
              (state.candidateAllowed ++
                [decide (configuration.sourceAt? state.origin.directOrdinal = none)])
            apply candidateAllowedExact_append_candidate configuration secretKey
              state.origin.viewed state.candidateAllowed hexact
            · exact (freshTargetCandidate_direct_iff secretKey hashInput output
                state.origin.viewed.cache finalCache hquery').mpr hfresh
            simpa [hcoherent.1.directOrdinal_eq] using
              targetCandidateIntervalAllowed_appendTargetViewedState_last
                configuration state.origin.viewed (.inl (.inr hashInput))
                  state.origin.viewed.cache output finalCache none
          · simp only [hfresh, if_false, support_pure, Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            change CandidateAllowedExact configuration secretKey
              (appendTargetViewedState (.inl (.inr hashInput))
                state.origin.viewed.cache output finalCache none state.origin.viewed)
              state.candidateAllowed
            apply candidateAllowedExact_append_noncandidate configuration secretKey
              state.origin.viewed state.candidateAllowed hexact
            exact fun hcandidate => hfresh
              ((freshTargetCandidate_direct_iff secretKey hashInput output
                state.origin.viewed.cache finalCache hquery').mp hcandidate)
  | inr request =>
      rw [originTargetMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨targetRun, htargetRun, hpure⟩ := hmem
      have hcand := freshTargetCandidate_signer_iff secretKey request
        state.origin.viewed.cache targetRun htargetRun
      cases hselection : targetRun.1.2 with
      | none =>
          simp only [hselection, targetSignerResultView, Option.map,
            support_pure, Set.mem_singleton_iff] at hpure
          have hstateEq := congrArg Prod.snd hpure
          rw [hstateEq]
          change CandidateAllowedExact configuration secretKey
            (appendTargetViewedState (.inr request) state.origin.viewed.cache
              targetRun.1.1 targetRun.2 none state.origin.viewed)
            state.candidateAllowed
          apply candidateAllowedExact_append_noncandidate configuration secretKey
            state.origin.viewed state.candidateAllowed hexact
          intro hcandidate
          obtain ⟨selectedInput, view, hsome, _⟩ := hcand.mp hcandidate
          rw [hselection] at hsome
          simp at hsome
      | some selection =>
          rcases selection with ⟨selectedInput, view⟩
          by_cases hfresh : state.origin.viewed.cache selectedInput = none
          · simp only [hselection, targetSignerResultView, Option.map, hfresh,
              if_true, support_pure, Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            change CandidateAllowedExact configuration secretKey
              (appendTargetViewedState (.inr request) state.origin.viewed.cache
                targetRun.1.1 targetRun.2 (some view) state.origin.viewed)
              (state.candidateAllowed ++
                [decide (pattern.selectedAt? state.origin.signerOrdinal = none)])
            apply candidateAllowedExact_append_candidate configuration secretKey
              state.origin.viewed state.candidateAllowed hexact
            · exact hcand.mpr ⟨selectedInput, view, hselection, hfresh⟩
            simpa [hcoherent.1.signerOrdinal_eq] using
              targetCandidateIntervalAllowed_appendTargetViewedState_last
                configuration state.origin.viewed (.inr request)
                  state.origin.viewed.cache targetRun.1.1 targetRun.2 (some view)
          · simp only [hselection, targetSignerResultView, Option.map, hfresh,
              if_false, support_pure, Set.mem_singleton_iff] at hpure
            have hstateEq := congrArg Prod.snd hpure
            rw [hstateEq]
            change CandidateAllowedExact configuration secretKey
              (appendTargetViewedState (.inr request) state.origin.viewed.cache
                targetRun.1.1 targetRun.2 (some view) state.origin.viewed)
              state.candidateAllowed
            apply candidateAllowedExact_append_noncandidate configuration secretKey
              state.origin.viewed state.candidateAllowed hexact
            intro hcandidate
            obtain ⟨input, foundView, hsome, hmiss⟩ := hcand.mp hcandidate
            have hfields := Prod.mk.inj (Option.some.inj (hselection.symm.trans hsome))
            apply hfresh
            rw [hfields.1]
            exact hmiss

theorem originTargetMonitoredAdversaryImpl_candidateAllowedTraceCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (result : α × OriginTargetMonitorState configuration)
    (hcoherent : initialState.CandidateAllowedTraceCoherent secretKey)
    (hmem : result ∈ support
      ((simulateQ
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState)) :
    result.2.CandidateAllowedTraceCoherent secretKey := by
  exact OracleComp.simulateQ_run_preservesInv
    (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
    (OriginTargetMonitorState.CandidateAllowedTraceCoherent secretKey)
    (by
      intro input state hstate queryResult hquery
      exact originTargetMonitoredAdversaryImpl_query_candidateAllowedTraceCoherent
        configuration secretKey targetOrdinal input state queryResult hstate hquery)
    computation initialState hcoherent result hmem

theorem OriginTargetMonitorState.CandidateTraceCoherent.candidateCountCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    {secretKey : SecretKey} {state : OriginTargetMonitorState configuration}
    (hcoherent : state.CandidateTraceCoherent secretKey)
    (hviews : state.candidateOrdinal = state.candidateViews.length) :
    state.CandidateCountCoherent secretKey := by
  rw [OriginTargetMonitorState.CandidateCountCoherent, hviews,
    hcoherent.2.2.1]

theorem OriginTargetMonitorState.targetView_eq_candidateInterval
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (state : OriginTargetMonitorState configuration)
    (position : Fin state.origin.viewed.trace.intervals.length)
    (hcandidate : FreshTargetCandidate secretKey
      (state.origin.viewed.trace.intervals.get position))
    (hviews : state.CandidateViewsCoherent
      (state.origin.viewed.trace.intervals.countPBefore
        (fun entry => decide (FreshTargetCandidate secretKey entry)) position.val))
    (hexact : CandidateViewsExact secretKey state.origin.viewed state.candidateViews) :
    state.targetView = some (targetCandidateIntervalView state.origin.viewed position) := by
  rw [hviews.2]
  exact hexact.2.2 position hcandidate

theorem OriginTargetMonitorState.valid_eq_candidateIntervalAllowed
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (state : OriginTargetMonitorState configuration)
    (position : Fin state.origin.viewed.trace.intervals.length)
    (hcandidate : FreshTargetCandidate secretKey
      (state.origin.viewed.trace.intervals.get position))
    (hfixed : state.CandidateAllowedCoherent
      (state.origin.viewed.trace.intervals.countPBefore
        (fun entry => decide (FreshTargetCandidate secretKey entry)) position.val))
    (hexact : CandidateAllowedExact configuration secretKey
      state.origin.viewed state.candidateAllowed) :
    state.valid = targetCandidateIntervalAllowed configuration state.origin.viewed position := by
  rw [hfixed.2, hexact.2 position hcandidate]
  rfl

theorem ProperFewTimeLeak.direct_target_not_configured_source
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (hproper : ProperFewTimeLeak f cache secretKey signingLog index targetLeaves)
    (forgery : Forgery) (forgedDigest : MessageDigest)
    (hforgedDigest : evalWithAnswerFn f
      (messageDigest secretKey.parameter secretKey.root forgery.message
        forgery.signature.randomness) = forgedDigest)
    (hleaves : targetLeaves = digestLeaves forgedDigest)
    {q limit : Nat} (hle : signingLog.length ≤ limit)
    (configuration : OriginConfiguration (hproper.1.cover.pattern.pad hle) q)
    (trace : FullAdversaryTrace)
    (hlog : trace.signing.toSigningLog = signingLog)
    (hrealized : configuration.PaddedRealizedBy hproper.1.cover hle trace hlog)
    (hvalid : trace.ValidIntervals secretKey)
    (position : Fin trace.intervals.length) (output : HashOutput)
    (initialCache finalCache : QueryCache HashSpec)
    (hinterval : trace.intervals.get position =
      ⟨.inl (.inr (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root forgery.message
          forgery.signature.randomness))), output, initialCache, finalCache⟩) :
    configuration.sourceAt?
      (directIntervalCount (trace.intervals.take position.val)) = none := by
  classical
  cases hsource : configuration.sourceAt?
      (directIntervalCount (trace.intervals.take position.val)) with
  | none => rfl
  | some selected =>
      exfalso
      have hgood := configuration.paddedRealized_direct_good hrealized hvalid position
        (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root forgery.message
            forgery.signature.randomness))
        output initialCache finalCache hinterval
        (directIntervalCount (trace.intervals.take position.val)) rfl selected hsource
      have hne := hproper.forged_digest_input_ne_entryDigestInput forgery forgedDigest
        hforgedDigest hleaves (hproper.1.cover.paddedEntry hle selected.1)
      apply hne
      simpa only [FewTimeCover.paddedExpectedInputs] using hgood.1

theorem FewTimeCover.failed_signer_not_selectedAt
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (state : ViewedFullTraceState)
    (hlog : state.trace.signing.toSigningLog = signingLog)
    (hvalid : state.ValidViews secretKey) (hconsistent : state.trace.Consistent)
    (hcaches : state.trace.signing.CachesLe cache) (hf : cache.AgreesWithFn f)
    {limit : Nat} (hle : signingLog.length ≤ limit)
    (position : Fin state.trace.intervals.length) (request : SignRequest)
    (initialCache finalCache : QueryCache HashSpec)
    (hinterval : state.trace.intervals.get position =
      ⟨.inr request, none, initialCache, finalCache⟩) :
    (cover.pattern.pad hle).selectedAt?
      (signerIntervalCount (state.trace.intervals.take position.val)) = none := by
  classical
  cases hselected : (cover.pattern.pad hle).selectedAt?
      (signerIntervalCount (state.trace.intervals.take position.val)) with
  | none => rfl
  | some selected =>
      exfalso
      have hrank : signerIntervalCount (state.trace.intervals.take position.val) =
          selected.1.val :=
        ((cover.pattern.pad hle).selectedAt?_eq_some_iff _ selected).mp hselected |>.symm
      have hsigner := cover.originReplayEvents_get_signer state hlog hvalid hconsistent
        hcaches hf hle selected position request none initialCache finalCache hinterval hrank
      let entry := cover.paddedEntry hle selected
      have hfields := cover.cacheEntry_request_signature state.trace.signing hlog entry
      have hsignature := congrArg SigningCacheEntry.signature hsigner.2
      change none = (cover.cacheEntry state.trace.signing hlog entry).signature at hsignature
      rw [hfields.2] at hsignature
      simp at hsignature

theorem ProperFewTimeLeak.signer_target_not_selectedAt
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (hproper : ProperFewTimeLeak f cache secretKey signingLog index targetLeaves)
    (state : ViewedFullTraceState)
    (hlog : state.trace.signing.toSigningLog = signingLog)
    (hvalidViews : state.ValidViews secretKey)
    (hconsistent : state.trace.Consistent)
    (hvalidRuns : state.trace.signing.ValidRuns secretKey)
    (hcaches : state.trace.signing.CachesLe cache) (hf : cache.AgreesWithFn f)
    {limit : Nat} (hle : signingLog.length ≤ limit)
    (position : Fin state.trace.intervals.length)
    (request : SignRequest) (signature : Option Signature)
    (initialCache finalCache : QueryCache HashSpec)
    (hinterval : state.trace.intervals.get position =
      ⟨.inr request, signature, initialCache, finalCache⟩)
    (targetPayload : HashInput) (output : HashOutput)
    (hbefore : initialCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = none)
    (hafter : finalCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = some output)
    (houtput : signAttemptResultOfOutput output = some (index, targetLeaves)) :
    (hproper.1.cover.pattern.pad hle).selectedAt?
      (signerIntervalCount (state.trace.intervals.take position.val)) = none := by
  have hsignature := hproper.signer_target_signature_eq_none state hlog hvalidViews
    hconsistent hvalidRuns hcaches hf position request signature initialCache finalCache
      hinterval targetPayload output hbefore hafter houtput
  subst signature
  exact hproper.1.cover.failed_signer_not_selectedAt state hlog hvalidViews hconsistent
    hcaches hf hle position request initialCache finalCache hinterval

theorem ProperFewTimeLeak.target_source_interval_allowed
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (hproper : ProperFewTimeLeak f cache secretKey signingLog index targetLeaves)
    (forgery : Forgery) (forgedDigest : MessageDigest)
    (hforgedDigest : evalWithAnswerFn f
      (messageDigest secretKey.parameter secretKey.root forgery.message
        forgery.signature.randomness) = forgedDigest)
    (hleaves : targetLeaves = digestLeaves forgedDigest)
    (state : ViewedFullTraceState)
    (hlog : state.trace.signing.toSigningLog = signingLog)
    (hvalidViews : state.ValidViews secretKey)
    (hconsistent : state.trace.Consistent)
    (hvalidRuns : state.trace.signing.ValidRuns secretKey)
    (hcaches : state.trace.signing.CachesLe cache) (hf : cache.AgreesWithFn f)
    {q limit : Nat} (hle : signingLog.length ≤ limit)
    (configuration : OriginConfiguration (hproper.1.cover.pattern.pad hle) q)
    (hrealized : configuration.PaddedRealizedBy hproper.1.cover hle state.trace hlog)
    (hvalidIntervals : state.trace.ValidIntervals secretKey)
    (position : Fin state.trace.intervals.length) (output : HashOutput)
    (hbefore : (state.trace.intervals.get position).initialCache
      (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root forgery.message
          forgery.signature.randomness)) = none)
    (hafter : (state.trace.intervals.get position).finalCache
      (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root forgery.message
          forgery.signature.randomness)) = some output)
    (houtput : signAttemptResultOfOutput output = some (index, targetLeaves))
    (hkind : (state.trace.intervals.get position).input = .inl (.inr
        (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root forgery.message
            forgery.signature.randomness))) ∨
      ∃ request, (state.trace.intervals.get position).input = .inr request) :
    targetCandidateIntervalAllowed configuration state position = true := by
  let entry := state.trace.intervals.get position
  have hentry : state.trace.intervals.get position = entry := rfl
  rcases entry with ⟨entryInput, entryOutput, initialCache, finalCache⟩
  rw [hentry] at hbefore hafter hkind
  change initialCache _ = none at hbefore
  change finalCache _ = some output at hafter
  rcases hkind with hdirect | ⟨request, hsigner⟩
  · change entryInput = .inl (.inr _) at hdirect
    subst entryInput
    have hnone := hproper.direct_target_not_configured_source forgery forgedDigest
      hforgedDigest hleaves hle configuration state.trace hlog hrealized hvalidIntervals
        position entryOutput initialCache finalCache hentry
    have hinputElem : state.trace.intervals[position.val].input = .inl (.inr
        (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root forgery.message
            forgery.signature.randomness))) := by
      simpa only [List.get_eq_getElem] using
        congrArg AdversaryCacheEntry.input hentry
    simp [targetCandidateIntervalAllowed, hinputElem, hnone]
  · change entryInput = .inr request at hsigner
    subst entryInput
    have hnone := hproper.signer_target_not_selectedAt state hlog hvalidViews hconsistent
      hvalidRuns hcaches hf hle position request entryOutput initialCache finalCache hentry
        (messageDigestPayload secretKey.root forgery.message
          forgery.signature.randomness) output hbefore hafter houtput
    have hinputElem : state.trace.intervals[position.val].input = .inr request := by
      simpa only [List.get_eq_getElem] using
        congrArg AdversaryCacheEntry.input hentry
    simp [targetCandidateIntervalAllowed, hinputElem, hnone]

theorem gameAfterSecretsWithViewTrace_target_source_candidate
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.cache.AgreesWithFn f)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest parameter result.1.1 result.1.2.1.message
        result.1.2.1.signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (source : Fin result.2.trace.intervals.length)
    (hsourceInitial : (result.2.trace.intervals.get source).initialCache
      (tweakableHashInput parameter .message
        (messageDigestPayload result.1.1 result.1.2.1.message
          result.1.2.1.signature.randomness)) = none)
    (hsourceFinal : (result.2.trace.intervals.get source).finalCache
      (tweakableHashInput parameter .message
        (messageDigestPayload result.1.1 result.1.2.1.message
          result.1.2.1.signature.randomness)) ≠ none)
    (hkind : (result.2.trace.intervals.get source).input = .inl (.inr
        (tweakableHashInput parameter .message
          (messageDigestPayload result.1.1 result.1.2.1.message
            result.1.2.1.signature.randomness))) ∨
      ∃ request, (result.2.trace.intervals.get source).input = .inr request) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    ∃ output,
      FreshTargetCandidate secretKey (result.2.trace.intervals.get source)
        ∧ targetCandidateIntervalView result.2 source =
          fewTimeTargetView (digestIndex digest) (digestLeaves digest)
        ∧ (result.2.trace.intervals.get source).finalCache
          (tweakableHashInput parameter .message
            (messageDigestPayload result.1.1 result.1.2.1.message
              result.1.2.1.signature.randomness)) = some output
        ∧ signAttemptResultOfOutput output =
          some (digestIndex digest, digestLeaves digest) := by
  let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
  let targetPayload := messageDigestPayload result.1.1 result.1.2.1.message
    result.1.2.1.signature.randomness
  let input := tweakableHashInput parameter .message targetPayload
  obtain ⟨output, hsourceOutput⟩ := Option.ne_none_iff_exists'.mp hsourceFinal
  have hbase : (result.1, result.2.base) ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
    rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
      support_map]
    exact ⟨result, hresult, rfl⟩
  have hintervals := gameAfterSecretsWithFullTrace_support_interval_invariants adversary
    parameter otsSecret ftsSecret (result.1, result.2.base) hbase
  have hvalidIntervals := gameAfterSecretsWithFullTrace_support_validIntervals adversary
    parameter otsSecret ftsSecret (result.1, result.2.base) hbase
  have hvalidViews := gameAfterSecretsWithViewTrace_support_validViews adversary parameter
    otsSecret ftsSecret result hresult
  let entry := result.2.trace.intervals.get source
  have hentry : result.2.trace.intervals.get source = entry := rfl
  have hsourceLe : entry.finalCache ≤ result.2.cache :=
    (hintervals.2.1 entry (List.get_mem _ source)).2
  have hcachedFinal : result.2.cache input = some output := by
    exact hsourceLe (by simpa only [entry, input] using hsourceOutput)
  have hanswer : f input = output := hf hcachedFinal
  have hdigestOutput : truncateMessageDigest output = digest := by
    simpa only [messageDigest, oracleHash, evalWithAnswerFn_bind, evalWithAnswerFn_query,
      evalWithAnswerFn_pure, input, targetPayload, hanswer] using hdigest
  have hattempt : signAttemptResultOfOutput output =
      some (digestIndex digest, digestLeaves digest) := by
    simp [signAttemptResultOfOutput, hdigestOutput, hadmissible]
  have htargetOutput : hashOutputFewTimeView output =
      fewTimeTargetView (digestIndex digest) (digestLeaves digest) := by
    simp [hashOutputFewTimeView, fewTimeTargetView, hdigestOutput]
  have hsourceCandidate : FreshTargetCandidate secretKey entry :=
    freshTargetCandidate_of_message_transition secretKey entry targetPayload
      (hvalidIntervals entry (List.get_mem _ source))
      (by simpa only [secretKey, input, entry] using hsourceInitial)
      (by simpa only [secretKey, input, entry, hsourceOutput])
      (by
        intro sourceOutput hsourceOutput'
        have hcached := hsourceLe (by simpa only [input] using hsourceOutput')
        rw [hcachedFinal] at hcached
        have hsourceOutputEq : sourceOutput = output :=
          (Option.some.inj hcached).symm
        rw [hsourceOutputEq, hattempt]
        simp)
      (by simpa only [secretKey, input, entry] using hkind)
  refine ⟨output, by simpa only [entry] using hsourceCandidate, ?_,
    by simpa only [input] using hsourceOutput, hattempt⟩
  rcases hkind with hdirect | ⟨request, hsigner⟩
  · rcases entry with ⟨entryInput, entryOutput, initialCache, finalCache⟩
    change (result.2.trace.intervals.get source).input = .inl (.inr input) at hdirect
    have hentryInput := congrArg AdversaryCacheEntry.input hentry
    rw [hentryInput] at hdirect
    rcases entryInput with worldInput | sourceRequest
    · rcases worldInput with uniformInput | directInput
      · simp at hdirect
      · simp only [Sum.inl.injEq, Sum.inr.injEq] at hdirect
        subst directInput
        rw [hentry] at hsourceOutput
        change finalCache input = some output at hsourceOutput
        have hvalidEntry := hvalidIntervals
          (⟨.inl (.inr input), entryOutput, initialCache, finalCache⟩ :
            AdversaryCacheEntry) (by rw [← hentry]; exact List.get_mem _ source)
        have hdirectRun : (entryOutput, finalCache) ∈ support
            ((randomOracle input).run initialCache) := hvalidEntry
        have hdirectCached : finalCache input = some entryOutput :=
          randomOracle_run_output_cached input initialCache finalCache entryOutput hdirectRun
        have hentryOutputEq : entryOutput = output := by
          rw [hsourceOutput] at hdirectCached
          exact (Option.some.inj hdirectCached).symm
        rw [targetCandidateIntervalView_direct result.2 source input entryOutput
          initialCache finalCache hentry, hentryOutputEq]
        exact htargetOutput
    · simp at hdirect
  · rcases entry with ⟨entryInput, entryOutput, initialCache, finalCache⟩
    change (result.2.trace.intervals.get source).input = .inr request at hsigner
    have hentryInput := congrArg AdversaryCacheEntry.input hentry
    rw [hentryInput] at hsigner
    rcases entryInput with worldInput | sourceRequest
    · simp at hsigner
    · simp only [Sum.inr.injEq] at hsigner
      subst sourceRequest
      rw [hentry] at hsourceInitial hsourceOutput
      change initialCache input = none at hsourceInitial
      change finalCache input = some output at hsourceOutput
      have hstored := ViewedFullTraceState.ValidViews.signer_interval_fresh_admissible_view
        hvalidViews hintervals.1 source request entryOutput initialCache finalCache
        hentry targetPayload output (digestIndex digest) (digestLeaves digest)
        (by simpa only [secretKey, input] using hsourceInitial)
        (by simpa only [secretKey, input] using hsourceOutput) hattempt
      rw [targetCandidateIntervalView_signer result.2 source request entryOutput
        initialCache finalCache (hashOutputFewTimeView output) hentry hstored]
      exact htargetOutput

def castTracePosition
    (left right : ViewedFullTraceState) (htrace : left.trace = right.trace)
    (position : Fin left.trace.intervals.length) :
    Fin right.trace.intervals.length :=
  Fin.cast (congrArg (fun trace : FullAdversaryTrace => trace.intervals.length) htrace)
    position

theorem get_castTracePosition
    (left right : ViewedFullTraceState) (htrace : left.trace = right.trace)
    (position : Fin left.trace.intervals.length) :
    right.trace.intervals.get (castTracePosition left right htrace position) =
      left.trace.intervals.get position := by
  have hintervals : left.trace.intervals = right.trace.intervals :=
    congrArg FullAdversaryTrace.intervals htrace
  have hright : position.val < right.trace.intervals.length := by
    rw [← hintervals]
    exact position.isLt
  have hget := congrArg (fun intervals : List AdversaryCacheEntry =>
    intervals[position.val]?) hintervals
  rw [List.getElem?_eq_getElem position.isLt,
    List.getElem?_eq_getElem hright] at hget
  exact (Option.some.inj hget).symm

theorem take_castTracePosition
    (left right : ViewedFullTraceState) (htrace : left.trace = right.trace)
    (position : Fin left.trace.intervals.length) :
    right.trace.intervals.take (castTracePosition left right htrace position).val =
      left.trace.intervals.take position.val := by
  have hintervals : left.trace.intervals = right.trace.intervals :=
    congrArg FullAdversaryTrace.intervals htrace
  change right.trace.intervals.take position.val =
    left.trace.intervals.take position.val
  exact (congrArg (List.take position.val) hintervals).symm

theorem targetCandidateIntervalView_castTracePosition
    (left right : ViewedFullTraceState) (htrace : left.trace = right.trace)
    (hviews : left.views = right.views)
    (position : Fin left.trace.intervals.length) :
    targetCandidateIntervalView right (castTracePosition left right htrace position) =
      targetCandidateIntervalView left position := by
  simp only [targetCandidateIntervalView]
  rw [get_castTracePosition left right htrace position,
    take_castTracePosition left right htrace position, ← hviews]

theorem targetCandidateIntervalAllowed_castTracePosition
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (left right : ViewedFullTraceState) (htrace : left.trace = right.trace)
    (position : Fin left.trace.intervals.length) :
    targetCandidateIntervalAllowed configuration right
        (castTracePosition left right htrace position) =
      targetCandidateIntervalAllowed configuration left position := by
  simp only [targetCandidateIntervalAllowed]
  rw [get_castTracePosition left right htrace position,
    take_castTracePosition left right htrace position]

theorem OriginConfiguration.paddedRealized_transport
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    {cover : FewTimeCover f cache secretKey signingLog index targetLeaves}
    {q limit : Nat} {hle : signingLog.length ≤ limit}
    {configuration : OriginConfiguration (cover.pattern.pad hle) q}
    (left right : FullAdversaryTrace) (htrace : left = right)
    (hlog : left.signing.toSigningLog = signingLog)
    (hrealized : configuration.PaddedRealizedBy cover hle left hlog) :
    ∃ hlog' : right.signing.toSigningLog = signingLog,
      configuration.PaddedRealizedBy cover hle right hlog' := by
  subst right
  exact ⟨hlog, hrealized⟩

theorem OriginConfiguration.paddedRealized_target_complete_and_hit
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    {cover : FewTimeCover f cache secretKey signingLog index targetLeaves}
    {q limit : Nat} {hle : signingLog.length ≤ limit}
    {configuration : OriginConfiguration (cover.pattern.pad hle) q}
    {state : OriginTargetMonitorState configuration}
    (hlog : state.origin.viewed.trace.signing.toSigningLog = signingLog)
    (hrealized : configuration.PaddedRealizedBy cover hle
      state.origin.viewed.trace hlog)
    (hreplay : state.origin.ReplayConsistent secretKey)
    (hvalidIntervals : state.origin.viewed.trace.ValidIntervals secretKey)
    (hchronological : FullAdversaryTrace.Chronological
      state.origin.viewed.trace.intervals)
    (hcaches : state.origin.viewed.trace.signing.CachesLe cache)
    (hf : cache.AgreesWithFn f)
    (position : Fin state.origin.viewed.trace.intervals.length)
    (hcandidate : FreshTargetCandidate secretKey
      (state.origin.viewed.trace.intervals.get position))
    (hview : targetCandidateIntervalView state.origin.viewed position =
      fewTimeTargetView index targetLeaves)
    (hallowed : targetCandidateIntervalAllowed configuration
      state.origin.viewed position = true)
    (hviewsCoherent : state.CandidateViewsCoherent
      (state.origin.viewed.trace.intervals.countPBefore
        (fun entry => decide (FreshTargetCandidate secretKey entry)) position.val))
    (hviewsExact : CandidateViewsExact secretKey
      state.origin.viewed state.candidateViews)
    (hallowedCoherent : state.CandidateAllowedCoherent
      (state.origin.viewed.trace.intervals.countPBefore
        (fun entry => decide (FreshTargetCandidate secretKey entry)) position.val))
    (hallowedExact : CandidateAllowedExact configuration secretKey
      state.origin.viewed state.candidateAllowed) :
    state.Complete ∧
      ∀ target, state.targetView = some target →
        FixedFewTimePatternHit (cover.pattern.pad hle).assignment
          (state.origin.observation.views, target) := by
  have horigin := configuration.paddedRealized_complete_and_hit hlog hrealized
    hreplay hvalidIntervals hchronological hcaches hf
  have htarget := state.targetView_eq_candidateInterval secretKey position hcandidate
    hviewsCoherent hviewsExact
  rw [hview] at htarget
  have hvalid := state.valid_eq_candidateIntervalAllowed secretKey position hcandidate
    hallowedCoherent hallowedExact
  rw [hallowed] at hvalid
  constructor
  · exact ⟨hvalid, horigin.1,
      fewTimeTargetView index targetLeaves, htarget⟩
  · intro target htarget'
    have htargetEq : target = fewTimeTargetView index targetLeaves := by
      exact Option.some.inj (htarget'.symm.trans htarget)
    rw [htargetEq]
    exact horigin.2

theorem probEvent_originConfiguration_hit_eq_pattern_mul
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) :
    Pr[configuration.Hit |
      ($ᵗ configuration.Sample : ProbComp configuration.Sample)] =
      Pr[FixedFewTimePatternHit pattern.assignment |
        ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) :
          ProbComp ((pattern.selected → FewTimeView) × FewTimeView))] *
        ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ configuration.prehit.card := by
  change Pr[configuration.Hit |
    Prod.mk <$>
      ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) :
        ProbComp ((pattern.selected → FewTimeView) × FewTimeView)) <*>
      ($ᵗ BitVec (127 * configuration.prehit.card) :
        ProbComp (BitVec (127 * configuration.prehit.card)))] = _
  calc
    _ = Pr[FixedFewTimePatternHit pattern.assignment |
          ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) :
            ProbComp ((pattern.selected → FewTimeView) × FewTimeView))] *
        Pr[fun value : BitVec (127 * configuration.prehit.card) => value = 0 |
          ($ᵗ BitVec (127 * configuration.prehit.card) :
            ProbComp (BitVec (127 * configuration.prehit.card)))] := by
      apply probEvent_seq_map_eq_mul
      intro views _ activations _
      rfl
    _ = _ := by rw [probEvent_uniformOriginActivation_zero]

theorem probEvent_originTargetMonitored_complete_fixedPattern_le_ideal
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (q : Nat) (hq : q ≤ 2 ^ 120)
    (hcache : QueryCache.enncard initialCache ≤ q) :
    Pr[fun result : α × OriginTargetMonitorState configuration =>
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            FixedFewTimePatternHit pattern.assignment
              (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q |
      (simulateQ
        (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run (OriginTargetMonitorState.initial configuration initialCache)] ≤
      Pr[configuration.Hit |
        ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
  calc
    _ ≤ ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ configuration.prehit.card *
        Pr[FixedFewTimePatternHit pattern.assignment |
          ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) :
            ProbComp ((pattern.selected → FewTimeView) × FewTimeView))] :=
      probEvent_originTargetMonitored_complete_le_ideal configuration secretKey
        targetOrdinal computation initialCache
          (FixedFewTimePatternHit pattern.assignment) q hq hcache
    _ = Pr[configuration.Hit |
        ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
      rw [probEvent_originConfiguration_hit_eq_pattern_mul]
      ac_rfl

theorem probEvent_exists_fixedOrdinal_viewedEvent_le_ideal
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (q : Nat) (hq : q ≤ 2 ^ 120)
    (hcache : QueryCache.enncard initialCache ≤ q) (candidates : Nat)
    (viewedEvent : Fin candidates → α × ViewedFullTraceState → Prop)
    (himp : ∀ (candidate : Fin candidates)
      (result : α × OriginTargetMonitorState configuration),
      result ∈ support
        ((simulateQ
          (originTargetMonitoredAdversaryImpl configuration secretKey candidate.val)
          computation).run (OriginTargetMonitorState.initial configuration initialCache)) →
      viewedEvent candidate (result.1, result.2.origin.viewed) →
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            FixedFewTimePatternHit pattern.assignment
              (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q) :
    Pr[fun result => ∃ candidate : Fin candidates, viewedEvent candidate result |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run
          (OriginTargetMonitorState.initial configuration initialCache).origin.viewed] ≤
      candidates * Pr[configuration.Hit |
        ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
  classical
  let run := (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
    computation).run
      (OriginTargetMonitorState.initial configuration initialCache).origin.viewed
  calc
    Pr[fun result => ∃ candidate : Fin candidates, viewedEvent candidate result | run] =
        Pr[fun result => ∃ candidate ∈ (Finset.univ : Finset (Fin candidates)),
          viewedEvent candidate result | run] := by
      congr 1
      funext result
      simp
    _ ≤ ∑ candidate ∈ (Finset.univ : Finset (Fin candidates)),
        Pr[viewedEvent candidate | run] :=
      probEvent_exists_finset_le_sum Finset.univ run viewedEvent
    _ ≤ ∑ _candidate ∈ (Finset.univ : Finset (Fin candidates)),
        Pr[configuration.Hit |
          ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
      apply Finset.sum_le_sum
      intro candidate _
      calc
        Pr[viewedEvent candidate | run] ≤
            Pr[fun result : α × OriginTargetMonitorState configuration =>
                result.2.Complete ∧
                  (∀ target, result.2.targetView = some target →
                    FixedFewTimePatternHit pattern.assignment
                      (result.2.origin.observation.views, target)) ∧
                  QueryCache.enncard result.2.origin.viewed.cache ≤ q |
              (simulateQ
                (originTargetMonitoredAdversaryImpl configuration secretKey candidate.val)
                computation).run
                  (OriginTargetMonitorState.initial configuration initialCache)] :=
          probEvent_viewed_le_originTargetMonitoredAdversaryImpl configuration secretKey
            candidate.val computation (OriginTargetMonitorState.initial configuration initialCache)
              (viewedEvent candidate) _ (himp candidate)
        _ ≤ _ := probEvent_originTargetMonitored_complete_fixedPattern_le_ideal
          configuration secretKey candidate.val computation initialCache q hq hcache
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem probEvent_exists_originConfiguration_fixedOrdinal_viewedEvent_le_idealOrigin
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 120) (hcache : QueryCache.enncard initialCache ≤ q)
    (candidates : Nat)
    (viewedEvent : ∀ (distinct : Nat) (pattern : FewTimePattern signatures distinct),
      OriginConfiguration pattern sources → Fin candidates →
        α × ViewedFullTraceState → Prop)
    (himp : ∀ (distinct : Nat) (pattern : FewTimePattern signatures distinct)
      (configuration : OriginConfiguration pattern sources) (candidate : Fin candidates)
      (result : α × OriginTargetMonitorState configuration),
      result ∈ support
        ((simulateQ
          (originTargetMonitoredAdversaryImpl configuration secretKey candidate.val)
          computation).run (OriginTargetMonitorState.initial configuration initialCache)) →
      viewedEvent distinct pattern configuration candidate
          (result.1, result.2.origin.viewed) →
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            FixedFewTimePatternHit pattern.assignment
              (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q) :
    Pr[fun result => ∃ distinct ∈ Finset.Icc 1 14,
        ∃ pattern : FewTimePattern signatures distinct,
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin candidates,
          viewedEvent distinct pattern configuration candidate result |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      candidates * idealOriginUnionBound signatures sources := by
  classical
  let run := (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
    computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩
  calc
    Pr[fun result => ∃ distinct ∈ Finset.Icc 1 14,
        ∃ pattern : FewTimePattern signatures distinct,
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin candidates,
          viewedEvent distinct pattern configuration candidate result | run] ≤
        ∑ distinct ∈ Finset.Icc 1 14,
          Pr[fun result =>
            ∃ pattern : FewTimePattern signatures distinct,
            ∃ configuration : OriginConfiguration pattern sources,
            ∃ candidate : Fin candidates,
              viewedEvent distinct pattern configuration candidate result | run] :=
      probEvent_exists_finset_le_sum (Finset.Icc 1 14) run fun distinct result =>
        ∃ pattern : FewTimePattern signatures distinct,
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin candidates,
          viewedEvent distinct pattern configuration candidate result
    _ ≤ ∑ distinct ∈ Finset.Icc 1 14,
        ∑ pattern : FewTimePattern signatures distinct,
          Pr[fun result =>
            ∃ configuration : OriginConfiguration pattern sources,
            ∃ candidate : Fin candidates,
              viewedEvent distinct pattern configuration candidate result | run] := by
      apply Finset.sum_le_sum
      intro distinct _
      calc
        _ = Pr[fun result =>
              ∃ pattern ∈ (Finset.univ : Finset (FewTimePattern signatures distinct)),
              ∃ configuration : OriginConfiguration pattern sources,
              ∃ candidate : Fin candidates,
                viewedEvent distinct pattern configuration candidate result | run] := by
            congr 1
            funext result
            simp
        _ ≤ _ := probEvent_exists_finset_le_sum Finset.univ run fun pattern result =>
          ∃ configuration : OriginConfiguration pattern sources,
          ∃ candidate : Fin candidates,
            viewedEvent distinct pattern configuration candidate result
    _ ≤ ∑ distinct ∈ Finset.Icc 1 14,
        ∑ pattern : FewTimePattern signatures distinct,
          ∑ configuration : OriginConfiguration pattern sources,
            Pr[fun result => ∃ candidate : Fin candidates,
                viewedEvent distinct pattern configuration candidate result | run] := by
      apply Finset.sum_le_sum
      intro distinct _
      apply Finset.sum_le_sum
      intro pattern _
      calc
        _ = Pr[fun result =>
              ∃ configuration ∈
                (Finset.univ : Finset (OriginConfiguration pattern sources)),
              ∃ candidate : Fin candidates,
                viewedEvent distinct pattern configuration candidate result | run] := by
            congr 1
            funext result
            simp
        _ ≤ _ := probEvent_exists_finset_le_sum Finset.univ run fun configuration result =>
          ∃ candidate : Fin candidates,
            viewedEvent distinct pattern configuration candidate result
    _ ≤ ∑ distinct ∈ Finset.Icc 1 14,
        ∑ pattern : FewTimePattern signatures distinct,
          ∑ configuration : OriginConfiguration pattern sources,
            candidates * Pr[configuration.Hit |
              ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
      apply Finset.sum_le_sum
      intro distinct _
      apply Finset.sum_le_sum
      intro pattern _
      apply Finset.sum_le_sum
      intro configuration _
      exact probEvent_exists_fixedOrdinal_viewedEvent_le_ideal configuration secretKey
        computation initialCache q hq hcache candidates
          (viewedEvent distinct pattern configuration)
          (himp distinct pattern configuration)
    _ = candidates * idealOriginUnionBound signatures sources := by
      rw [idealOriginUnionBound]
      simp_rw [← Finset.mul_sum]

def FixedOriginTargetViewedTerminal
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (q : Nat)
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (candidate : Nat)
    (result : α × ViewedFullTraceState) : Prop :=
  QueryCache.enncard result.2.cache ≤ q ∧
    ∀ monitored : α × OriginTargetMonitorState configuration,
      monitored ∈ support
        ((simulateQ
          (originTargetMonitoredAdversaryImpl configuration secretKey candidate)
          computation).run (OriginTargetMonitorState.initial configuration initialCache)) →
      (monitored.1, monitored.2.origin.viewed) = result →
      monitored.2.Complete ∧
        ∀ target, monitored.2.targetView = some target →
          FixedFewTimePatternHit pattern.assignment
            (monitored.2.origin.observation.views, target)

noncomputable instance
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (q : Nat)
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (candidate : Nat) :
    DecidablePred
      (FixedOriginTargetViewedTerminal secretKey computation initialCache q
        configuration candidate) :=
  fun result => Classical.propDecidable
    (FixedOriginTargetViewedTerminal secretKey computation initialCache q
      configuration candidate result)

theorem probEvent_exists_fixedOriginTargetViewedTerminal_le_idealOrigin
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 120) (hcache : QueryCache.enncard initialCache ≤ q) :
    Pr[fun result => ∃ distinct ∈ Finset.Icc 1 14,
        ∃ pattern : FewTimePattern signatures distinct,
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin q,
          FixedOriginTargetViewedTerminal secretKey computation initialCache q
            configuration candidate.val result |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      q * idealOriginUnionBound signatures sources := by
  apply probEvent_exists_originConfiguration_fixedOrdinal_viewedEvent_le_idealOrigin
    secretKey computation initialCache signatures sources q hq hcache q
      (fun _ _ configuration candidate =>
        FixedOriginTargetViewedTerminal secretKey computation initialCache q
          configuration candidate.val)
  intro distinct pattern configuration candidate result hresult hevent
  obtain ⟨hcacheFinal, hterminal⟩ := hevent
  have hprojection : (result.1, result.2.origin.viewed) =
      (result.1, result.2.origin.viewed) := rfl
  obtain ⟨hcomplete, hhit⟩ := hterminal result hresult hprojection
  exact ⟨hcomplete, hhit, hcacheFinal⟩

theorem OriginConfiguration.target_monitored_complete_of_projection
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.cache.AgreesWithFn f)
    (digest : MessageDigest)
    (hproper : ProperFewTimeLeak f result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.trace.signing.toSigningLog (digestIndex digest) (digestLeaves digest))
    {limit sources : Nat} (hle : result.2.trace.signing.toSigningLog.length ≤ limit)
    (configuration : OriginConfiguration (hproper.1.cover.pattern.pad hle) sources)
    (hrealized : configuration.PaddedRealizedBy hproper.1.cover hle result.2.trace rfl)
    (source : Fin result.2.trace.intervals.length)
    (hcandidate : FreshTargetCandidate
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      (result.2.trace.intervals.get source))
    (hsourceView : targetCandidateIntervalView result.2 source =
      fewTimeTargetView (digestIndex digest) (digestLeaves digest))
    (hallowed : targetCandidateIntervalAllowed configuration result.2 source = true)
    (targetOrdinal : Nat)
    (htargetOrdinal : targetOrdinal = result.2.trace.intervals.countPBefore
      (fun entry => decide (FreshTargetCandidate
        ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ entry)) source.val)
    (rootCache : QueryCache HashSpec)
    (monitored : Forgery × OriginTargetMonitorState configuration)
    (hmonitored : monitored ∈ support
      ((simulateQ
        (originTargetMonitoredAdversaryImpl configuration
          ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ targetOrdinal)
        (adversary.main ⟨result.1.1, parameter⟩)).run
          (OriginTargetMonitorState.initial configuration rootCache)))
    (htrace : result.2.trace = monitored.2.origin.viewed.trace)
    (hviews : result.2.views = monitored.2.origin.viewed.views) :
    monitored.2.Complete ∧
      ∀ target, monitored.2.targetView = some target →
        FixedFewTimePatternHit (hproper.1.cover.pattern.pad hle).assignment
          (monitored.2.origin.observation.views, target) := by
  let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
  let monitoredPosition := castTracePosition result.2 monitored.2.origin.viewed
    htrace source
  have hcandidateMonitored : FreshTargetCandidate secretKey
      (monitored.2.origin.viewed.trace.intervals.get monitoredPosition) := by
    rw [get_castTracePosition result.2 monitored.2.origin.viewed htrace source]
    exact hcandidate
  have hviewMonitored : targetCandidateIntervalView monitored.2.origin.viewed
      monitoredPosition = fewTimeTargetView (digestIndex digest) (digestLeaves digest) := by
    rw [targetCandidateIntervalView_castTracePosition result.2
      monitored.2.origin.viewed htrace hviews source]
    exact hsourceView
  have hallowedMonitored : targetCandidateIntervalAllowed configuration
      monitored.2.origin.viewed monitoredPosition = true := by
    rw [targetCandidateIntervalAllowed_castTracePosition configuration result.2
      monitored.2.origin.viewed htrace source]
    exact hallowed
  have hbase : (result.1, result.2.base) ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
    rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
      support_map]
    exact ⟨result, hresult, rfl⟩
  have hinvariants := gameAfterSecretsWithFullTrace_support_invariants adversary
    parameter otsSecret ftsSecret (result.1, result.2.base) hbase
  have hintervals := gameAfterSecretsWithFullTrace_support_interval_invariants adversary
    parameter otsSecret ftsSecret (result.1, result.2.base) hbase
  have hvalidIntervals := gameAfterSecretsWithFullTrace_support_validIntervals adversary
    parameter otsSecret ftsSecret (result.1, result.2.base) hbase
  have htraceCoherent := originTargetMonitoredAdversaryImpl_candidateTraceCoherent
    configuration secretKey targetOrdinal (adversary.main ⟨result.1.1, parameter⟩)
    (OriginTargetMonitorState.initial configuration rootCache) monitored
    (OriginTargetMonitorState.candidateTraceCoherent_initial configuration secretKey rootCache)
    hmonitored
  have hallowedTraceCoherent :=
    originTargetMonitoredAdversaryImpl_candidateAllowedTraceCoherent
      configuration secretKey targetOrdinal (adversary.main ⟨result.1.1, parameter⟩)
      (OriginTargetMonitorState.initial configuration rootCache) monitored
      (OriginTargetMonitorState.candidateAllowedTraceCoherent_initial
        configuration secretKey rootCache)
      hmonitored
  have hviewsCoherent := originTargetMonitoredAdversaryImpl_candidateViewsCoherent
    configuration secretKey targetOrdinal (adversary.main ⟨result.1.1, parameter⟩)
    (OriginTargetMonitorState.initial configuration rootCache) monitored
    (OriginTargetMonitorState.candidateViewsCoherent_initial configuration rootCache
      targetOrdinal) hmonitored
  have hallowedCoherent := originTargetMonitoredAdversaryImpl_candidateAllowedCoherent
    configuration secretKey targetOrdinal (adversary.main ⟨result.1.1, parameter⟩)
    (OriginTargetMonitorState.initial configuration rootCache) monitored
    (OriginTargetMonitorState.candidateAllowedCoherent_initial configuration rootCache
      targetOrdinal) hmonitored
  have htargetOrdinalMonitored : targetOrdinal =
      monitored.2.origin.viewed.trace.intervals.countPBefore
        (fun entry => decide (FreshTargetCandidate secretKey entry))
          monitoredPosition.val := by
    rw [htargetOrdinal]
    rw [List.countPBefore_eq_countP_take, List.countPBefore_eq_countP_take,
      take_castTracePosition result.2 monitored.2.origin.viewed htrace source]
  obtain ⟨hlogMonitored, hrealizedMonitored⟩ :=
    configuration.paddedRealized_transport result.2.trace
      monitored.2.origin.viewed.trace htrace rfl hrealized
  have hvalidIntervalsMonitored :
      monitored.2.origin.viewed.trace.ValidIntervals secretKey := by
    rw [← htrace]
    exact hvalidIntervals
  have hchronologicalMonitored : FullAdversaryTrace.Chronological
      monitored.2.origin.viewed.trace.intervals := by
    rw [← htrace]
    exact hintervals.2.2
  have hcachesMonitored : monitored.2.origin.viewed.trace.signing.CachesLe
      result.2.cache := by
    rw [← htrace]
    exact hinvariants.2.1
  exact configuration.paddedRealized_target_complete_and_hit
    hlogMonitored hrealizedMonitored htraceCoherent.1 hvalidIntervalsMonitored
    hchronologicalMonitored hcachesMonitored hf monitoredPosition hcandidateMonitored
    hviewMonitored hallowedMonitored (by rwa [← htargetOrdinalMonitored])
    htraceCoherent.2 (by rwa [← htargetOrdinalMonitored]) hallowedTraceCoherent.2

def VerifierFreshTarget (parameter : PublicParameter)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  let input := tweakableHashInput parameter .message
    (messageDigestPayload result.1.1 result.1.2.1.message
      result.1.2.1.signature.randomness)
  ∃ (adversaryCache digestCache : QueryCache HashSpec) (output : HashOutput),
    adversaryCache input = none
      ∧ (output, digestCache) ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _) (oracleHash input)).run
          adversaryCache)
      ∧ digestCache ≤ result.2.cache
      ∧ result.2.targetView = some (hashOutputFewTimeView output)

noncomputable instance (parameter : PublicParameter) :
    DecidablePred (VerifierFreshTarget parameter) :=
  fun result => Classical.propDecidable (VerifierFreshTarget parameter result)

def ViewedProperFewTimeLeakWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  ∃ (f : QueryImpl HashSpec Id) (digest : MessageDigest),
    result.2.cache.AgreesWithFn f
      ∧ SigningTranscript.Valid result.2.trace.signing.toSigningLog
      ∧ ¬SigningTranscript.Contains result.2.trace.signing.toSigningLog result.1.2.1
      ∧ evalWithAnswerFn f
          (messageDigest parameter result.1.1 result.1.2.1.message
            result.1.2.1.signature.randomness) = digest
      ∧ Admissible digest
      ∧ ProperFewTimeLeak f result.2.cache
        ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
        result.2.trace.signing.toSigningLog (digestIndex digest) (digestLeaves digest)

noncomputable instance (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    DecidablePred (ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret) :=
  fun result => Classical.propDecidable
    (ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result)

theorem gameAfterSecretsWithViewTrace_proper_target_classified_at_adversary_state
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.cache.AgreesWithFn f)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest parameter result.1.1 result.1.2.1.message
        result.1.2.1.signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hproper : ProperFewTimeLeak f result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.trace.signing.toSigningLog (digestIndex digest) (digestLeaves digest))
    (hle : result.2.trace.signing.toSigningLog.length ≤ signatureLimit)
    (rootCache : QueryCache HashSpec) (state : ViewedFullTraceState)
    (htrace : result.2.trace = state.trace) (hviews : result.2.views = state.views)
    (hstateCache : state.cache ≤ result.2.cache) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    VerifierFreshTarget parameter result ∨
      ∃ (distinct : Nat) (_ : distinct ∈ Finset.Icc 1 14)
          (pattern : FewTimePattern signatureLimit distinct)
          (configuration : OriginConfiguration pattern q) (candidate : Fin q),
        FixedOriginTargetViewedTerminal secretKey
          (adversary.main ⟨result.1.1, parameter⟩) rootCache q
            configuration candidate.val (result.1.2.1, state) := by
  classical
  let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
  let targetPayload := messageDigestPayload result.1.1 result.1.2.1.message
    result.1.2.1.signature.randomness
  let targetInput := tweakableHashInput parameter .message targetPayload
  obtain ⟨_, adversaryCache, digestCache, output, _, _, hquery, hdigestLe,
      htargetView, horigin, _⟩ :=
    gameAfterSecretsWithViewTrace_target_source_kind adversary parameter otsSecret
      ftsSecret result hresult
  rcases horigin with hverifier | ⟨source, hsourceInitial, hsourceFinal, hkind⟩
  · exact Or.inl ⟨adversaryCache, digestCache, output,
      by simpa only [targetInput, targetPayload] using hverifier,
      by simpa only [targetInput, targetPayload] using hquery, hdigestLe, htargetView⟩
  · obtain ⟨sourceOutput, hcandidate, hsourceView, hsourceOutput, hattempt⟩ :=
      gameAfterSecretsWithViewTrace_target_source_candidate adversary parameter otsSecret
        ftsSecret result hresult f hf digest hdigest hadmissible source
          (by simpa only [targetInput, targetPayload] using hsourceInitial)
          (by simpa only [targetInput, targetPayload] using hsourceFinal)
          (by simpa only [targetInput, targetPayload] using hkind)
    have hbase : (result.1, result.2.base) ∈ support
        (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
      rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
        support_map]
      exact ⟨result, hresult, rfl⟩
    obtain ⟨configuration, hrealized⟩ :=
      hproper.1.cover.exists_paddedRealized_originConfiguration_of_queryBudget
        adversary q hq parameter hparameter otsSecret hots ftsSecret hfts
          (result.1, result.2.base) hbase f hf (digestIndex digest) (digestLeaves digest)
          signatureLimit hle
    have hinvariants := gameAfterSecretsWithFullTrace_support_invariants adversary
      parameter otsSecret ftsSecret (result.1, result.2.base) hbase
    have hintervals := gameAfterSecretsWithFullTrace_support_interval_invariants adversary
      parameter otsSecret ftsSecret (result.1, result.2.base) hbase
    have hvalidIntervals := gameAfterSecretsWithFullTrace_support_validIntervals adversary
      parameter otsSecret ftsSecret (result.1, result.2.base) hbase
    have hvalidViews := gameAfterSecretsWithViewTrace_support_validViews adversary parameter
      otsSecret ftsSecret result hresult
    have hallowed : targetCandidateIntervalAllowed configuration result.2 source = true :=
      hproper.target_source_interval_allowed result.1.2.1 digest hdigest rfl result.2 rfl
        hvalidViews hintervals.1 hinvariants.1 hinvariants.2.1 hf hle configuration
          hrealized hvalidIntervals source sourceOutput
          (by simpa only [targetInput, targetPayload] using hsourceInitial)
          (by simpa only [targetInput, targetPayload] using hsourceOutput)
          hattempt (by simpa only [targetInput, targetPayload] using hkind)
    let targetOrdinal := result.2.trace.intervals.countPBefore
      (fun entry => decide (FreshTargetCandidate secretKey entry)) source.val
    have hordinalLt : targetOrdinal < freshTargetCandidateCount secretKey result.2.trace := by
      apply List.countPBefore_lt_countP_of_lt_length_of_pos
      exact decide_eq_true hcandidate
    have hcountLe : freshTargetCandidateCount secretKey result.2.trace ≤ q := by
      rw [freshTargetCandidateCount_eq_card]
      have hbound := gameAfterSecretsWithViewTrace_freshTargetCandidatePositions_card_le
        adversary q hq parameter hparameter otsSecret hots ftsSecret hfts result hresult
      exact_mod_cast hbound
    let candidate : Fin q := ⟨targetOrdinal, hordinalLt.trans_le hcountLe⟩
    have hfinalCache : QueryCache.enncard result.2.cache ≤ q :=
      gameAfterSecretsWithFullTrace_support_enncard_le adversary q hq parameter hparameter
        otsSecret hots ftsSecret hfts (result.1, result.2.base) hbase
    have hviewedCache : QueryCache.enncard state.cache ≤ q :=
      (QueryCache.enncard_mono hstateCache).trans hfinalCache
    refine Or.inr ⟨hproper.1.cover.entries.card,
      Finset.mem_Icc.2 ⟨hproper.1.cover.entries_card_pos,
        hproper.1.cover.entries_card_le_trees⟩,
      hproper.1.cover.pattern.pad hle, configuration, candidate, hviewedCache, ?_⟩
    intro monitored hmonitored heq
    have hstateEq : monitored.2.origin.viewed = state := congrArg Prod.snd heq
    have htrace' : result.2.trace = monitored.2.origin.viewed.trace := by
      rw [hstateEq]
      exact htrace
    have hviews' : result.2.views = monitored.2.origin.viewed.views := by
      rw [hstateEq]
      exact hviews
    exact configuration.target_monitored_complete_of_projection adversary parameter
      otsSecret ftsSecret result hresult f hf digest hproper hle hrealized source
      hcandidate hsourceView hallowed targetOrdinal rfl rootCache monitored hmonitored
      htrace' hviews'

theorem gameAfterSecretsWithViewTrace_proper_target_classified
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.cache.AgreesWithFn f)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest parameter result.1.1 result.1.2.1.message
        result.1.2.1.signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hproper : ProperFewTimeLeak f result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.trace.signing.toSigningLog (digestIndex digest) (digestLeaves digest))
    (hle : result.2.trace.signing.toSigningLog.length ≤ signatureLimit) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    VerifierFreshTarget parameter result ∨
      ∃ (rootCache : QueryCache HashSpec) (state : ViewedFullTraceState)
          (distinct : Nat) (_ : distinct ∈ Finset.Icc 1 14)
          (pattern : FewTimePattern signatureLimit distinct)
          (configuration : OriginConfiguration pattern q) (candidate : Fin q),
        (result.1.2.1, state) ∈ support
          ((simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
            (adversary.main ⟨result.1.1, parameter⟩)).run
              ⟨rootCache, ⟨[], [], []⟩, [], none⟩)
        ∧ FixedOriginTargetViewedTerminal secretKey
          (adversary.main ⟨result.1.1, parameter⟩) rootCache q
            configuration candidate.val (result.1.2.1, state) := by
  obtain ⟨rootCache, state, _, hadversary, htrace, hviews, hstateCache⟩ :=
    gameAfterSecretsWithViewTrace_support_adversary_state adversary parameter otsSecret
      ftsSecret result hresult
  rcases gameAfterSecretsWithViewTrace_proper_target_classified_at_adversary_state
      adversary q hq parameter hparameter otsSecret hots ftsSecret hfts result hresult
      f hf digest hdigest hadmissible hproper hle rootCache state htrace
      hviews hstateCache with hfresh | hclassified
  · exact Or.inl hfresh
  · obtain ⟨distinct, hdistinct, pattern, configuration, candidate, hterminal⟩ :=
      hclassified
    exact Or.inr ⟨rootCache, state, distinct, hdistinct, pattern, configuration,
      candidate, hadversary, hterminal⟩

theorem OracleComp.IsQueryBoundP.of_bind_left
    {ι : Type} {spec : ι → Type} {oa : OracleComp spec α}
    {ob : α → OracleComp spec β} {p : ι → Prop} [DecidablePred p] {q : Nat}
    (hbound : (oa >>= ob).IsQueryBoundP p q) : oa.IsQueryBoundP p q := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure _ => trivial
  | query_bind input continuation ih =>
      rw [bind_assoc, isQueryBoundP_query_bind_iff] at hbound
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨hbound.1, fun output => ih output (hbound.2 output)⟩

theorem probEvent_gameRestWithViewTrace_nonfresh_proper_leak_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 120)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (root : Digest) (rootCache : QueryCache HashSpec)
    (hroot : (root, rootCache) ∈ support
      ((simulateQ romImpl
        (liftM ((treeRoot parameter topLayer rootTree
          (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
            OracleComp OracleWorld Digest)).run ∅)) :
    Pr[fun rest =>
        let result : (Digest × Forgery × Bool) × ViewedFullTraceState :=
          ((root, rest.1.1, rest.1.2), rest.2)
        ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∧ ¬VerifierFreshTarget parameter result |
      gameRestWithViewTrace adversary ⟨root, parameter⟩
        ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache] ≤
      q * idealOriginUnionBound signatureLimit q := by
  classical
  let secretKey : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
  let publicKey : PublicKey := ⟨root, parameter⟩
  let initialState : ViewedFullTraceState :=
    ⟨rootCache, ⟨[], [], []⟩, [], none⟩
  let run := (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
    (adversary.main publicKey)).run initialState
  let finish : Forgery × ViewedFullTraceState →
      ProbComp ((Forgery × Bool) × ViewedFullTraceState) := fun prior => do
    let ((verified, targetView), finalCache) ←
      (simulateQ romImpl
        (liftM (verifyWithView publicKey prior.1.message prior.1.signature) :
          OracleComp OracleWorld (Bool × FewTimeView))).run prior.2.cache
    let log := prior.2.trace.signing.toSigningLog
    let verdict := decide (SigningTranscript.Valid log ∧
      ¬SigningTranscript.Contains log prior.1) && verified
    pure ((prior.1, verdict),
      ⟨finalCache, prior.2.trace, prior.2.views, some targetView⟩)
  let prefixEvent := fun prior : Forgery × ViewedFullTraceState =>
    ∃ distinct ∈ Finset.Icc 1 14,
      ∃ pattern : FewTimePattern signatureLimit distinct,
      ∃ configuration : OriginConfiguration pattern q,
      ∃ candidate : Fin q,
        FixedOriginTargetViewedTerminal secretKey (adversary.main publicKey)
          rootCache q configuration candidate.val prior
  have hgame : gameRestWithViewTrace adversary publicKey secretKey rootCache =
      run >>= finish := by
    rfl
  rw [show ⟨root, parameter⟩ = publicKey from rfl,
    show ⟨parameter, root, otsSecret, ftsSecret⟩ = secretKey from rfl, hgame]
  calc
    _ ≤ Pr[prefixEvent | run] := by
      apply probEvent_bind_le_probEvent
      intro prior hprior hnotPrefix
      rcases prior with ⟨forgery, state⟩
      apply probEvent_eq_zero
      intro rest hrest hevent
      rw [mem_support_bind_iff] at hrest
      obtain ⟨⟨⟨verified, targetView⟩, finalCache⟩, hverify, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst rest
      let result : (Digest × Forgery × Bool) × ViewedFullTraceState :=
        ((root, forgery,
          decide (SigningTranscript.Valid state.trace.signing.toSigningLog ∧
            ¬SigningTranscript.Contains state.trace.signing.toSigningLog forgery) &&
              verified),
          ⟨finalCache, state.trace, state.views, some targetView⟩)
      have hrestSupport :
          ((forgery,
              decide (SigningTranscript.Valid state.trace.signing.toSigningLog ∧
                ¬SigningTranscript.Contains state.trace.signing.toSigningLog forgery) &&
                  verified),
            ⟨finalCache, state.trace, state.views, some targetView⟩) ∈
            support (gameRestWithViewTrace adversary publicKey secretKey rootCache) := by
        rw [hgame, mem_support_bind_iff]
        refine ⟨(forgery, state), hprior, ?_⟩
        rw [mem_support_bind_iff]
        exact ⟨((verified, targetView), finalCache), hverify,
          by simp only [support_pure, Set.mem_singleton_iff]⟩
      have hresult : result ∈ support
          (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret) := by
        rw [gameAfterSecretsWithViewTrace, mem_support_bind_iff]
        refine ⟨(root, rootCache), hroot, ?_⟩
        rw [mem_support_bind_iff]
        exact ⟨_, hrestSupport, by simp [result]⟩
      obtain ⟨f, digest, hf, hvalid, _, hdigest, hadmissible, hproper⟩ := hevent.1
      have hcacheLe : state.cache ≤ finalCache :=
        simulateQ_romImpl_cache_le
          (liftM (verifyWithView publicKey forgery.message forgery.signature) :
            OracleComp OracleWorld (Bool × FewTimeView)) state.cache
              ((verified, targetView), finalCache) hverify
      rcases gameAfterSecretsWithViewTrace_proper_target_classified_at_adversary_state
          adversary q hq parameter hparameter otsSecret hots ftsSecret hfts result hresult
          f hf digest hdigest hadmissible hproper hvalid rootCache state rfl rfl hcacheLe with
        hfresh | hclassified
      · exact hevent.2 hfresh
      · obtain ⟨distinct, hdistinct, pattern, configuration, candidate, hterminal⟩ :=
          hclassified
        apply hnotPrefix
        exact ⟨distinct, hdistinct, pattern, configuration, candidate, hterminal⟩
    _ ≤ _ := probEvent_exists_fixedOriginTargetViewedTerminal_le_idealOrigin
      secretKey (adversary.main publicKey) rootCache signatureLimit q q hqMax
        (by
          have hroot' : QueryCache.enncard rootCache ≤ q := by
            have hprojected : (root, rootCache) ∈ support
                ((simulateQ romImpl
                  (liftM ((treeRoot parameter topLayer rootTree
                    (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
                      OracleComp OracleWorld Digest)).run ∅) := hroot
            have hgameBound := isQueryBoundP_gameAfterSecrets adversary q hq
              hparameter hots hfts
            rw [gameAfterSecrets] at hgameBound
            have hrootBound := OracleComp.IsQueryBoundP.of_bind_left
              (p := fun input : OracleWorld.Domain => input matches Sum.inr _) hgameBound
            have hbound := simulateQ_romImpl_enncard_le_queryBound
              (liftM ((treeRoot parameter topLayer rootTree
                (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
                  OracleComp OracleWorld Digest) q
              hrootBound
              (root, rootCache) hprojected
            exact hbound
          exact hroot')

theorem probEvent_gameAfterSecretsWithViewTrace_nonfresh_proper_leak_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 120)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result =>
        ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∧ ¬VerifierFreshTarget parameter result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      q * idealOriginUnionBound signatureLimit q := by
  rw [gameAfterSecretsWithViewTrace]
  apply probEvent_bind_le_of_forall_le
  rintro ⟨root, rootCache⟩ hroot
  let attach := fun rest : (Forgery × Bool) × ViewedFullTraceState =>
    ((root, rest.1.1, rest.1.2), rest.2)
  change Pr[fun result =>
      ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result ∧
        ¬VerifierFreshTarget parameter result |
    gameRestWithViewTrace adversary ⟨root, parameter⟩
      ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache >>= pure ∘ attach] ≤ _
  rw [probEvent_bind_pure_comp]
  exact probEvent_gameRestWithViewTrace_nonfresh_proper_leak_le adversary q hq hqMax
    parameter hparameter otsSecret hots ftsSecret hfts root rootCache hroot

theorem probEvent_gameAfterSecretsWithViewTrace_nonfresh_proper_leak_le_inv
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 120)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result =>
        ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∧ ¬VerifierFreshTarget parameter result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      q * ((2 ^ 121 : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ q * idealOriginUnionBound signatureLimit q :=
      probEvent_gameAfterSecretsWithViewTrace_nonfresh_proper_leak_le adversary q hq
        hqMax parameter hparameter otsSecret hots ftsSecret hfts
    _ ≤ _ := by
      gcongr
      exact idealOriginUnionBound_le le_rfl hqMax

theorem gameAfterSecretsWithViewTrace_proper_target_bridge
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.cache.AgreesWithFn f)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest parameter result.1.1 result.1.2.1.message
        result.1.2.1.signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hproper : ProperFewTimeLeak f result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.trace.signing.toSigningLog (digestIndex digest) (digestLeaves digest))
    {limit : Nat} (hle : result.2.trace.signing.toSigningLog.length ≤ limit)
    {sources : Nat}
    (configuration : OriginConfiguration (hproper.1.cover.pattern.pad hle) sources)
    (hrealized : configuration.PaddedRealizedBy hproper.1.cover hle result.2.trace rfl) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    VerifierFreshTarget parameter result ∨
      ∃ (targetOrdinal : Nat) (rootCache : QueryCache HashSpec)
          (monitored : Forgery × OriginTargetMonitorState configuration),
        targetOrdinal < freshTargetCandidateCount secretKey result.2.trace
          ∧ monitored ∈ support
            ((simulateQ
              (originTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
              (adversary.main ⟨result.1.1, parameter⟩)).run
                (OriginTargetMonitorState.initial configuration rootCache))
          ∧ monitored.1 = result.1.2.1
          ∧ monitored.2.Complete
          ∧ ∀ target, monitored.2.targetView = some target →
            FixedFewTimePatternHit (hproper.1.cover.pattern.pad hle).assignment
              (monitored.2.origin.observation.views, target) := by
  classical
  let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
  let targetPayload := messageDigestPayload result.1.1 result.1.2.1.message
    result.1.2.1.signature.randomness
  let targetInput := tweakableHashInput parameter .message targetPayload
  obtain ⟨rootCache₀, adversaryCache, digestCache, verifierOutput, _, _, hverify,
      hdigestLe, htargetView, horigin, _⟩ :=
    gameAfterSecretsWithViewTrace_target_source_kind adversary parameter otsSecret
      ftsSecret result hresult
  rcases horigin with hverifier | ⟨source, hsourceInitial, hsourceFinal, hkind⟩
  · exact Or.inl ⟨adversaryCache, digestCache, verifierOutput,
      by simpa only [targetInput, targetPayload] using hverifier,
      by simpa only [targetInput, targetPayload] using hverify, hdigestLe, htargetView⟩
  · obtain ⟨sourceOutput, hcandidate, hsourceView, hsourceOutput, hattempt⟩ :=
      gameAfterSecretsWithViewTrace_target_source_candidate adversary parameter otsSecret
        ftsSecret result hresult f hf digest hdigest hadmissible source
          (by simpa only [targetInput, targetPayload] using hsourceInitial)
          (by simpa only [targetInput, targetPayload] using hsourceFinal)
          (by simpa only [targetInput, targetPayload] using hkind)
    let targetOrdinal := result.2.trace.intervals.countPBefore
      (fun entry => decide (FreshTargetCandidate secretKey entry)) source.val
    obtain ⟨rootCache, monitored, _, hmonitored, hforgery, htrace, hviews, hcache⟩ :=
      gameAfterSecretsWithViewTrace_support_target_monitored_state configuration
        targetOrdinal adversary parameter otsSecret ftsSecret result hresult
    let monitoredPosition := castTracePosition result.2 monitored.2.origin.viewed
      htrace source
    have hcandidateMonitored : FreshTargetCandidate secretKey
        (monitored.2.origin.viewed.trace.intervals.get monitoredPosition) := by
      rw [get_castTracePosition result.2 monitored.2.origin.viewed htrace source]
      exact hcandidate
    have hviewMonitored : targetCandidateIntervalView monitored.2.origin.viewed
        monitoredPosition = fewTimeTargetView (digestIndex digest) (digestLeaves digest) := by
      rw [targetCandidateIntervalView_castTracePosition result.2
        monitored.2.origin.viewed htrace hviews source]
      exact hsourceView
    have hbase : (result.1, result.2.base) ∈ support
        (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
      rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
        support_map]
      exact ⟨result, hresult, rfl⟩
    have hinvariants := gameAfterSecretsWithFullTrace_support_invariants adversary
      parameter otsSecret ftsSecret (result.1, result.2.base) hbase
    have hintervals := gameAfterSecretsWithFullTrace_support_interval_invariants adversary
      parameter otsSecret ftsSecret (result.1, result.2.base) hbase
    have hvalidIntervals := gameAfterSecretsWithFullTrace_support_validIntervals adversary
      parameter otsSecret ftsSecret (result.1, result.2.base) hbase
    have hvalidViews := gameAfterSecretsWithViewTrace_support_validViews adversary parameter
      otsSecret ftsSecret result hresult
    have hallowed : targetCandidateIntervalAllowed configuration result.2 source = true :=
      hproper.target_source_interval_allowed result.1.2.1 digest hdigest rfl result.2 rfl
        hvalidViews hintervals.1 hinvariants.1 hinvariants.2.1 hf hle configuration
          hrealized hvalidIntervals source sourceOutput
          (by simpa only [targetInput, targetPayload] using hsourceInitial)
          (by simpa only [targetInput, targetPayload] using hsourceOutput)
          hattempt (by simpa only [targetInput, targetPayload] using hkind)
    have hallowedMonitored : targetCandidateIntervalAllowed configuration
        monitored.2.origin.viewed monitoredPosition = true := by
      rw [targetCandidateIntervalAllowed_castTracePosition configuration result.2
        monitored.2.origin.viewed htrace source]
      exact hallowed
    have htraceCoherent := originTargetMonitoredAdversaryImpl_candidateTraceCoherent
      configuration secretKey targetOrdinal (adversary.main ⟨result.1.1, parameter⟩)
      (OriginTargetMonitorState.initial configuration rootCache) monitored
      (OriginTargetMonitorState.candidateTraceCoherent_initial configuration secretKey rootCache)
      hmonitored
    have hallowedTraceCoherent :=
      originTargetMonitoredAdversaryImpl_candidateAllowedTraceCoherent
        configuration secretKey targetOrdinal (adversary.main ⟨result.1.1, parameter⟩)
        (OriginTargetMonitorState.initial configuration rootCache) monitored
        (OriginTargetMonitorState.candidateAllowedTraceCoherent_initial
          configuration secretKey rootCache)
        hmonitored
    have hviewsCoherent := originTargetMonitoredAdversaryImpl_candidateViewsCoherent
      configuration secretKey targetOrdinal (adversary.main ⟨result.1.1, parameter⟩)
      (OriginTargetMonitorState.initial configuration rootCache) monitored
      (OriginTargetMonitorState.candidateViewsCoherent_initial configuration rootCache
        targetOrdinal) hmonitored
    have hallowedCoherent := originTargetMonitoredAdversaryImpl_candidateAllowedCoherent
      configuration secretKey targetOrdinal (adversary.main ⟨result.1.1, parameter⟩)
      (OriginTargetMonitorState.initial configuration rootCache) monitored
      (OriginTargetMonitorState.candidateAllowedCoherent_initial configuration rootCache
        targetOrdinal) hmonitored
    have htargetOrdinal : targetOrdinal =
        monitored.2.origin.viewed.trace.intervals.countPBefore
          (fun entry => decide (FreshTargetCandidate secretKey entry))
            monitoredPosition.val := by
      change result.2.trace.intervals.countPBefore
          (fun entry => decide (FreshTargetCandidate secretKey entry)) source.val =
        monitored.2.origin.viewed.trace.intervals.countPBefore
          (fun entry => decide (FreshTargetCandidate secretKey entry)) monitoredPosition.val
      rw [List.countPBefore_eq_countP_take, List.countPBefore_eq_countP_take,
        take_castTracePosition result.2 monitored.2.origin.viewed htrace source]
    obtain ⟨hlogMonitored, hrealizedMonitored⟩ :=
      configuration.paddedRealized_transport result.2.trace
        monitored.2.origin.viewed.trace htrace rfl hrealized
    have hvalidIntervalsMonitored :
        monitored.2.origin.viewed.trace.ValidIntervals secretKey := by
      rw [← htrace]
      exact hvalidIntervals
    have hchronologicalMonitored : FullAdversaryTrace.Chronological
        monitored.2.origin.viewed.trace.intervals := by
      rw [← htrace]
      exact hintervals.2.2
    have hcachesMonitored : monitored.2.origin.viewed.trace.signing.CachesLe
        result.2.cache := by
      rw [← htrace]
      exact hinvariants.2.1
    have hterminal := configuration.paddedRealized_target_complete_and_hit
      hlogMonitored hrealizedMonitored htraceCoherent.1 hvalidIntervalsMonitored
      hchronologicalMonitored hcachesMonitored hf monitoredPosition hcandidateMonitored
      hviewMonitored hallowedMonitored (by rwa [← htargetOrdinal]) htraceCoherent.2
      (by rwa [← htargetOrdinal]) hallowedTraceCoherent.2
    have hordinalLt : targetOrdinal < freshTargetCandidateCount secretKey result.2.trace := by
      apply List.countPBefore_lt_countP_of_lt_length_of_pos
      exact decide_eq_true hcandidate
    exact Or.inr ⟨targetOrdinal, rootCache, monitored, hordinalLt, hmonitored,
      hforgery, hterminal.1, hterminal.2⟩

end Concrete

end SphincsSecurity
