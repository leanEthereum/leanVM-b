import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeTargetInvariant
import SphincsSecurity.Proof.FewTimeTargetView

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
          (FixedFewTimePatternHit pattern.assignment) q (hq.trans (by norm_num)) hcache
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

@[irreducible] def SomeFixedOriginTargetViewedTerminal
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q candidates : Nat)
    (result : α × ViewedFullTraceState) : Prop :=
  ∃ distinct ∈ Finset.Icc 1 14,
    ∃ pattern : FewTimePattern signatures distinct,
    ∃ configuration : OriginConfiguration pattern sources,
    ∃ candidate : Fin candidates,
      FixedOriginTargetViewedTerminal secretKey computation initialCache q
        configuration candidate.val result

theorem FullAdversaryTrace.CacheChain.finish_lookup_eq
    (input : HashInput) {leftStart rightStart leftFinish rightFinish : QueryCache HashSpec}
    {intervals : List AdversaryCacheEntry}
    (hstart : leftStart input = rightStart input)
    (hleft : FullAdversaryTrace.CacheChain leftStart intervals leftFinish)
    (hright : FullAdversaryTrace.CacheChain rightStart intervals rightFinish) :
    leftFinish input = rightFinish input := by
  induction intervals generalizing leftStart rightStart with
  | nil =>
      simp only [FullAdversaryTrace.CacheChain] at hleft hright
      subst leftFinish
      subst rightFinish
      exact hstart
  | cons entry rest ih =>
      obtain ⟨_, hleft⟩ := hleft
      obtain ⟨_, hright⟩ := hright
      exact ih rfl hleft hright

def VerifierFreshTarget (parameter : PublicParameter)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  let input := tweakableHashInput parameter .message
    (messageDigestPayload result.1.1 result.1.2.1.message
      result.1.2.1.signature.randomness)
  ∃ (rootCache adversaryCache digestCache : QueryCache HashSpec) (output : HashOutput),
    (∀ payload, rootCache (tweakableHashInput parameter .message payload) = none)
      ∧ FullAdversaryTrace.CacheChain rootCache result.2.trace.intervals adversaryCache
      ∧ adversaryCache input = none
      ∧ (output, digestCache) ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _) (oracleHash input)).run
          adversaryCache)
      ∧ digestCache ≤ result.2.cache
      ∧ result.2.targetView = some (hashOutputFewTimeView output)

noncomputable instance instDecidablePredProdDigestForgeryBoolViewedFullTraceStateVerifierFreshTarget (parameter : PublicParameter) :
    DecidablePred (VerifierFreshTarget parameter) :=
  fun result => Classical.propDecidable (VerifierFreshTarget parameter result)

theorem directHashQueries_append (left right : QueryLog (OracleWorld + SigningSpec)) :
    directHashQueries (left ++ right) =
      directHashQueries left ++ directHashQueries right := by
  induction left with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨input, output⟩ := head
      rcases input with worldInput | request
      · rcases worldInput with uniformInput | hashInput <;>
          simp [directHashQueries, ih]
      · simp [directHashQueries, ih]

theorem OriginConfiguration.paddedRealized_append_direct
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    {cover : FewTimeCover f cache secretKey signingLog index targetLeaves}
    {q limit : Nat} {hle : signingLog.length ≤ limit}
    {configuration : OriginConfiguration (cover.pattern.pad hle) q}
    (state : ViewedFullTraceState)
    (hlog : state.trace.signing.toSigningLog = signingLog)
    (hrealized : configuration.PaddedRealizedBy cover hle state.trace hlog)
    (input : HashInput) (output : HashOutput) (finalCache : QueryCache HashSpec) :
    let appended := appendTargetViewedState (.inl (.inr input)) state.cache output
      finalCache none state
    ∃ hlog' : appended.trace.signing.toSigningLog = signingLog,
      configuration.PaddedRealizedBy cover hle appended.trace hlog' := by
  classical
  let appended := appendTargetViewedState (.inl (.inr input)) state.cache output
    finalCache none state
  have hlog' : appended.trace.signing.toSigningLog = signingLog := by
    simpa [appended, appendTargetViewedState, fullAdversaryTraceUpdate,
      signingCacheTraceUpdate] using hlog
  refine ⟨hlog', ?_⟩
  have hlogEq : hlog' = hlog := Subsingleton.elim _ _
  subst hlog'
  constructor
  · exact hrealized.1
  · intro entry hselected
    obtain ⟨sourceOutput, sourcePosition, intervalPosition, selectedIntervalPosition,
      hdirect, hsource, hordinal, hbefore, hselectedInterval, hselectedRank,
      hinput, hinitial, hquery, hadmissible, hview⟩ := hrealized.2 entry hselected
    let sourcePosition' : Fin appended.trace.hashQueries.length :=
      ⟨sourcePosition.val, by
        simp [appended, appendTargetViewedState, fullAdversaryTraceUpdate,
          FullAdversaryTrace.hashQueries, directHashQueries_append, directHashQueries]⟩
    let intervalPosition' : Fin appended.trace.intervals.length :=
      ⟨intervalPosition.val, by
        simp [appended, appendTargetViewedState, fullAdversaryTraceUpdate]⟩
    let selectedIntervalPosition' : Fin appended.trace.intervals.length :=
      ⟨selectedIntervalPosition.val, by
        simp [appended, appendTargetViewedState, fullAdversaryTraceUpdate]⟩
    have hinterval : appended.trace.intervals.get intervalPosition' =
        state.trace.intervals.get intervalPosition := by
      simp [appended, appendTargetViewedState, fullAdversaryTraceUpdate,
        intervalPosition', List.get_eq_getElem,
        List.getElem_append_left intervalPosition.isLt]
    have hselectedInterval' : appended.trace.intervals.get selectedIntervalPosition' =
        state.trace.intervals.get selectedIntervalPosition := by
      simp [appended, appendTargetViewedState, fullAdversaryTraceUpdate,
        selectedIntervalPosition', List.get_eq_getElem,
        List.getElem_append_left selectedIntervalPosition.isLt]
    have hdirect' : isDirectHashQuery
        (appended.trace.intervals.get intervalPosition').input := by
      rwa [hinterval]
    refine ⟨sourceOutput, sourcePosition', intervalPosition', selectedIntervalPosition',
      hdirect', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hsource
    · calc
        sourcePosition'.val = sourcePosition.val := rfl
        _ = (Fin.encodeSubtype (fun position =>
            isDirectHashQuery (state.trace.intervals.get position).input)
            ⟨intervalPosition, hdirect⟩).val := hordinal
        _ = directIntervalCount (state.trace.intervals.take intervalPosition.val) :=
          encodeSubtype_directInterval_eq state.trace.intervals intervalPosition hdirect
        _ = directIntervalCount
            (appended.trace.intervals.take intervalPosition'.val) := by
          simp [appended, appendTargetViewedState, fullAdversaryTraceUpdate,
            intervalPosition', List.take_append_of_le_length intervalPosition.isLt.le]
        _ = (Fin.encodeSubtype (fun position =>
            isDirectHashQuery (appended.trace.intervals.get position).input)
            ⟨intervalPosition', hdirect'⟩).val :=
          (encodeSubtype_directInterval_eq appended.trace.intervals
            intervalPosition' hdirect').symm
    · exact hbefore
    · rwa [hselectedInterval']
    · simpa [appended, appendTargetViewedState, fullAdversaryTraceUpdate,
        selectedIntervalPosition', List.take_append_of_le_length
          selectedIntervalPosition.isLt.le] using hselectedRank
    · rwa [hinterval]
    · rwa [hinterval]
    · rw [hinterval]
      exact hquery
    · exact hadmissible
    · exact hview

theorem OriginConfiguration.paddedRealized_sourceAt_directIntervalCount_eq_none
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    {cover : FewTimeCover f cache secretKey signingLog index targetLeaves}
    {q limit : Nat} {hle : signingLog.length ≤ limit}
    {configuration : OriginConfiguration (cover.pattern.pad hle) q}
    {trace : FullAdversaryTrace} {hlog : trace.signing.toSigningLog = signingLog}
    (hrealized : configuration.PaddedRealizedBy cover hle trace hlog) :
    configuration.sourceAt? (directIntervalCount trace.intervals) = none := by
  cases hlookup : configuration.sourceAt? (directIntervalCount trace.intervals) with
  | none => rfl
  | some selected =>
      have heq := (configuration.sourceAt?_eq_some_iff _ selected).1 hlookup
      have hlt := configuration.paddedRealized_source_lt_directIntervalCount
        hrealized selected
      omega

def adversaryWithTargetQuery (adversary : Adversary) (publicKey : PublicKey) :
    OracleComp (OracleWorld + SigningSpec) (Forgery × HashOutput) := do
  let forgery ← adversary.main publicKey
  let input := tweakableHashInput publicKey.parameter .message
    (messageDigestPayload publicKey.root forgery.message forgery.signature.randomness)
  let output ← OracleComp.liftComp
    (OracleComp.liftComp
      (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) OracleWorld)
    (OracleWorld + SigningSpec)
  pure (forgery, output)

def appendDirectTargetViewedState (input : HashInput)
    (initialCache : QueryCache HashSpec) (output : HashOutput)
    (finalCache : QueryCache HashSpec) (state : ViewedFullTraceState) :
    ViewedFullTraceState :=
  appendTargetViewedState (.inl (.inr input)) initialCache output finalCache none state

def verifyWithViewAfterOutput (publicKey : PublicKey) (signature : Signature)
    (output : HashOutput) : OracleComp HashSpec (Bool × FewTimeView) :=
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

theorem verifyWithView_split_run (publicKey : PublicKey) (message : Message)
    (signature : Signature) (cache : QueryCache HashSpec) :
    (simulateQ romImpl
        (liftM (verifyWithView publicKey message signature) :
          OracleComp OracleWorld (Bool × FewTimeView))).run cache =
      (randomOracle (tweakableHashInput publicKey.parameter .message
          (messageDigestPayload publicKey.root message signature.randomness))).run cache >>=
        fun source =>
          (simulateQ romImpl
            (liftM (verifyWithViewAfterOutput publicKey signature source.1) :
              OracleComp OracleWorld (Bool × FewTimeView))).run source.2 := by
  let input := tweakableHashInput publicKey.parameter .message
    (messageDigestPayload publicKey.root message signature.randomness)
  have hqueryRun :
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (oracleHash input)).run cache = (randomOracle input).run cache := by
    change (simulateQ (randomOracle : QueryImpl HashSpec _)
      (liftM (HashSpec.query input))).run cache = _
    rw [simulateQ_spec_query]
  simp only [simulateQ_romImpl_liftM]
  rw [verifyWithView, simulateQ_bind, StateT.run_bind]
  rw [show tweakableHashInput publicKey.parameter .message
      (messageDigestPayload publicKey.root message signature.randomness) = input from rfl,
    hqueryRun]
  rfl

theorem adversaryWithTargetQuery_viewed_run
    (adversary : Adversary) (publicKey : PublicKey) (secretKey : SecretKey)
    (rootCache : QueryCache HashSpec) :
    (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        (adversaryWithTargetQuery adversary publicKey)).run
          ⟨rootCache, ⟨[], [], []⟩, [], none⟩ = (do
      let (forgery, state) ←
        (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
          (adversary.main publicKey)).run ⟨rootCache, ⟨[], [], []⟩, [], none⟩
      let input := tweakableHashInput publicKey.parameter .message
        (messageDigestPayload publicKey.root forgery.message forgery.signature.randomness)
      let (output, finalCache) ← (randomOracle input).run state.cache
      pure ((forgery, output), appendDirectTargetViewedState input
        state.cache output finalCache state)) := by
  rw [adversaryWithTargetQuery, simulateQ_bind, StateT.run_bind]
  apply bind_congr
  rintro ⟨forgery, state⟩
  rw [simulateQ_bind, StateT.run_bind]
  let input := tweakableHashInput publicKey.parameter .message
    (messageDigestPayload publicKey.root forgery.message forgery.signature.randomness)
  have hsingle :
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        (OracleComp.liftComp
          (OracleComp.liftComp
            (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) OracleWorld)
          (OracleWorld + SigningSpec))).run state =
        (fun result => (result.1, appendDirectTargetViewedState input state.cache
          result.1 result.2 state)) <$> (randomOracle input).run state.cache := by
    let worldImpl : QueryImpl OracleWorld (StateT ViewedFullTraceState ProbComp) :=
      fun worldInput => viewedFullTracedMappedAdversaryImpl secretKey (.inl worldInput)
    let signingImpl : QueryImpl SigningSpec (StateT ViewedFullTraceState ProbComp) :=
      fun request => viewedFullTracedMappedAdversaryImpl secretKey (.inr request)
    have houter : viewedFullTracedMappedAdversaryImpl secretKey =
        worldImpl + signingImpl := by
      funext queryInput
      cases queryInput <;> rfl
    have houterSim := QueryImpl.simulateQ_add_liftComp_left worldImpl signingImpl
      (OracleComp.liftComp
        (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) OracleWorld)
    let uniformImpl : QueryImpl unifSpec (StateT ViewedFullTraceState ProbComp) :=
      fun uniformInput => worldImpl (.inl uniformInput)
    let hashImpl : QueryImpl HashSpec (StateT ViewedFullTraceState ProbComp) :=
      fun hashInput => worldImpl (.inr hashInput)
    have hworld : worldImpl = uniformImpl + hashImpl := by
      funext worldInput
      cases worldInput <;> rfl
    have hworldSim := QueryImpl.simulateQ_add_liftComp_right uniformImpl hashImpl
      (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput)
    let directImpl : QueryImpl HashSpec (StateT ViewedFullTraceState ProbComp) :=
      fun hashInput current =>
        (fun queryResult => (queryResult.1,
          ⟨queryResult.2,
            fullAdversaryTraceUpdate (.inl (.inr hashInput)) current.cache
              queryResult.1 queryResult.2 current.trace,
            current.views, current.targetView⟩)) <$>
          (randomOracle hashInput).run current.cache
    have hhash : hashImpl = directImpl := by
      funext hashInput current
      dsimp [hashImpl, worldImpl]
      rw [viewedFullTracedMappedAdversaryImpl]
      rfl
    calc
      _ = (simulateQ (worldImpl + signingImpl)
          (OracleComp.liftComp
            (OracleComp.liftComp
              (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) OracleWorld)
            (OracleWorld + SigningSpec))).run state := by rw [← houter]
      _ = (simulateQ worldImpl
          (OracleComp.liftComp
            (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput)
            OracleWorld)).run state :=
        congrArg (fun computation => computation.run state) houterSim
      _ = (simulateQ (uniformImpl + hashImpl)
          (OracleComp.liftComp
            (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput)
            OracleWorld)).run state := by rw [← hworld]
      _ = (simulateQ hashImpl
          (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput)).run state :=
        congrArg (fun computation => computation.run state) hworldSim
      _ = _ := by
        rw [hhash, simulateQ_spec_query]
        rfl
  rw [hsingle]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply bind_congr
  rintro ⟨output, finalCache⟩
  rfl

theorem adversaryWithTargetQuery_viewed_support
    (adversary : Adversary) (publicKey : PublicKey) (secretKey : SecretKey)
    (rootCache : QueryCache HashSpec) (forgery : Forgery) (state : ViewedFullTraceState)
    (hadversary : (forgery, state) ∈ support
      ((simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        (adversary.main publicKey)).run ⟨rootCache, ⟨[], [], []⟩, [], none⟩))
    (output : HashOutput) (finalCache : QueryCache HashSpec)
    (hquery : (output, finalCache) ∈ support
      ((randomOracle (tweakableHashInput publicKey.parameter .message
        (messageDigestPayload publicKey.root forgery.message
          forgery.signature.randomness))).run state.cache)) :
    ((forgery, output), appendTargetViewedState
        (.inl (.inr (tweakableHashInput publicKey.parameter .message
          (messageDigestPayload publicKey.root forgery.message
            forgery.signature.randomness))))
        state.cache output finalCache none state) ∈ support
      ((simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        (adversaryWithTargetQuery adversary publicKey)).run
          ⟨rootCache, ⟨[], [], []⟩, [], none⟩) := by
  rw [adversaryWithTargetQuery, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff]
  refine ⟨(forgery, state), hadversary, ?_⟩
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  let appended := appendTargetViewedState
    (.inl (.inr (tweakableHashInput publicKey.parameter .message
      (messageDigestPayload publicKey.root forgery.message forgery.signature.randomness))))
    state.cache output finalCache none state
  refine ⟨(output, appended), ?_, ?_⟩
  · let input := tweakableHashInput publicKey.parameter .message
      (messageDigestPayload publicKey.root forgery.message forgery.signature.randomness)
    have hsingle : (output, appended) ∈ support
        ((simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
          (OracleComp.liftComp
            (OracleComp.liftComp
              (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) OracleWorld)
            (OracleWorld + SigningSpec))).run state) := by
      let worldImpl : QueryImpl OracleWorld (StateT ViewedFullTraceState ProbComp) :=
        fun worldInput => viewedFullTracedMappedAdversaryImpl secretKey (.inl worldInput)
      let signingImpl : QueryImpl SigningSpec (StateT ViewedFullTraceState ProbComp) :=
        fun request => viewedFullTracedMappedAdversaryImpl secretKey (.inr request)
      have houter : viewedFullTracedMappedAdversaryImpl secretKey =
          worldImpl + signingImpl := by
        funext queryInput
        cases queryInput <;> rfl
      rw [houter]
      have houterSim := QueryImpl.simulateQ_add_liftComp_left worldImpl signingImpl
        (OracleComp.liftComp
          (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) OracleWorld)
      have houterRun := congrArg (fun computation => computation.run state) houterSim
      have houterSupport := congrArg support houterRun
      apply (Set.ext_iff.mp houterSupport (output, appended)).mpr
      let uniformImpl : QueryImpl unifSpec (StateT ViewedFullTraceState ProbComp) :=
        fun uniformInput => worldImpl (.inl uniformInput)
      let hashImpl : QueryImpl HashSpec (StateT ViewedFullTraceState ProbComp) :=
        fun hashInput => worldImpl (.inr hashInput)
      have hworld : worldImpl = uniformImpl + hashImpl := by
        funext worldInput
        cases worldInput <;> rfl
      rw [hworld]
      have hworldSim := QueryImpl.simulateQ_add_liftComp_right uniformImpl hashImpl
        (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput)
      have hworldRun := congrArg (fun computation => computation.run state) hworldSim
      have hworldSupport := congrArg support hworldRun
      apply (Set.ext_iff.mp hworldSupport (output, appended)).mpr
      let directImpl : QueryImpl HashSpec (StateT ViewedFullTraceState ProbComp) :=
        fun hashInput current =>
          (fun queryResult => (queryResult.1,
            ⟨queryResult.2,
              fullAdversaryTraceUpdate (.inl (.inr hashInput)) current.cache
                queryResult.1 queryResult.2 current.trace,
              current.views, current.targetView⟩)) <$>
            (randomOracle hashInput).run current.cache
      have hhash : hashImpl = directImpl := by
        funext hashInput current
        dsimp [hashImpl, worldImpl]
        rw [viewedFullTracedMappedAdversaryImpl]
        rfl
      rw [hhash, simulateQ_spec_query]
      change (output, appended) ∈ support (directImpl input state)
      dsimp only [directImpl]
      rw [support_map]
      refine ⟨(output, finalCache), hquery, ?_⟩
      simp [input, appendTargetViewedState, appendOriginReplayView, appended]
    simpa only [Prod.fst, Prod.snd, input] using hsingle
  · simp [appended]

theorem viewedFullTracedMappedAdversaryImpl_interval_invariants
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (result : α × ViewedFullTraceState)
    (hmem : result ∈ support
      ((simulateQ (viewedFullTracedMappedAdversaryImpl secretKey) computation).run
        ⟨initialCache, ⟨[], [], []⟩, [], none⟩)) :
    result.2.trace.Consistent ∧ result.2.trace.IntervalsLe result.2.cache ∧
      FullAdversaryTrace.Chronological result.2.trace.intervals := by
  have hprojected : (result.1, result.2.base) ∈ support
      ((simulateQ (fullTracedMappedAdversaryImpl secretKey) computation).run
        (initialCache, ⟨[], [], []⟩)) := by
    have hmap : (result.1, result.2.base) ∈ support
        (Prod.map id ViewedFullTraceState.base <$>
          (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey) computation).run
            ⟨initialCache, ⟨[], [], []⟩, [], none⟩) := by
      rw [support_map]
      exact ⟨result, hmem, rfl⟩
    rw [viewedFullTracedMappedAdversaryImpl_projection secretKey computation
      ⟨initialCache, ⟨[], [], []⟩, [], none⟩] at hmap
    exact hmap
  exact fullTracedMappedAdversaryImpl_interval_invariants secretKey computation
    initialCache ⟨[], [], []⟩ (result.1, result.2.base)
      (by simp [FullAdversaryTrace.Consistent])
      (by simp [FullAdversaryTrace.IntervalsLe])
      (by simp [FullAdversaryTrace.Chronological]) hprojected

theorem viewedFullTracedMappedAdversaryImpl_validIntervals
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (result : α × ViewedFullTraceState)
    (hmem : result ∈ support
      ((simulateQ (viewedFullTracedMappedAdversaryImpl secretKey) computation).run
        ⟨initialCache, ⟨[], [], []⟩, [], none⟩)) :
    result.2.trace.ValidIntervals secretKey := by
  have hprojected : (result.1, result.2.base) ∈ support
      ((simulateQ (fullTracedMappedAdversaryImpl secretKey) computation).run
        (initialCache, ⟨[], [], []⟩)) := by
    have hmap : (result.1, result.2.base) ∈ support
        (Prod.map id ViewedFullTraceState.base <$>
          (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey) computation).run
            ⟨initialCache, ⟨[], [], []⟩, [], none⟩) := by
      rw [support_map]
      exact ⟨result, hmem, rfl⟩
    rw [viewedFullTracedMappedAdversaryImpl_projection secretKey computation
      ⟨initialCache, ⟨[], [], []⟩, [], none⟩] at hmap
    exact hmap
  exact fullTracedMappedAdversaryImpl_validIntervals secretKey computation
    initialCache ⟨[], [], []⟩ (result.1, result.2.base)
      (by simp [FullAdversaryTrace.ValidIntervals]) hprojected

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

theorem probEvent_bind_le_bind_of_forall_le
    {mx : ProbComp α} {left : α → ProbComp β} {right : α → ProbComp γ}
    {leftEvent : β → Prop} {rightEvent : γ → Prop}
    (h : ∀ value ∈ support mx,
      Pr[leftEvent | left value] ≤ Pr[rightEvent | right value]) :
    Pr[leftEvent | mx >>= left] ≤ Pr[rightEvent | mx >>= right] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro value
  by_cases hvalue : value ∈ support mx
  · exact mul_le_mul' le_rfl (h value hvalue)
  · simp [probOutput_eq_zero_of_not_mem_support hvalue]

end Concrete

end SphincsSecurity
