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

end Concrete

end SphincsSecurity
