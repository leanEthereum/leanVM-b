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

end Concrete

end SphincsSecurity
