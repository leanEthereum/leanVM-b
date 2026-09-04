import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHiddenPlanFinal

/-!
# Hidden fixed-candidate matching

A coordinate that is already published stays published through the direct interpreter, and a
private stop cannot name it. This strengthens the post-selection observer from the ungated
candidate risk to the hidden candidate risk.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

def KnownPublishedCoordinateResult
    (coordinate : Coordinate) (output : HashOutput) : DirectWitnessResult α → Prop
  | .stoppedPrivate witness => coordinate ≠ .position witness.position
  | .done result =>
      result.context.state.values coordinate = some output ∧
        coordinate ∈ result.context.state.revealed
  | _ => True

set_option maxRecDepth 100000 in
theorem knownPublishedCoordinateResult_of_mem_runDirectResolvedWitnessFromTable
    (coordinate : Coordinate) (output : HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hvalue : context.state.values coordinate = some output)
    (hrevealed : coordinate ∈ context.state.revealed) :
    ∀ result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation),
      KnownPublishedCoordinateResult coordinate output result := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      intro result hresult
      simp [runDirectResolvedWitnessFromTable] at hresult
      subst result
      exact ⟨hvalue, hrevealed⟩
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          rw [runDirectResolvedWitnessFromTable_uniform_query_bind]
          intro result hresult
          rw [mem_support_bind_iff] at hresult
          obtain ⟨sampled, _hsampled, htail⟩ := hresult
          exact ih sampled context fuel hvalue hrevealed result htail
      | hashOutput =>
          rw [runDirectResolvedWitnessFromTable_hashOutput_query_bind]
          intro result hresult
          rw [mem_support_bind_iff] at hresult
          obtain ⟨sampled, _hsampled, htail⟩ := hresult
          exact ih sampled context fuel hvalue hrevealed result htail
      | ensure ensured =>
          rw [runDirectResolvedWitnessFromTable_ensure_query_bind]
          intro result hresult
          exact ih () { context with state := context.state.ensure ensured } fuel hvalue
            hrevealed result hresult
      | probe probed candidate =>
          rw [runDirectResolvedWitnessFromTable_probe_query_bind]
          intro result hresult
          cases fuel with
          | zero =>
              simp at hresult
              subst result
              trivial
          | succ remaining =>
              by_cases hprobedRevealed : probed ∈ context.state.revealed
              · simp only [hprobedRevealed, ↓reduceIte] at hresult
                exact ih () context remaining hvalue hrevealed result hresult
              · simp only [hprobedRevealed, ↓reduceIte] at hresult
                exact ih () { context with state := context.state.addPending probed candidate }
                  remaining hvalue hrevealed result hresult
      | peek peeked =>
          rw [runDirectResolvedWitnessFromTable_peek_query_bind]
          intro result hresult
          exact ih (context.state.values peeked) context fuel hvalue hrevealed result hresult
      | publish published =>
          rw [runDirectResolvedWitnessFromTable_publish_query_bind]
          intro result hresult
          exact ih () { context with state := context.state.publish published } fuel hvalue
            (by simp [LazyRevealProbe.State.publish, hrevealed]) result hresult
      | reveal revealed =>
          rw [runDirectResolvedWitnessFromTable_reveal_query_bind]
          intro result hresult
          cases hrevealedValue : context.state.values revealed with
          | some revealedOutput =>
              simp only [hrevealedValue] at hresult
              exact ih revealedOutput context fuel hvalue hrevealed result hresult
          | none =>
              simp only [hrevealedValue] at hresult
              have hne : revealed ≠ coordinate := by
                intro heq
                subst revealed
                rw [hvalue] at hrevealedValue
                contradiction
              cases revealed with
              | chainStart lay tree leafIdx chainIdx =>
                  let revealedOutput := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) revealedOutput
                  · simp [revealedOutput, hhit] at hresult
                    subst result
                    trivial
                  · simp only [revealedOutput, hhit, ↓reduceIte] at hresult
                    have hnextValue :
                        (context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) revealedOutput).values
                            coordinate = some output := by
                      simpa [LazyRevealProbe.State.materialize,
                        Function.update_of_ne (Ne.symm hne)] using hvalue
                    exact ih revealedOutput
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) revealedOutput
                        values := context.values }
                      fuel hnextValue hrevealed result hresult
              | position position =>
                  cases hprivate : context.values position with
                  | some revealedOutput =>
                      by_cases hhit : context.state.hitAt (.position position) revealedOutput
                      · simp [hprivate, hhit] at hresult
                        subst result
                        exact Ne.symm hne
                      · simp only [hprivate, hhit, ↓reduceIte] at hresult
                        have hnextValue :
                            (context.state.materialize (.position position) revealedOutput).values
                                coordinate = some output := by
                          simpa [LazyRevealProbe.State.materialize,
                            Function.update_of_ne (Ne.symm hne)] using hvalue
                        exact ih revealedOutput
                          { state := context.state.materialize (.position position) revealedOutput
                            values := context.values }
                          fuel hnextValue hrevealed result hresult
                  | none =>
                      simp only [hprivate] at hresult
                      rw [mem_support_bind_iff] at hresult
                      obtain ⟨revealedOutput, _houtput, htail⟩ := hresult
                      by_cases hhit : context.state.hitAt (.position position) revealedOutput
                      · simp [hhit] at htail
                        subst result
                        trivial
                      · simp only [hhit, ↓reduceIte] at htail
                        have hnextValue :
                            (context.state.materialize (.position position) revealedOutput).values
                                coordinate = some output := by
                          simpa [LazyRevealProbe.State.materialize,
                            Function.update_of_ne (Ne.symm hne)] using hvalue
                        exact ih revealedOutput
                          { state := context.state.materialize (.position position) revealedOutput
                            values := context.values.install position revealedOutput }
                          fuel hnextValue hrevealed result htail

noncomputable def finishDirectWitnessHiddenCandidateMatch
    (candidate : Probe) : DirectWitnessResult α → ProbComp Bool
  | .stoppedFuel => pure false
  | .stoppedOrdinary => pure false
  | .stoppedPrivate witness => pure (decide (witness.MatchesCandidate candidate))
  | .done result => hiddenPrivateCandidateFire candidate result.context

theorem probEvent_runDirectWitnessHiddenCandidateMatch_le_zero_of_revealed
    (candidate : Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hpublished : PublishedValues context.state)
    (hrevealed : candidate.coordinate ∈ context.state.revealed) :
    Pr[fun hit : Bool => hit = true |
        runDirectResolvedWitnessFromTable context fuel table computation >>=
          finishDirectWitnessHiddenCandidateMatch candidate] ≤ 0 := by
  obtain ⟨output, hvalue⟩ := Option.ne_none_iff_exists'.mp
    (hpublished candidate.coordinate hrevealed)
  rw [probEvent_bind_eq_tsum]
  have hzero : (∑' result,
      Pr[= result | runDirectResolvedWitnessFromTable context fuel table computation] *
        Pr[fun hit : Bool => hit = true |
          finishDirectWitnessHiddenCandidateMatch candidate result]) = 0 := by
    apply ENNReal.tsum_eq_zero.2
    intro result
    by_cases hresult : result ∈ support
        (runDirectResolvedWitnessFromTable context fuel table computation)
    · have hsafe := knownPublishedCoordinateResult_of_mem_runDirectResolvedWitnessFromTable
        candidate.coordinate output computation context fuel table hvalue hrevealed result hresult
      cases result with
      | stoppedFuel => simp [finishDirectWitnessHiddenCandidateMatch]
      | stoppedOrdinary => simp [finishDirectWitnessHiddenCandidateMatch]
      | stoppedPrivate witness =>
          have hnotMatch : ¬witness.MatchesCandidate candidate := by
            intro hmatch
            exact hsafe hmatch.1
          simp [finishDirectWitnessHiddenCandidateMatch, hnotMatch]
      | done result =>
          simp [finishDirectWitnessHiddenCandidateMatch, hiddenPrivateCandidateFire,
            hsafe.2]
    · rw [probOutput_eq_zero_of_not_mem_support hresult]
      simp
  rw [hzero]

theorem probEvent_finishDirectWitnessHiddenCandidateMatch_le
    (candidate : Probe) (result : DirectWitnessResult α) :
    Pr[fun hit : Bool => hit = true |
        finishDirectWitnessHiddenCandidateMatch candidate result] ≤
      Pr[fun hit : Bool => hit = true |
        finishDirectWitnessPrivateCandidateMatch candidate result] := by
  cases result with
  | stoppedFuel =>
      change Pr[fun hit : Bool => hit = true | pure false] ≤
        Pr[fun hit : Bool => hit = true | pure false]
      exact le_rfl
  | stoppedOrdinary =>
      change Pr[fun hit : Bool => hit = true | pure false] ≤
        Pr[fun hit : Bool => hit = true | pure false]
      exact le_rfl
  | stoppedPrivate witness =>
      change Pr[fun hit : Bool => hit = true |
          pure (decide (witness.MatchesCandidate candidate))] ≤
        Pr[fun hit : Bool => hit = true |
          pure (decide (witness.MatchesCandidate candidate))]
      exact le_rfl
  | done result =>
      change Pr[fun hit : Bool => hit = true |
          hiddenPrivateCandidateFire candidate result.context] ≤
        Pr[fun hit : Bool => hit = true |
          privateCandidateFire candidate result.context]
      unfold hiddenPrivateCandidateFire
      split
      · simp
      · exact le_rfl

theorem probEvent_runDirectWitnessHiddenCandidateMatch_le
    (candidate : Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hpublished : PublishedValues context.state) :
    Pr[fun hit : Bool => hit = true |
        runDirectResolvedWitnessFromTable context fuel table computation >>=
          finishDirectWitnessHiddenCandidateMatch candidate] ≤
      Pr[fun hit : Bool => hit = true | hiddenPrivateCandidateFire candidate context] := by
  by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
  · rw [hiddenPrivateCandidateFire_of_revealed candidate context hrevealed]
    simpa using probEvent_runDirectWitnessHiddenCandidateMatch_le_zero_of_revealed candidate
      context fuel table computation hpublished hrevealed
  · rw [hiddenPrivateCandidateFire_of_not_revealed candidate context hrevealed]
    have hleft :
        Pr[fun hit : Bool => hit = true |
            runDirectResolvedWitnessFromTable context fuel table computation >>=
              finishDirectWitnessHiddenCandidateMatch candidate] ≤
          Pr[fun hit : Bool => hit = true |
            runDirectResolvedWitnessFromTable context fuel table computation >>=
              finishDirectWitnessPrivateCandidateMatch candidate] := by
      apply probEvent_bind_mono
      intro result _hresult
      exact probEvent_finishDirectWitnessHiddenCandidateMatch_le candidate result
    exact hleft.trans
      (probEvent_runDirectWitnessPrivateCandidateMatch_le candidate context fuel table computation)

theorem probEvent_finishDirectWitnessPlanMatchesCandidate_le_hidden
    (candidate : Probe)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (result : DirectWitnessResult α)
    (hobserve : ∀ resolved : ResolvedRunResult α,
      result = .done resolved →
      Pr[PrivateWitnessPlanMatchesCandidate candidate |
          observe resolved.context resolved.remaining resolved.value candidates] ≤
        Pr[fun hit : Bool => hit = true |
          hiddenPrivateCandidateFire candidate resolved.context]) :
    Pr[PrivateWitnessPlanMatchesCandidate candidate |
        finishDirectWitnessPlanObserve observe candidates result] ≤
      Pr[fun hit : Bool => hit = true |
        finishDirectWitnessHiddenCandidateMatch candidate result] := by
  cases result with
  | stoppedFuel => simp [finishDirectWitnessPlanObserve,
      finishDirectWitnessHiddenCandidateMatch, PrivateWitnessPlanMatchesCandidate]
  | stoppedOrdinary => simp [finishDirectWitnessPlanObserve,
      finishDirectWitnessHiddenCandidateMatch, PrivateWitnessPlanMatchesCandidate]
  | stoppedPrivate witness =>
      simp [finishDirectWitnessPlanObserve, finishDirectWitnessHiddenCandidateMatch,
        PrivateWitnessPlanMatchesCandidate]
  | done resolved =>
      simpa [finishDirectWitnessPlanObserve, finishDirectWitnessHiddenCandidateMatch] using
        hobserve resolved rfl

set_option maxRecDepth 100000 in
theorem probEvent_runDirectWitnessPlanMatchesCandidate_le_hidden
    (candidate : Probe)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hpublished : PublishedValues context.state)
    (hobserve : ∀ result : ResolvedRunResult α,
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable context fuel table computation) →
      Pr[PrivateWitnessPlanMatchesCandidate candidate |
          observe result.context result.remaining result.value candidates] ≤
        Pr[fun hit : Bool => hit = true |
          hiddenPrivateCandidateFire candidate result.context]) :
    Pr[PrivateWitnessPlanMatchesCandidate candidate |
        runDirectWitnessPlanObserve observe candidates context fuel table computation] ≤
      Pr[fun hit : Bool => hit = true |
        hiddenPrivateCandidateFire candidate context] := by
  unfold runDirectWitnessPlanObserve
  calc
    _ ≤ Pr[fun hit : Bool => hit = true |
        runDirectResolvedWitnessFromTable context fuel table computation >>=
          finishDirectWitnessHiddenCandidateMatch candidate] := by
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support
          (runDirectResolvedWitnessFromTable context fuel table computation)
      · exact mul_le_mul' le_rfl
          (probEvent_finishDirectWitnessPlanMatchesCandidate_le_hidden candidate observe candidates
            result (by
              intro resolved heq
              subst result
              exact hobserve resolved hresult))
      · rw [probOutput_eq_zero_of_not_mem_support hresult]
        simp
    _ ≤ _ := probEvent_runDirectWitnessHiddenCandidateMatch_le candidate context fuel table
      computation hpublished

end SphincsSecurity.Concrete.OtsProbeSimulation
