import SphincsSecurity.Proof.FewTimeTargetSigner

/-!
# Completing an optional fresh signer target

A signer may produce no fresh selected digest. Completing that absent selection with an independent
uniform view keeps the result uniform. This is the optional-candidate form needed by the target
monitor.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def freshSelectedLoopView?
    (referenceCache : QueryCache HashSpec) (secretKey : SecretKey) (message : Message)
    (result : Option (Randomness × Index × (DigestTree → FtsLeaf)) ×
      QueryCache HashSpec) : Option FewTimeView :=
  match result.1 with
  | none => none
  | some (randomness, index, leaves) =>
      if referenceCache (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness)) = none then
        some (selectedFewTimeView index leaves)
      else none

noncomputable def completeFreshSelectedLoopView
    (referenceCache : QueryCache HashSpec) (secretKey : SecretKey) (message : Message)
    (result : Option (Randomness × Index × (DigestTree → FtsLeaf)) ×
      QueryCache HashSpec) : ProbComp FewTimeView :=
  match freshSelectedLoopView? referenceCache secretKey message result with
  | some view => pure view
  | none => $ᵗ FewTimeView

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
theorem probEvent_completeFreshSelectedLoopView_le_uniform
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (P : FewTimeView → Prop)
    (hinvariant : OnlyRejectedNewMessageEntries referenceCache workingCache secretKey message) :
    Pr[P | (simulateQ romImpl (signDigestLoop attempts secretKey message)).run workingCache >>=
      completeFreshSelectedLoopView referenceCache secretKey message] ≤
      Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  induction attempts generalizing workingCache with
  | zero =>
      simp [signDigestLoop, completeFreshSelectedLoopView, freshSelectedLoopView?]
  | succ attempts ih =>
      rw [signDigestLoop_run_succ_eq]
      rw [bind_assoc]
      refine probEvent_bind_le_of_forall_le fun randomness _hrandomness => ?_
      let input := tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)
      by_cases hreference : referenceCache input = none
      · by_cases hworking : workingCache input = none
        · let continuation := signDigestLoopContinuation attempts secretKey message randomness
          have hcoordinates := evalDist_signAttempt_fresh_bind_coordinates
            secretKey message randomness workingCache (by simpa only [input] using hworking)
            continuation
          change Pr[P |
              ((simulateQ randomOracle
                (signAttempt secretKey message randomness :
                  OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf))))).run
                workingCache >>= continuation) >>=
                  completeFreshSelectedLoopView referenceCache secretKey message] ≤ _
          have hcoordinates' :
              𝒟[((simulateQ randomOracle
                  (signAttempt secretKey message randomness :
                    OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf))))).run
                    workingCache >>= continuation) >>=
                    completeFreshSelectedLoopView referenceCache secretKey message] =
                𝒟[(do
                  let coordinates ← $ᵗ HashOutputCoordinates
                  let output := hashOutputCoordinatesEquiv.symm coordinates
                  continuation (signAttemptResultOfOutput output,
                    workingCache.cacheQuery input output)) >>=
                    completeFreshSelectedLoopView referenceCache secretKey message] := by
            rw [evalDist_bind, hcoordinates, ← evalDist_bind]
          rw [probEvent_congr' (fun _ _ => Iff.rfl) hcoordinates']
          rw [bind_assoc]
          have hreorder := evalDist_uniformHashOutputCoordinates_bind_reordered
            (fun coordinates =>
              let output := hashOutputCoordinatesEquiv.symm coordinates
              continuation (signAttemptResultOfOutput output,
                workingCache.cacheQuery input output) >>=
                  completeFreshSelectedLoopView referenceCache secretKey message)
          rw [probEvent_congr' (fun _ _ => Iff.rfl) hreorder]
          refine probEvent_bind_le_of_forall_le fun rest _hrest => ?_
          by_cases hadmissible : rest.1 = 0
          · refine (probEvent_bind_le_probEvent (p := P) (q := P) ?_).trans le_rfl
            intro view _hview hnotP
            let coordinates : HashOutputCoordinates := ((view, rest.1), rest.2)
            let output := hashOutputCoordinatesEquiv.symm coordinates
            have hsuccessful : signAttemptResultOfOutput output ≠ none := by
              rw [signAttemptResultOfOutput_coordinates_ne_none_iff]
              exact hadmissible
            obtain ⟨indexLeaves, hindexLeaves⟩ := Option.ne_none_iff_exists'.mp hsuccessful
            rcases indexLeaves with ⟨index, leaves⟩
            have hviewEq : selectedFewTimeView index leaves = view :=
              signAttemptResultOfOutput_coordinates_view coordinates index leaves
                (by simpa only [output] using hindexLeaves)
            dsimp only
            rw [show signAttemptResultOfOutput
                (hashOutputCoordinatesEquiv.symm ((view, rest.1), rest.2)) =
                some (index, leaves) by
              simpa only [coordinates, output] using hindexLeaves]
            simp only [continuation, signDigestLoopContinuation, pure_bind]
            rw [completeFreshSelectedLoopView, freshSelectedLoopView?]
            have hreference' : referenceCache
                (tweakableHashInput secretKey.parameter .message
                  (messageDigestPayload secretKey.root message randomness)) = none := by
              simpa only [input] using hreference
            simp [hreference', hviewEq, hnotP]
          · refine probEvent_bind_le_of_forall_le fun view _hview => ?_
            let coordinates : HashOutputCoordinates := ((view, rest.1), rest.2)
            let output := hashOutputCoordinatesEquiv.symm coordinates
            have hrejected : signAttemptResultOfOutput output = none := by
              apply Option.eq_none_iff_forall_not_mem.mpr
              intro selected hselected
              have hne : signAttemptResultOfOutput output ≠ none := by
                rw [hselected]
                simp
              rw [signAttemptResultOfOutput_coordinates_ne_none_iff] at hne
              exact hadmissible hne
            have hinvariant' := onlyRejectedNewMessageEntries_cacheRejected
              referenceCache workingCache secretKey message randomness output hinvariant
              hrejected
            simpa only [coordinates, output, continuation, hrejected,
              signDigestLoopContinuation] using
              ih (workingCache.cacheQuery input output) hinvariant'
        · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hworking
          have hrejected := hinvariant randomness output
            (by simpa only [input] using hreference) (by simpa only [input] using houtput)
          rw [bind_assoc]
          refine probEvent_bind_le_of_forall_le fun attemptResult hattempt => ?_
          have hle : workingCache ≤ attemptResult.2 :=
            simulateQ_romImpl_cache_le
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))) :
                  OracleComp OracleWorld (Option (Index × (DigestTree → FtsLeaf))))
              workingCache attemptResult (by
                rw [simulateQ_romImpl_liftM]
                exact hattempt)
          have hattemptResult : attemptResult.1 = none :=
            (signAttempt_result_of_cached secretKey message randomness workingCache
              attemptResult.2 attemptResult.1 output
              (hle (by simpa only [input] using houtput)) hattempt).trans hrejected
          have hinvariant' := onlyRejectedNewMessageEntries_of_failed_attempt
            referenceCache workingCache attemptResult.2 secretKey message randomness
            hinvariant (by
              have heq : attemptResult = (none, attemptResult.2) :=
                Prod.ext hattemptResult rfl
              rw [← heq]
              exact hattempt)
          simpa only [hattemptResult, signDigestLoopContinuation] using
            ih attemptResult.2 hinvariant'
      · rw [bind_assoc]
        refine probEvent_bind_le_of_forall_le fun attemptResult hattempt => ?_
        cases hattemptResult : attemptResult.1 with
        | none =>
            have hinvariant' := onlyRejectedNewMessageEntries_of_failed_attempt
              referenceCache workingCache attemptResult.2 secretKey message randomness
              hinvariant (by
                have heq : attemptResult = (none, attemptResult.2) :=
                  Prod.ext hattemptResult rfl
                rw [← heq]
                exact hattempt)
            simpa only [hattemptResult, signDigestLoopContinuation] using
              ih attemptResult.2 hinvariant'
        | some selected =>
            rcases selected with ⟨index, leaves⟩
            have hreference' : referenceCache
                (tweakableHashInput secretKey.parameter .message
                  (messageDigestPayload secretKey.root message randomness)) ≠ none := by
              simpa only [input] using hreference
            simp [signDigestLoopContinuation, hattemptResult,
              completeFreshSelectedLoopView, freshSelectedLoopView?, hreference']

noncomputable def completeFreshTargetSignerView
    (initialCache : QueryCache HashSpec)
    (result : TargetSignerResult × QueryCache HashSpec) : ProbComp FewTimeView :=
  match freshTargetSignerView? initialCache result with
  | some view => pure view
  | none => $ᵗ FewTimeView

set_option maxRecDepth 100000 in
theorem probEvent_completeFreshTargetSignerView_le_uniform
    (secretKey : SecretKey) (message : Message)
    (initialCache : QueryCache HashSpec) (P : FewTimeView → Prop) :
    Pr[P | (simulateQ romImpl (signWithTargetView secretKey message)).run initialCache >>=
      completeFreshTargetSignerView initialCache] ≤
      Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  rw [signWithTargetView, simulateQ_bind, StateT.run_bind, bind_assoc]
  calc
    _ = Pr[P |
        (simulateQ romImpl (signDigestLoop digestAttemptLimit secretKey message)).run
          initialCache >>= completeFreshSelectedLoopView initialCache secretKey message] := by
      apply probEvent_bind_congr
      intro loopResult _hloop
      cases hloopResult : loopResult.1 with
      | none =>
          simp [hloopResult, completeFreshTargetSignerView,
            freshTargetSignerView?, completeFreshSelectedLoopView,
            freshSelectedLoopView?]
      | some selected =>
          rcases selected with ⟨randomness, index, leaves⟩
          simp only [simulateQ_bind, StateT.run_bind, bind_assoc,
            simulateQ_pure, StateT.run_pure, pure_bind]
          simp only [completeFreshTargetSignerView, freshTargetSignerView?]
          rw [probEvent_bind_const]
          rw [probFailure_eq_zero' inferInstance]
          simp only [tsub_zero, one_mul]
          by_cases hfresh : initialCache
              (tweakableHashInput secretKey.parameter .message
                (messageDigestPayload secretKey.root message randomness)) = none
          · simp [completeFreshSelectedLoopView, freshSelectedLoopView?,
              hloopResult, hfresh]
          · simp [completeFreshSelectedLoopView, freshSelectedLoopView?,
              hloopResult, hfresh]
    _ ≤ _ := probEvent_completeFreshSelectedLoopView_le_uniform digestAttemptLimit
      secretKey message initialCache initialCache P
        (onlyRejectedNewMessageEntries_self initialCache secretKey message)

theorem tsum_probOutput_signWithTargetView_completed_le_expected
    (secretKey : SecretKey) (message : Message)
    (initialCache : QueryCache HashSpec)
    (cost : (TargetSignerResult × QueryCache HashSpec) → ℝ≥0∞)
    (risk : FewTimeView → ℝ≥0∞)
    (hnone : ∀ signerResult ∈ support
        ((simulateQ romImpl (signWithTargetView secretKey message)).run initialCache),
      freshTargetSignerView? initialCache signerResult = none →
        cost signerResult ≤
          ∑ view, Pr[fun value : FewTimeView => value = view |
            ($ᵗ FewTimeView : ProbComp FewTimeView)] * risk view)
    (hsome : ∀ signerResult ∈ support
        ((simulateQ romImpl (signWithTargetView secretKey message)).run initialCache),
      ∀ view, freshTargetSignerView? initialCache signerResult = some view →
        cost signerResult ≤ risk view) :
    (∑' signerResult,
      Pr[= signerResult |
        (simulateQ romImpl (signWithTargetView secretKey message)).run initialCache] *
          cost signerResult) ≤
      ∑ view, Pr[fun value : FewTimeView => value = view |
        ($ᵗ FewTimeView : ProbComp FewTimeView)] * risk view := by
  let signerComp :=
    (simulateQ romImpl (signWithTargetView secretKey message)).run initialCache
  let uniformRisk := ∑ view, Pr[fun value : FewTimeView => value = view |
    ($ᵗ FewTimeView : ProbComp FewTimeView)] * risk view
  calc
    (∑' signerResult, Pr[= signerResult | signerComp] * cost signerResult) ≤
        ∑' signerResult, Pr[= signerResult | signerComp] *
          match freshTargetSignerView? initialCache signerResult with
          | some view => risk view
          | none => uniformRisk := by
      apply ENNReal.tsum_le_tsum
      intro signerResult
      by_cases hsupport : signerResult ∈ support signerComp
      · apply mul_le_mul' le_rfl
        cases hview : freshTargetSignerView? initialCache signerResult with
        | none => exact hnone signerResult hsupport hview
        | some view => exact hsome signerResult hsupport view hview
      · rw [probOutput_eq_zero_of_not_mem_support hsupport]
        simp
    _ = ∑' view,
        Pr[= view | signerComp >>= completeFreshTargetSignerView initialCache] *
          risk view := by
      rw [tsum_probOutput_bind_mul]
      apply tsum_congr
      intro signerResult
      congr 1
      cases hview : freshTargetSignerView? initialCache signerResult with
      | none =>
          simp [completeFreshTargetSignerView, hview, uniformRisk,
            probEvent_eq_eq_probOutput, tsum_fintype]
      | some view =>
          simp [completeFreshTargetSignerView, hview]
    _ ≤ ∑' view, Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] * risk view := by
      apply ENNReal.tsum_le_tsum
      intro view
      apply mul_le_mul' _ le_rfl
      rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
      exact probEvent_completeFreshTargetSignerView_le_uniform secretKey message
        initialCache (fun value => value = view)
    _ = _ := by simp only [tsum_fintype, probEvent_eq_eq_probOutput]

end SphincsSecurity.Concrete
