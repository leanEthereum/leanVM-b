import SphincsSecurity.Proof.FewTimeFresh

/-!
# Signer selection witnesses for target monitoring

This richer proof-only signer retains the exact selected message-digest input. Forgetting that input
recovers `signWithView`. It lets a later monitor recognize a fresh selected view even when signature
construction returns `none`.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

abbrev TargetSignerResult := Option Signature × Option (HashInput × FewTimeView)

def targetSignerResultView (result : TargetSignerResult) :
    Option Signature × Option FewTimeView :=
  (result.1, result.2.map Prod.snd)

noncomputable def signWithTargetView (secretKey : SecretKey) (message : Message) :
    OracleComp OracleWorld TargetSignerResult := do
  match ← signDigestLoop digestAttemptLimit secretKey message with
  | none => pure (none, none)
  | some (randomness, index, leaves) => do
      let signature ← liftM (signAfterDigest secretKey randomness index leaves)
      let input := tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)
      pure (signature, some (input, selectedFewTimeView index leaves))

theorem signWithTargetView_projection (secretKey : SecretKey) (message : Message) :
    targetSignerResultView <$> signWithTargetView secretKey message =
      signWithView secretKey message := by
  simp only [signWithTargetView, signWithView, map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro loopResult
  cases loopResult with
  | none => simp [targetSignerResultView]
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      simp [targetSignerResultView]

theorem simulateQ_signWithTargetView_projection_run
    (secretKey : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (fun result => (targetSignerResultView result.1, result.2)) <$>
        (simulateQ romImpl (signWithTargetView secretKey message)).run cache =
      (simulateQ romImpl (signWithView secretKey message)).run cache := by
  calc
    _ = (simulateQ romImpl
        (targetSignerResultView <$> signWithTargetView secretKey message)).run cache := by
      rw [simulateQ_map, StateT.run_map]
    _ = _ := by rw [signWithTargetView_projection]

def freshTargetSignerView? (initialCache : QueryCache HashSpec)
    (result : TargetSignerResult × QueryCache HashSpec) : Option FewTimeView :=
  match result.1.2 with
  | none => none
  | some (input, view) => if initialCache input = none then some view else none

def FreshTargetSignerView (initialCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (P : FewTimeView → Prop)
    (result : TargetSignerResult × QueryCache HashSpec) : Prop :=
  ∃ randomness index leaves,
    result.1.2 = some
      (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness),
        selectedFewTimeView index leaves)
      ∧ initialCache (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)) = none
      ∧ P (selectedFewTimeView index leaves)

theorem freshTargetSignerView?_eq_some_iff
    (initialCache : QueryCache HashSpec) (secretKey : SecretKey) (message : Message)
    (result : TargetSignerResult × QueryCache HashSpec) (view : FewTimeView)
    (hmem : result ∈ support
      ((simulateQ romImpl (signWithTargetView secretKey message)).run initialCache)) :
    freshTargetSignerView? initialCache result = some view ↔
      FreshTargetSignerView initialCache secretKey message (fun value => value = view) result := by
  rw [signWithTargetView, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨loopResult, loopCache⟩, _, hfinish⟩ := hmem
  cases loopResult with
  | none =>
      have heq : result = ((none, none), loopCache) := by
        simpa only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hfinish
      subst result
      simp [freshTargetSignerView?, FreshTargetSignerView]
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hfinish
      obtain ⟨⟨signature, signatureCache⟩, _, hpure⟩ := hfinish
      have heq : result =
          ((signature, some
            (tweakableHashInput secretKey.parameter .message
              (messageDigestPayload secretKey.root message randomness),
              selectedFewTimeView index leaves)), signatureCache) := by
        simpa only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hpure
      subst result
      simp only [freshTargetSignerView?, FreshTargetSignerView]
      by_cases hfresh : initialCache
          (tweakableHashInput secretKey.parameter .message
            (messageDigestPayload secretKey.root message randomness)) = none
      · constructor
        · intro hclassified
          have hview : selectedFewTimeView index leaves = view := by
            simpa only [hfresh, if_pos, Option.some.injEq] using hclassified
          exact ⟨randomness, index, leaves, rfl, hfresh, hview⟩
        · rintro ⟨foundRandomness, foundIndex, foundLeaves, hselected, hmiss, hview⟩
          have hfields := Prod.mk.inj (Option.some.inj hselected)
          rw [hfresh]
          exact congrArg some (hfields.2.trans hview)
      · constructor
        · intro hclassified
          simp [hfresh] at hclassified
        · rintro ⟨foundRandomness, foundIndex, foundLeaves, hselected, hmiss, _⟩
          have hinput := (Prod.mk.inj (Option.some.inj hselected)).1
          have hpayload := (tweakableHashInput_injective secretKey.parameter
            (by trivial) (by trivial) hinput).2
          have hrandomness := (messageDigestPayload_injective secretKey.root hpayload).2
          rw [← hrandomness] at hmiss
          exact (hfresh hmiss).elim

set_option maxRecDepth 100000 in
theorem probEvent_signWithTargetView_fresh_le_uniform
    (secretKey : SecretKey) (message : Message)
    (initialCache : QueryCache HashSpec) (P : FewTimeView → Prop) :
    Pr[FreshTargetSignerView initialCache secretKey message P |
      (simulateQ romImpl (signWithTargetView secretKey message)).run initialCache] ≤
      Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  rw [signWithTargetView, simulateQ_bind, StateT.run_bind]
  refine (probEvent_bind_le_probEvent
    (p := FreshSelectedView initialCache secretKey message P) ?_).trans
    (probEvent_signDigestLoop_freshSelectedView_le_uniform digestAttemptLimit
      secretKey message initialCache initialCache P
      (onlyRejectedNewMessageEntries_self initialCache secretKey message))
  intro loopResult _hloop hnotFresh
  cases hloopResult : loopResult.1 with
  | none =>
      refine probEvent_eq_zero ?_
      intro result hresult hevent
      have hresultEq : result = ((none, none), loopResult.2) := by
        simpa only [hloopResult, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hresult
      obtain ⟨randomness, index, leaves, hselected, _, _⟩ := hevent
      rw [hresultEq] at hselected
      simp at hselected
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      refine probEvent_eq_zero ?_
      intro result hresult hevent
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨⟨signature, signatureCache⟩, _, hpure⟩ := hresult
      have hpureEq : result =
          ((signature, some
            (tweakableHashInput secretKey.parameter .message
              (messageDigestPayload secretKey.root message randomness),
              selectedFewTimeView index leaves)), signatureCache) := by
        simpa only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hpure
      obtain ⟨foundRandomness, foundIndex, foundLeaves, hselected, hmiss, hP⟩ := hevent
      have hfields := Prod.mk.inj (Option.some.inj (hselected.symm.trans
        (congrArg (fun value => value.1.2) hpureEq)))
      have hinput := hfields.1
      have hpayload := (tweakableHashInput_injective secretKey.parameter
        (by trivial) (by trivial) hinput).2
      have hrandomness := (messageDigestPayload_injective secretKey.root hpayload).2
      have hview : selectedFewTimeView foundIndex foundLeaves =
          selectedFewTimeView index leaves := hfields.2
      apply hnotFresh
      refine ⟨randomness, index, leaves, hloopResult, ?_, ?_⟩
      · rw [← hrandomness]
        exact hmiss
      · rw [← hview]
        exact hP

theorem probEvent_freshTargetSignerView?_eq_some_le_uniform
    (secretKey : SecretKey) (message : Message)
    (initialCache : QueryCache HashSpec) (view : FewTimeView) :
    Pr[fun result => freshTargetSignerView? initialCache result = some view |
      (simulateQ romImpl (signWithTargetView secretKey message)).run initialCache] ≤
      Pr[fun value : FewTimeView => value = view |
        ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  calc
    _ = Pr[FreshTargetSignerView initialCache secretKey message (fun value => value = view) |
        (simulateQ romImpl (signWithTargetView secretKey message)).run initialCache] := by
      apply probEvent_congr'
      · intro result hmem
        exact freshTargetSignerView?_eq_some_iff initialCache secretKey message result view hmem
      · rfl
    _ ≤ _ := probEvent_signWithTargetView_fresh_le_uniform secretKey message initialCache _

end SphincsSecurity.Concrete
