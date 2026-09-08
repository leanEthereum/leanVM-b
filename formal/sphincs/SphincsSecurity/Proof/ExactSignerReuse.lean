import SphincsSecurity.Proof.CachedDigestRate
import SphincsSecurity.Proof.SignerInputWeight

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signWithView signDigestLoop signAfterDigest

theorem probEvent_signWithView_prehitSuccessful_le_selected
    (secretKey : SecretKey) (message : Message) (referenceCache initialCache : QueryCache HashSpec)
    (P : FewTimeView → Prop) (hreference : referenceCache ≤ initialCache) :
    Pr[PrehitSuccessfulSignerView referenceCache secretKey message P |
      (simulateQ romImpl (signWithView secretKey message)).run initialCache] ≤
      Pr[PrehitSelectedView referenceCache secretKey message P |
        (simulateQ romImpl (signDigestLoop digestAttemptLimit secretKey message)).run initialCache] := by
  rw [signWithView, simulateQ_bind, StateT.run_bind]
  refine probEvent_bind_le_probEvent (p := PrehitSelectedView referenceCache secretKey message P) ?_
  intro loopResult hloop hnotPrehit
  cases hloopResult : loopResult.1 with
  | none =>
      refine probEvent_eq_zero ?_
      intro result hresult hevent
      have hresultEq : result = ((none, none), loopResult.2) := by
        simpa only [hloopResult, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hresult
      obtain ⟨signature, view, hsuccessful, _⟩ := hevent
      rw [hresultEq] at hsuccessful
      simp at hsuccessful
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      refine probEvent_eq_zero ?_
      intro result hresult hevent
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨⟨signatureResult, signatureCache⟩, hsignature, hpure⟩ := hresult
      have hpureEq : result =
          ((signatureResult, some (selectedFewTimeView index leaves)), signatureCache) := by
        simpa only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hpure
      obtain ⟨signature, view, hsuccessful, output, hcached, hP⟩ := hevent
      have hpureFirst := congrArg Prod.fst hpureEq
      have hsignatureResult : signatureResult = some signature := by
        have hfirst := congrArg Prod.fst (hpureFirst.symm.trans hsuccessful)
        simpa using hfirst
      have hsignature' : (some signature, signatureCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec _)
            (signAfterDigest secretKey randomness index leaves)).run loopResult.2) := by
        rw [hsignatureResult] at hsignature
        simpa only [simulateQ_romImpl_liftM] using hsignature
      have hrandomness := signAfterDigest_support_some_randomness secretKey randomness
        index leaves loopResult.2 signatureCache signature hsignature'
      have hcached' : initialCache
          (tweakableHashInput secretKey.parameter .message
            (messageDigestPayload secretKey.root message randomness)) = some output := by
        apply hreference
        rw [← hrandomness]
        exact hcached
      have hloop' : (some (randomness, index, leaves), loopResult.2) ∈ support
          ((simulateQ romImpl
            (signDigestLoop digestAttemptLimit secretKey message)).run initialCache) := by
        have heq : loopResult = (some (randomness, index, leaves), loopResult.2) :=
          Prod.ext hloopResult rfl
        rw [← heq]
        exact hloop
      have hresultOutput := signDigestLoop_initial_cached_result
        digestAttemptLimit secretKey message randomness index leaves initialCache loopResult.2
        output hcached' hloop'
      apply hnotPrehit
      exact ⟨randomness, index, leaves, hloopResult, output, by
        rw [← hrandomness]
        exact hcached, hresultOutput, hP⟩

theorem probEvent_signWithView_prehitSuccessful_le_count_mul_exactWeight
    (key : SecretKey) (message : Message) (referenceCache initialCache : QueryCache HashSpec)
    (P : FewTimeView → Prop) (hreference : referenceCache ≤ initialCache) :
    Pr[PrehitSuccessfulSignerView referenceCache key message P |
      (simulateQ romImpl (signWithView key message)).run initialCache] ≤
      cachedMessageEntryCountWhere referenceCache key.parameter key.root message P * exactDigestReuseWeight key message initialCache := by
  apply (probEvent_signWithView_prehitSuccessful_le_selected key message referenceCache initialCache P hreference).trans_eq
  rw [probEvent_signDigestLoop_prehit_eq_rate_mul_attempts digestAttemptLimit key message referenceCache initialCache hreference,
    cachedDigestAttemptRate_eq_count, exactDigestReuseWeight]
  ring

theorem probEvent_signWithView_fixedPrehit_le_exactWeight
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (target : HashInput) (P : FewTimeView → Prop) :
    Pr[PrehitSuccessfulSignerView (onlyInputCache cache target) key message P |
      (simulateQ romImpl (signWithView key message)).run cache] ≤ exactDigestReuseWeight key message cache := by
  have h := probEvent_signWithView_prehitSuccessful_le_count_mul_exactWeight key message (onlyInputCache cache target) cache P
    (onlyInputCache_le cache target)
  exact h.trans ((mul_le_mul' (cachedMessageEntryCountWhere_onlyInput_le_one cache target key.parameter key.root message P) le_rfl).trans_eq
    (one_mul _))

theorem expected_successfulSignerInputWeight_le_exactReuse (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      successfulSignerInputWeight key message weight result) ≤
      freshDigestSelectionProbability key message before *
        (∑' view, Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] * uniformWeight view) +
        (∑' input, cachedSignerInputWeight key message before weight input) * exactDigestReuseWeight key message before :=
  expected_successfulSignerInputWeight_le_freshMass_add_reuseWeight key message before weight uniformWeight hweight
    (exactDigestReuseWeight key message before) (fun input =>
      probEvent_signWithView_fixedPrehit_le_exactWeight key message before input (fun _ => True))

end SphincsSecurity.Concrete
