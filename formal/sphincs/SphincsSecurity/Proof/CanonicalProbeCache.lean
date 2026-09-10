import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.CanonicalProbeKernel
import SphincsSecurity.Proof.RetainedObservation

namespace SphincsSecurity.Concrete.CanonicalProbeRouting

open _root_.OracleComp HiddenLabelObservation RetainedObservation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev ExternalCache := HashInput → Option HashOutput

def CacheClean (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels) (cache : ExternalCache) : Prop :=
  ∀ input answer, cache input = some answer → ¬Bad parameter words disclosed actual input answer

theorem hidden_mono (words : OtsReferenceWords) (before after : Index → FtsTree → FtsLeaf → Prop)
    (hdisclosed : ∀ index tree leaf, before index tree leaf → after index tree leaf) (coordinate : CanonicalCoordinate) :
    CanonicalCoordinate.Hidden words after coordinate → CanonicalCoordinate.Hidden words before coordinate := by
  cases coordinate with
  | otsStart => exact id
  | graph position => cases position <;> exact id
  | ftsStart index tree leaf =>
      intro hhidden hbefore
      exact hhidden (hdisclosed index tree leaf hbefore)

theorem bad_mono (parameter : PublicParameter) (words : OtsReferenceWords)
    (before after : Index → FtsTree → FtsLeaf → Prop)
    (hdisclosed : ∀ index tree leaf, before index tree leaf → after index tree leaf)
    (actual : Labels) (input : HashInput) (answer : HashOutput) :
    Bad parameter words after actual input answer → Bad parameter words before actual input answer := by
  rintro ⟨position, hat, hbad⟩
  refine ⟨position, hat, ?_⟩
  rcases hbad with ⟨⟨coordinate, hslot, hhidden⟩, hinput⟩ | houtput
  · exact Or.inl ⟨⟨coordinate, hslot, hidden_mono words before after hdisclosed coordinate hhidden⟩, hinput⟩
  · exact Or.inr houtput

theorem cacheClean_disclose (parameter : PublicParameter) (words : OtsReferenceWords)
    (before after : Index → FtsTree → FtsLeaf → Prop)
    (hdisclosed : ∀ index tree leaf, before index tree leaf → after index tree leaf)
    (actual : Labels) (cache : ExternalCache) (hclean : CacheClean parameter words before actual cache) :
    CacheClean parameter words after actual cache := by
  intro input answer hcache hbad
  exact hclean input answer hcache (bad_mono parameter words before after hdisclosed actual input answer hbad)

theorem cacheClean_empty (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels) :
    CacheClean parameter words disclosed actual (fun _ => none) := by
  intro input answer hcache
  cases hcache

theorem cacheClean_store (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels) (cache : ExternalCache)
    (hclean : CacheClean parameter words disclosed actual cache) (input : HashInput) (answer : HashOutput)
    (hsafe : ¬Bad parameter words disclosed actual input answer) :
    CacheClean parameter words disclosed actual (Function.update cache input (some answer)) := by
  intro other output hcache
  by_cases heq : other = input
  · subst other
    rw [Function.update_self] at hcache
    have heq := Option.some.inj hcache
    exact heq ▸ hsafe
  · rw [Function.update_of_ne heq] at hcache
    exact hclean other output hcache

noncomputable def stoppedCachedResponse (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels)
    (replies : CanonicalGraphLabels) (cache : ExternalCache) (input : HashInput) (outside : PMF HashOutput) : SPMF HashOutput :=
  match cache input with
  | some answer => if ¬Bad parameter words disclosed actual input answer then pure answer else failure
  | none => stoppedResponse parameter words disclosed actual replies input outside

noncomputable def routedCachedResponse (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (publicReplies : CanonicalGraphLabels) (cache : ExternalCache) (input : HashInput) (outside : PMF HashOutput) : SPMF HashOutput :=
  match cache input with
  | some answer => pure answer
  | none => routedResponse outside publicReplies actual (route parameter words disclosed known input)

theorem stoppedCachedResponse_eq_routed (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (hagrees : PublicAgreement words disclosed known actual)
    (replies publicReplies : CanonicalGraphLabels)
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden words disclosed (.graph position) →
      publicReplies position = replies position)
    (cache : ExternalCache) (hclean : CacheClean parameter words disclosed actual cache)
    (input : HashInput) (outside : PMF HashOutput) :
    stoppedCachedResponse parameter words disclosed actual replies cache input outside =
      routedCachedResponse parameter words disclosed known actual publicReplies cache input outside := by
  cases hcache : cache input with
  | none =>
      simp only [stoppedCachedResponse, routedCachedResponse, hcache]
      exact stoppedResponse_route parameter words disclosed known actual hagrees replies publicReplies hreplies input outside
  | some answer =>
      simp only [stoppedCachedResponse, routedCachedResponse, hcache, if_pos (hclean input answer hcache)]

theorem stoppedCachedResponse_safe (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels)
    (replies : CanonicalGraphLabels) (cache : ExternalCache) (input : HashInput) (outside : PMF HashOutput)
    (answer : HashOutput)
    (hanswer : stoppedCachedResponse parameter words disclosed actual replies cache input outside answer ≠ 0) :
    ¬Bad parameter words disclosed actual input answer := by
  cases hcache : cache input with
  | none =>
      simp only [stoppedCachedResponse, hcache, stoppedResponse_apply] at hanswer
      by_contra hbad
      simp only [not_not.mpr hbad, if_false] at hanswer
      exact hanswer rfl
  | some cached =>
      simp only [stoppedCachedResponse, hcache] at hanswer
      split at hanswer
      · rename_i hsafe
        by_cases heq : cached = answer
        · exact heq ▸ hsafe
        · simp only [SPMF.pure_apply, if_neg (Ne.symm heq)] at hanswer
          exact (hanswer rfl).elim
      · simp only [SPMF.failure_apply] at hanswer
        exact (hanswer rfl).elim

structure ExternalMemory where
  cache : ExternalCache
  hashCalls : Nat
  probes : Nat

noncomputable def charge (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (input : HashInput)
    (memory : ExternalMemory) : ExternalMemory :=
  { memory with
    hashCalls := memory.hashCalls + 1
    probes := memory.probes + match memory.cache input with
      | some _ => 0
      | none => match route parameter words disclosed known input with
        | .probe _ => 1
        | _ => 0 }

noncomputable def storeReply (memory : ExternalMemory) (input : HashInput) (answer : HashOutput) : ExternalMemory :=
  { memory with cache := Function.update memory.cache input (some answer) }

theorem charge_probes_le (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (input : HashInput) (memory : ExternalMemory) :
    (charge parameter words disclosed known input memory).probes ≤ memory.probes + 1 := by
  unfold charge
  cases hcache : memory.cache input with
  | some answer => exact Nat.le_add_right _ _
  | none => cases route parameter words disclosed known input <;> simp

noncomputable def stoppedStep (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (replies : CanonicalGraphLabels) (input : HashInput) (outside : PMF HashOutput) (memory : ExternalMemory) :
    SPMF (Option HashOutput × ExternalMemory) :=
  let paid := charge parameter words disclosed known input memory
  observe (stoppedCachedResponse parameter words disclosed actual replies memory.cache input outside)
    (pure (none, paid)) (fun answer => pure (some answer, storeReply paid input answer))

noncomputable def routedStep (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (publicReplies : CanonicalGraphLabels) (input : HashInput) (outside : PMF HashOutput) (memory : ExternalMemory) :
    SPMF (Option HashOutput × ExternalMemory) :=
  let paid := charge parameter words disclosed known input memory
  observe (routedCachedResponse parameter words disclosed known actual publicReplies memory.cache input outside)
    (pure (none, paid)) (fun answer => pure (some answer, storeReply paid input answer))

theorem stoppedStep_eq_routed (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (hagrees : PublicAgreement words disclosed known actual)
    (replies publicReplies : CanonicalGraphLabels)
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden words disclosed (.graph position) →
      publicReplies position = replies position)
    (input : HashInput) (outside : PMF HashOutput) (memory : ExternalMemory)
    (hclean : CacheClean parameter words disclosed actual memory.cache) :
    stoppedStep parameter words disclosed known actual replies input outside memory =
      routedStep parameter words disclosed known actual publicReplies input outside memory := by
  unfold stoppedStep routedStep
  rw [stoppedCachedResponse_eq_routed parameter words disclosed known actual hagrees replies publicReplies hreplies
    memory.cache hclean input outside]

theorem stoppedStep_preserves {parameter : PublicParameter} {words : OtsReferenceWords}
    {disclosed : Index → FtsTree → FtsLeaf → Prop} {known actual : Labels}
    {replies : CanonicalGraphLabels} {input : HashInput} {outside : PMF HashOutput} {memory : ExternalMemory}
    (hclean : CacheClean parameter words disclosed actual memory.cache)
    (result : Option HashOutput × ExternalMemory)
    (hresult : stoppedStep parameter words disclosed known actual replies input outside memory result ≠ 0) :
    CacheClean parameter words disclosed actual result.2.cache ∧
      result.2.hashCalls = memory.hashCalls + 1 ∧
      result.2.probes = (charge parameter words disclosed known input memory).probes := by
  rw [stoppedStep, observe_nonzero] at hresult
  rcases hresult with ⟨_, hresult⟩ | ⟨answer, hanswer, hresult⟩
  · simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
    subst result
    exact ⟨hclean, rfl, rfl⟩
  · simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
    subst result
    exact ⟨cacheClean_store parameter words disclosed actual memory.cache hclean input answer
      (stoppedCachedResponse_safe parameter words disclosed actual replies memory.cache input outside answer hanswer), rfl, rfl⟩

theorem stoppedStep_probes_le_hashCalls {parameter : PublicParameter} {words : OtsReferenceWords}
    {disclosed : Index → FtsTree → FtsLeaf → Prop} {known actual : Labels}
    {replies : CanonicalGraphLabels} {input : HashInput} {outside : PMF HashOutput} {memory : ExternalMemory}
    (hclean : CacheClean parameter words disclosed actual memory.cache) (hinitial : memory.probes ≤ memory.hashCalls)
    (result : Option HashOutput × ExternalMemory)
    (hresult : stoppedStep parameter words disclosed known actual replies input outside memory result ≠ 0) :
    result.2.probes ≤ result.2.hashCalls := by
  have h := stoppedStep_preserves hclean result hresult
  rw [h.2.1, h.2.2]
  exact (charge_probes_le parameter words disclosed known input memory).trans (Nat.add_le_add_right hinitial 1)

theorem stoppedStep_bind_const {Result : Type} (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (replies : CanonicalGraphLabels) (input : HashInput) (outside : PMF HashOutput) (memory : ExternalMemory)
    (next : SPMF Result) :
    (stoppedStep parameter words disclosed known actual replies input outside memory >>= fun _ => next) = next := by
  simp only [stoppedStep, observe_bind, pure_bind]
  exact observe_const _ next

end SphincsSecurity.Concrete.CanonicalProbeRouting
