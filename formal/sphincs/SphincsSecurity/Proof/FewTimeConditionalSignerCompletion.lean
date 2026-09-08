import SphincsSecurity.Proof.FewTimeCoverageCompletion
import SphincsSecurity.Proof.FewTimeWeightedOriginRace
import SphincsSecurity.Proof.FewTimeFreshMass

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def SuccessfulSignerViewSatisfies (P : FewTimeView → Prop)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : Prop :=
  ∃ signature view, result.1 = (some signature, some view) ∧ P view

theorem successfulSignerViewSatisfies_fresh_or_prehit (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (P : FewTimeView → Prop)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run cache))
    (hP : SuccessfulSignerViewSatisfies P result) :
    FreshSuccessfulSignerView cache key message P result ∨ PrehitSuccessfulSignerView cache key message P result := by
  obtain ⟨signature, view, hshape, hP⟩ := hP
  by_cases hfresh : cache (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message signature.randomness)) = none
  · exact Or.inl ⟨signature, view, hshape, hfresh, hP⟩
  · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hfresh
    have hresult' : ((some signature, some view), result.2) ∈ support
        ((simulateQ romImpl (signWithView key message)).run cache) := by
      have heq : result = ((some signature, some view), result.2) := Prod.ext hshape rfl
      rwa [heq] at hresult
    obtain ⟨randomness, index, leaves, loopCache, hloop, hfinish, hview⟩ :=
      signWithView_support_some key message cache result.2 signature (some view) hresult'
    have hrandomness := signAfterDigest_support_some_randomness key randomness index leaves loopCache result.2 signature hfinish
    have hcached : cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output := by
      rwa [← hrandomness]
    have hselected := signDigestLoop_initial_cached_result digestAttemptLimit key message randomness index leaves cache loopCache output hcached hloop
    have hviewOutput : view = hashOutputFewTimeView output :=
      (Option.some.inj hview).trans (signAttemptResultOfOutput_view output index leaves hselected)
    exact Or.inr ⟨signature, view, hshape, output, houtput, hviewOutput ▸ hP⟩

theorem probEvent_successfulSignerViewSatisfies_le_freshMass_mul_uniform_add_reuse
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (P : FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    Pr[SuccessfulSignerViewSatisfies P | (simulateQ romImpl (signWithView key message)).run cache] ≤
      freshDigestSelectionProbability key message cache *
        Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] +
        cachedMessageEntryCountWhere cache key.parameter key.root message P * digestReuseWeight q := by
  calc
    _ ≤ Pr[fun result => FreshSuccessfulSignerView cache key message P result ∨
        PrehitSuccessfulSignerView cache key message P result |
        (simulateQ romImpl (signWithView key message)).run cache] :=
      probEvent_mono (fun result hresult hP => successfulSignerViewSatisfies_fresh_or_prehit key message cache P result hresult hP)
    _ ≤ Pr[FreshSuccessfulSignerView cache key message P | (simulateQ romImpl (signWithView key message)).run cache] +
        Pr[PrehitSuccessfulSignerView cache key message P | (simulateQ romImpl (signWithView key message)).run cache] := probEvent_or_le _ _ _
    _ ≤ _ := add_le_add (probEvent_signWithView_freshSuccessful_le_mass_mul_uniform key message cache P)
      (probEvent_signWithView_prehitSuccessful_le_queryBudget127 key message cache cache P le_rfl q hq hcache)

theorem probEvent_successfulSignerViewSatisfies_le_uniform_add_reuse
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (P : FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    Pr[SuccessfulSignerViewSatisfies P | (simulateQ romImpl (signWithView key message)).run cache] ≤
      Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] +
        cachedMessageEntryCountWhere cache key.parameter key.root message P * digestReuseWeight q := by
  refine (probEvent_successfulSignerViewSatisfies_le_freshMass_mul_uniform_add_reuse
    key message cache P q hq hcache).trans (add_le_add ?_ le_rfl)
  simpa only [one_mul] using mul_le_mul'
    (freshDigestSelectionProbability_le_one key message cache)
    (le_refl Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)])

def CompletesSomeFewTimeTarget {α : Type} {n : Nat} (targets : Finset α)
    (views : α → Fin n → Option FewTimeView) (targetView : α → FewTimeView) (source : FewTimeView) : Prop :=
  ∃ target ∈ targets, CompletesFewTimeView (views target) (targetView target) source

theorem probEvent_uniform_completesSomeFewTimeTarget_le {α : Type} {n : Nat}
    (targets : Finset α) (views : α → Fin n → Option FewTimeView) (targetView : α → FewTimeView) :
    Pr[CompletesSomeFewTimeTarget targets views targetView | ($ᵗ FewTimeView : ProbComp FewTimeView)] ≤
      ∑ target ∈ targets, completionProbability (views target) (targetView target) := by
  change Pr[fun source => ∃ target ∈ targets, CompletesFewTimeView (views target) (targetView target) source |
    ($ᵗ FewTimeView : ProbComp FewTimeView)] ≤ _
  exact (probEvent_exists_finset_le_sum _ _ _).trans_eq (by simp_rw [probEvent_uniform_completesFewTimeView])

theorem probEvent_signer_completesSomeFewTimeTarget_le_freshMass_mul {α : Type} {n : Nat}
    (targets : Finset α) (views : α → Fin n → Option FewTimeView) (targetView : α → FewTimeView)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    Pr[SuccessfulSignerViewSatisfies (CompletesSomeFewTimeTarget targets views targetView) |
      (simulateQ romImpl (signWithView key message)).run cache] ≤
      freshDigestSelectionProbability key message cache *
        (∑ target ∈ targets, completionProbability (views target) (targetView target)) +
        cachedMessageEntryCountWhere cache key.parameter key.root message
          (CompletesSomeFewTimeTarget targets views targetView) * digestReuseWeight q :=
  (probEvent_successfulSignerViewSatisfies_le_freshMass_mul_uniform_add_reuse
    key message cache _ q hq hcache).trans
      (add_le_add (mul_le_mul' le_rfl
        (probEvent_uniform_completesSomeFewTimeTarget_le targets views targetView)) le_rfl)

theorem probEvent_signer_completesSomeFewTimeTarget_le {α : Type} {n : Nat}
    (targets : Finset α) (views : α → Fin n → Option FewTimeView) (targetView : α → FewTimeView)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    Pr[SuccessfulSignerViewSatisfies (CompletesSomeFewTimeTarget targets views targetView) |
      (simulateQ romImpl (signWithView key message)).run cache] ≤
      (∑ target ∈ targets, completionProbability (views target) (targetView target)) +
        cachedMessageEntryCountWhere cache key.parameter key.root message
          (CompletesSomeFewTimeTarget targets views targetView) * digestReuseWeight q :=
  (probEvent_successfulSignerViewSatisfies_le_uniform_add_reuse key message cache _ q hq hcache).trans
    (add_le_add (probEvent_uniform_completesSomeFewTimeTarget_le targets views targetView) le_rfl)

end SphincsSecurity.Concrete
