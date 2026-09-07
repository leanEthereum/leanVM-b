import SphincsSecurity.Proof.TargetMixedGrowthPolynomial

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def normalizedTargetLogIncrement (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset FtsTree) (source : FewTimeView) : ENNReal :=
  ∑ selected ∈ required.powerset.erase ∅, normalizedSourceSubsetMatch target source selected *
    normalizedTargetLogProduct key cache log payload target (required \ selected)

theorem normalizedTargetLogProduct_add_increment (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset FtsTree) (source : FewTimeView) :
    normalizedTargetLogProduct key cache log payload target required + normalizedTargetLogIncrement key cache log payload target required source =
      ∏ tree ∈ required, (normalizedTargetLogMatch key cache log payload target tree + normalizedSourceSubsetMatch target source {tree}) := by
  rw [targetLogProduct_insert_expansion, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset required)]
  simp only [normalizedSourceSubsetMatch, Finset.card_empty, pow_zero, Nat.cast_one, sourceSubsetMatch,
    Finset.prod_empty, Nat.cast_one, one_mul, Finset.sdiff_empty, normalizedTargetLogIncrement, normalizedTargetLogProduct]

theorem normalizedTargetLogProduct_append_none (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (entry : SigningEntry) (payload : HashInput) (target : FewTimeView) (required : Finset FtsTree)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hnone : eligibleSigningView? (messageAnswers key.parameter after) key.root payload entry = none) :
    normalizedTargetLogProduct key after (log ++ [entry]) payload target required =
      normalizedTargetLogProduct key before log payload target required := by
  apply Finset.prod_congr rfl
  intro tree _
  have hstep := targetTreeMatchCount_log_append_singleton log entry
    (eligibleSigningView? (messageAnswers key.parameter after) key.root payload) target tree
  change targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter after) key.root payload (log ++ [entry])) target tree =
    targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter after) key.root payload log) target tree + _ at hstep
  simp only [hnone, reduceCtorEq, false_and, exists_false, if_false, add_zero,
    eligibleSigningViews_cache_stable key before after log payload hcache hsigned] at hstep
  exact congrArg (fun count : Nat => (Fintype.card FtsLeaf : ENNReal) * (count : ENNReal)) hstep

theorem signWithView_normalizedTargetLogProduct_le_input (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset FtsTree)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) payload target required ≤
      normalizedTargetLogProduct key before log payload target required +
        successfulSignerInputWeight key message (fun input source =>
          if input = tweakableHashInput key.parameter .message payload then 0 else normalizedTargetLogIncrement key before log payload target required source) result := by
  have hcache := simulateQ_romImpl_cache_le (signWithView key message) before result hresult
  cases hresponse : result.1.1 with
  | none =>
      rw [normalizedTargetLogProduct_append_none key before result.2 log _ payload target required hcache hsigned (by simp [eligibleSigningView?])]
      simp only [successfulSignerInputWeight, hresponse, add_zero, le_refl]
  | some signature =>
      have hresult' : ((some signature, result.1.2), result.2) ∈ support ((simulateQ romImpl (signWithView key message)).run before) := by
        have heq : result = ((some signature, result.1.2), result.2) := Prod.ext (Prod.ext hresponse rfl) rfl
        rwa [heq] at hresult
      obtain ⟨output, _, _, hview⟩ := signWithView_successful_cached_output key message before result.2 signature result.1.2 hresult'
      by_cases hsame : messageDigestPayload key.root message signature.randomness = payload
      · rw [normalizedTargetLogProduct_append_none key before result.2 log _ payload target required hcache hsigned (by simp [eligibleSigningView?, hsame])]
        exact le_self_add
      · have hinput : tweakableHashInput key.parameter .message (messageDigestPayload key.root message signature.randomness) ≠
            tweakableHashInput key.parameter .message payload := by
          intro heq
          exact hsame (tweakableHashInput_injective key.parameter (by trivial) (by trivial) heq).2
        simp only [successfulSignerInputWeight, hresponse, hview, if_neg hinput]
        rw [normalizedTargetLogProduct_add_increment]
        apply Finset.prod_le_prod'
        intro tree _
        simpa only [hresponse] using signWithView_normalizedTargetLogMatch_le key message before log payload target _ tree hsigned result hresult hview

theorem expected_normalizedTargetLogIncrement (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset FtsTree) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * normalizedTargetLogIncrement key cache log payload target required source) =
      (Fintype.card Index : ENNReal)⁻¹ * ∑ selected ∈ required.powerset.erase ∅,
        normalizedTargetLogProduct key cache log payload target (required \ selected) := by
  simp only [normalizedTargetLogIncrement, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro selected hselected
  simp only [← mul_assoc, ENNReal.tsum_mul_right]
  rw [expected_normalizedSourceSubsetMatch target selected
    (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1)]

theorem cached_normalizedTargetLogIncrement (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset FtsTree) :
    cacheMessageWeight key.parameter (fun input source => if input = tweakableHashInput key.parameter .message payload then 0
      else normalizedTargetLogIncrement key cache log payload target required source) cache =
      ∑ selected ∈ required.powerset.erase ∅,
        normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload) target selected *
          normalizedTargetLogProduct key cache log payload target (required \ selected) := by
  have hpoint (input : HashInput) (source : FewTimeView) :
      (if input = tweakableHashInput key.parameter .message payload then 0 else normalizedTargetLogIncrement key cache log payload target required source) =
      ∑ selected ∈ required.powerset.erase ∅,
        (if input = tweakableHashInput key.parameter .message payload then 0 else normalizedSourceSubsetMatch target source selected) *
          normalizedTargetLogProduct key cache log payload target (required \ selected) := by
    unfold normalizedTargetLogIncrement
    split_ifs <;> simp only [zero_mul, Finset.sum_const_zero]
  simp only [hpoint, cacheMessageWeight_sum, cacheMessageWeight_mul_right, normalizedCachedTargetSubsetMatch_eq_weight]

theorem expected_signWithView_normalizedTargetLogProduct_le (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset FtsTree)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) payload target required) ≤
      normalizedTargetLogProduct key before log payload target required +
        (Fintype.card Index : ENNReal)⁻¹ * (∑ selected ∈ required.powerset.erase ∅, normalizedTargetLogProduct key before log payload target (required \ selected)) +
        (∑ selected ∈ required.powerset.erase ∅,
          normalizedCachedTargetSubsetMatch key.parameter before (tweakableHashInput key.parameter .message payload) target selected *
            normalizedTargetLogProduct key before log payload target (required \ selected)) * digestReuseWeight q := by
  let weight := fun input source => if input = tweakableHashInput key.parameter .message payload then 0
    else normalizedTargetLogIncrement key before log payload target required source
  have hweight (input : HashInput) (source : FewTimeView) : weight input source ≤ normalizedTargetLogIncrement key before log payload target required source := by
    unfold weight
    split_ifs; exact bot_le; exact le_rfl
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        (normalizedTargetLogProduct key before log payload target required + successfulSignerInputWeight key message weight result) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
      · exact mul_le_mul' le_rfl (signWithView_normalizedTargetLogProduct_le_input key message before log payload target required hsigned result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ ≤ normalizedTargetLogProduct key before log payload target required +
        (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] * successfulSignerInputWeight key message weight result) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl
    _ ≤ _ := by
      have hbound := expected_successfulSignerInputWeight_le_allMessage key message before weight _ hweight q hq hcache
      simp only [weight, expected_normalizedTargetLogIncrement, cached_normalizedTargetLogIncrement] at hbound
      simpa only [add_assoc, weight] using add_le_add (le_refl (normalizedTargetLogProduct key before log payload target required)) hbound

end SphincsSecurity.Concrete
