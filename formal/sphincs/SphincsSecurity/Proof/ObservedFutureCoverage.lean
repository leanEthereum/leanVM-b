import SphincsSecurity.Proof.FutureCoverage
import SphincsSecurity.Proof.ObservedSignerOccupancy

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem mem_uncovered_eligibleSigningViews (answers : HashInput → Option HashOutput) (root : Digest)
    (payload : HashInput) (log : QueryLog SigningSpec) (target : FewTimeView) (tree : FtsTree) :
    tree ∈ uncoveredFewTimeTrees (eligibleSigningViews answers root payload log) target ↔
      ¬ ∃ entry ∈ log, ∃ view, eligibleSigningView? answers root payload entry = some view ∧
        view.1 = target.1 ∧ view.2 tree = target.2 tree := by
  simp only [uncoveredFewTimeTrees, Finset.mem_filter, Finset.mem_univ, true_and]
  apply not_congr
  constructor
  · rintro ⟨slot, view, hview, hi, hl⟩
    exact ⟨log.get slot, List.get_mem _ _, view, hview, hi, hl⟩
  · rintro ⟨entry, hentry, view, hview, hi, hl⟩
    obtain ⟨slot, hslot⟩ := List.mem_iff_get.mp hentry
    exact ⟨slot, view, by simpa only [eligibleSigningViews, hslot] using hview, hi, hl⟩

theorem uncovered_eligibleSigningViews_append_none (answers : HashInput → Option HashOutput) (root : Digest)
    (payload : HashInput) (log : QueryLog SigningSpec) (entry : SigningEntry) (target : FewTimeView)
    (hnone : eligibleSigningView? answers root payload entry = none) :
    uncoveredFewTimeTrees (eligibleSigningViews answers root payload (log ++ [entry])) target =
      uncoveredFewTimeTrees (eligibleSigningViews answers root payload log) target := by
  ext tree
  simp only [mem_uncovered_eligibleSigningViews, List.mem_append, List.mem_singleton,
    or_and_right, exists_or, exists_eq_left, hnone, reduceCtorEq, false_and, exists_false, or_false]

theorem uncovered_eligibleSigningViews_append_some (answers : HashInput → Option HashOutput) (root : Digest)
    (payload : HashInput) (log : QueryLog SigningSpec) (entry : SigningEntry) (target source : FewTimeView)
    (hsome : eligibleSigningView? answers root payload entry = some source) :
    uncoveredFewTimeTrees (eligibleSigningViews answers root payload (log ++ [entry])) target =
      remainingFewTimeTrees (uncoveredFewTimeTrees (eligibleSigningViews answers root payload log) target) target source := by
  ext tree
  simp only [remainingFewTimeTrees, Finset.mem_filter, mem_uncovered_eligibleSigningViews,
    List.mem_append, List.mem_singleton, or_and_right, exists_or, exists_eq_left, hsome,
    Option.some.injEq, exists_eq_left', not_or]

noncomputable def observedTargetFutureCoverage (remaining : Nat) (parameter : PublicParameter)
    (root : Digest) (payload : HashInput) (target : FewTimeView)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) : ENNReal :=
  futureFewTimeCoverage remaining
    (uncoveredFewTimeTrees (eligibleSigningViews (messageAnswers parameter cache) root payload log) target) target

theorem observedTargetFutureCoverage_cache_stable (remaining : Nat) (parameter : PublicParameter)
    (root : Digest) (payload : HashInput) (target : FewTimeView)
    (before after : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached parameter before root log) :
    observedTargetFutureCoverage remaining parameter root payload target after log =
      observedTargetFutureCoverage remaining parameter root payload target before log := by
  have hstable : eligibleSigningViews (messageAnswers parameter after) root payload log =
      eligibleSigningViews (messageAnswers parameter before) root payload log := by
    funext slot
    exact eligibleSigningView?_cache_stable parameter root before after hcache payload (log.get slot)
      (hsigned _ (List.get_mem _ _))
  simp only [observedTargetFutureCoverage, hstable]

theorem signWithView_observedTargetFutureCoverage_le (remaining : Nat) (key : SecretKey)
    (message : Message) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    observedTargetFutureCoverage remaining key.parameter key.root payload target result.2
      (log ++ [⟨message, result.1.1⟩]) ≤
      observedTargetFutureCoverage remaining key.parameter key.root payload target before log +
        successfulSignerViewWeight
          (futureFewTimeCoverageIncrement remaining
            (uncoveredFewTimeTrees (eligibleSigningViews (messageAnswers key.parameter before) key.root payload log) target) target) result := by
  have hcache := simulateQ_romImpl_cache_le (signWithView key message) before result hresult
  have hstable : eligibleSigningViews (messageAnswers key.parameter result.2) key.root payload log =
      eligibleSigningViews (messageAnswers key.parameter before) key.root payload log := by
    funext slot
    exact eligibleSigningView?_cache_stable key.parameter key.root before result.2 hcache payload (log.get slot)
      (hsigned _ (List.get_mem _ _))
  unfold observedTargetFutureCoverage
  cases hresponse : result.1.1 with
  | none =>
      rw [uncovered_eligibleSigningViews_append_none _ _ _ _ _ _ (by simp [eligibleSigningView?]), hstable]
      simp only [successfulSignerViewWeight, hresponse, add_zero, le_refl]
  | some signature =>
      have hresult' : ((some signature, result.1.2), result.2) ∈ support
          ((simulateQ romImpl (signWithView key message)).run before) := by
        have heq : result = ((some signature, result.1.2), result.2) := Prod.ext (Prod.ext hresponse rfl) rfl
        rwa [heq] at hresult
      obtain ⟨output, houtput, _, hview⟩ := signWithView_successful_cached_output key message before result.2 signature result.1.2 hresult'
      simp only [successfulSignerViewWeight, hresponse, hview]
      by_cases hsame : messageDigestPayload key.root message signature.randomness = payload
      · rw [uncovered_eligibleSigningViews_append_none _ _ _ _ _ _ (by simp [eligibleSigningView?, hsame]), hstable]
        exact le_self_add
      · have hsome : eligibleSigningView? (messageAnswers key.parameter result.2) key.root payload ⟨message, some signature⟩ =
            some (hashOutputFewTimeView output) := by
          simp [eligibleSigningView?, observedSigningView?, messageAnswers, hsame, houtput]
        rw [uncovered_eligibleSigningViews_append_some _ _ _ _ _ _ _ hsome, hstable,
          futureFewTimeCoverage_add_increment]

noncomputable def targetFutureCoverageReuseCharge (remaining : Nat) (key : SecretKey)
    (message : Message) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView) (q : Nat) : ENNReal :=
  (∑' source, cachedMessageEntryCountWhere before key.parameter key.root message (· = source) *
    futureFewTimeCoverageIncrement remaining
      (uncoveredFewTimeTrees (eligibleSigningViews (messageAnswers key.parameter before) key.root payload log) target) target source) *
    digestReuseWeight q

theorem expected_signWithView_observedTargetFutureCoverage_le (remaining : Nat) (key : SecretKey)
    (message : Message) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      observedTargetFutureCoverage remaining key.parameter key.root payload target result.2
        (log ++ [⟨message, result.1.1⟩])) ≤
      observedTargetFutureCoverage (remaining + 1) key.parameter key.root payload target before log +
        targetFutureCoverageReuseCharge remaining key message before log payload target q := by
  let required := uncoveredFewTimeTrees (eligibleSigningViews (messageAnswers key.parameter before) key.root payload log) target
  let weight := futureFewTimeCoverageIncrement remaining required target
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        (futureFewTimeCoverage remaining required target + successfulSignerViewWeight weight result) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
      · exact mul_le_mul' le_rfl (signWithView_observedTargetFutureCoverage_le remaining key message before log payload target hsigned result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ ≤ futureFewTimeCoverage remaining required target +
        (∑' source, Pr[SuccessfulSignerViewSatisfies (· = source) |
          (simulateQ romImpl (signWithView key message)).run before] * weight source) := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, expected_successfulSignerViewWeight_eq]
      exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl
    _ ≤ futureFewTimeCoverage remaining required target +
        ((∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight source) +
          targetFutureCoverageReuseCharge remaining key message before log payload target q) :=
      add_le_add le_rfl (expected_successfulSignerView_weight_le weight key message before q hq hcache)
    _ = _ := by
      rw [← add_assoc, expected_futureFewTimeCoverageIncrement]
      rfl

end SphincsSecurity.Concrete
