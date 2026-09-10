import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeFixedPrehit

/-!
# Probability composition for a direct few-time origin

A realized prehit has a fresh direct random-oracle source. If the rest of the execution can satisfy
an event only after that source returns an admissible answer with a selected view, its probability
is the source probability multiplied by the conditional bound for the rest of the execution.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem tsum_probOutput_mul_le_gated
    {Value : Type} (computation : ProbComp Value) (gate : Value → Prop)
    (cost : Value → ℝ≥0∞) (epsilon : ℝ≥0∞)
    (hoff : ∀ value ∈ support computation, ¬ gate value → cost value = 0)
    (hon : ∀ value ∈ support computation, gate value → cost value ≤ epsilon) :
    (∑' value, Pr[= value | computation] * cost value) ≤
      Pr[gate | computation] * epsilon := by
  classical
  rw [probEvent_eq_tsum_indicator, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro value
  by_cases hvalue : value ∈ support computation
  · by_cases hgate : gate value
    · simpa [hgate] using mul_le_mul' le_rfl (hon value hvalue hgate)
    · rw [hoff value hvalue hgate]
      simp [hgate]
  · rw [probOutput_eq_zero_of_not_mem_support hvalue]
    simp

theorem tsum_probOutput_mul_le_classifiedRisk
    {Value Index : Type} [Fintype Index]
    (computation : ProbComp Value) (classify : Value → Option Index)
    (risk : Index → ℝ≥0∞) (cost : Value → ℝ≥0∞)
    (hoff : ∀ value ∈ support computation, classify value = none → cost value = 0)
    (hon : ∀ value ∈ support computation, ∀ index,
      classify value = some index → cost value ≤ risk index) :
    (∑' value, Pr[= value | computation] * cost value) ≤
      ∑ index, Pr[fun value => classify value = some index | computation] * risk index := by
  classical
  calc
    ∑' value, Pr[= value | computation] * cost value ≤
        ∑' value, ∑ index,
          if classify value = some index then Pr[= value | computation] * risk index
          else 0 := by
      apply ENNReal.tsum_le_tsum
      intro value
      by_cases hvalue : value ∈ support computation
      · cases hclass : classify value with
        | none =>
            rw [hoff value hvalue hclass]
            simp
        | some index =>
            calc
              Pr[= value | computation] * cost value ≤
                  Pr[= value | computation] * risk index :=
                mul_le_mul' le_rfl (hon value hvalue index hclass)
              _ = ∑ candidate,
                  if some index = some candidate then
                    Pr[= value | computation] * risk candidate
                  else 0 := by
                rw [Finset.sum_eq_single index]
                · rw [if_pos rfl]
                · intro candidate _ hne
                  rw [if_neg]
                  exact fun heq => hne (Option.some.inj heq).symm
                · intro hnot
                  exact (hnot (Finset.mem_univ index)).elim
      · rw [probOutput_eq_zero_of_not_mem_support hvalue]
        simp
    _ = ∑ index, ∑' value,
          if classify value = some index then Pr[= value | computation] * risk index
          else 0 := by
      calc
        (∑' value, ∑ index,
            if classify value = some index then Pr[= value | computation] * risk index
            else 0) =
            ∑' value, ∑' index,
              if classify value = some index then Pr[= value | computation] * risk index
              else 0 := by simp only [tsum_fintype]
        _ = ∑' index, ∑' value,
              if classify value = some index then Pr[= value | computation] * risk index
              else 0 := ENNReal.tsum_comm
        _ = _ := by simp only [tsum_fintype]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _
      rw [probEvent_eq_tsum_indicator, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro value
      by_cases hclass : classify value = some index <;> simp [hclass]

theorem tsum_probOutput_mul_le_uniformClassifiedRisk
    {Value Index : Type} [Fintype Index]
    (computation : ProbComp Value) (classify : Value → Option Index)
    (uniform : ProbComp Index) (weight : ℝ≥0∞)
    (risk : Index → ℝ≥0∞) (cost : Value → ℝ≥0∞)
    (hpoint : ∀ index, Pr[fun value => classify value = some index | computation] ≤
      weight * Pr[fun value : Index => value = index | uniform])
    (hoff : ∀ value ∈ support computation, classify value = none → cost value = 0)
    (hon : ∀ value ∈ support computation, ∀ index,
      classify value = some index → cost value ≤ risk index) :
    (∑' value, Pr[= value | computation] * cost value) ≤
      weight * ∑ index, Pr[fun value : Index => value = index | uniform] * risk index := by
  calc
    ∑' value, Pr[= value | computation] * cost value ≤
        ∑ index, Pr[fun value => classify value = some index | computation] * risk index :=
      tsum_probOutput_mul_le_classifiedRisk computation classify risk cost hoff hon
    _ ≤ ∑ index,
        (weight * Pr[fun value : Index => value = index | uniform]) * risk index := by
      apply Finset.sum_le_sum
      intro index _
      exact mul_le_mul' (hpoint index) le_rfl
    _ = ∑ index, weight *
        (Pr[fun value : Index => value = index | uniform] * risk index) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [mul_assoc]
    _ = _ := by rw [Finset.mul_sum]

noncomputable def Concrete.freshSuccessfulView?
    (initialCache : QueryCache HashSpec) (secretKey : SecretKey) (message : Message)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) :
    Option FewTimeView := by
  classical
  exact if FreshSuccessfulSignerView initialCache secretKey message (fun _ => True) result then
      result.1.2
    else none

theorem Concrete.freshSuccessfulView?_eq_some_iff
    (initialCache : QueryCache HashSpec) (secretKey : SecretKey) (message : Message)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (view : FewTimeView) :
    freshSuccessfulView? initialCache secretKey message result = some view ↔
      FreshSuccessfulSignerView initialCache secretKey message
        (fun value => value = view) result := by
  classical
  constructor
  · intro hview
    by_cases hfresh : FreshSuccessfulSignerView initialCache secretKey message
        (fun _ => True) result
    · rw [freshSuccessfulView?, if_pos hfresh] at hview
      obtain ⟨signature, selectedView, hresult, hmiss, _⟩ := hfresh
      have hselected : selectedView = view := by
        apply Option.some.inj
        simpa [hresult] using hview
      subst selectedView
      exact ⟨signature, view, hresult, hmiss, rfl⟩
    · simp [freshSuccessfulView?, hfresh] at hview
  · rintro ⟨signature, selectedView, hresult, hmiss, hview⟩
    subst selectedView
    have hfresh : FreshSuccessfulSignerView initialCache secretKey message
        (fun _ => True) result := ⟨signature, view, hresult, hmiss, trivial⟩
    simp [freshSuccessfulView?, hfresh, hresult]

set_option maxRecDepth 100000 in
theorem Concrete.tsum_probOutput_signWithView_fresh_mul_le_expected
    (secretKey : SecretKey) (message : Message)
    (initialCache : QueryCache HashSpec)
    (cost : ((Option Signature × Option FewTimeView) × QueryCache HashSpec) → ℝ≥0∞)
    (risk : FewTimeView → ℝ≥0∞)
    (hoff : ∀ signerResult ∈ support
        ((simulateQ romImpl (signWithView secretKey message)).run initialCache),
      freshSuccessfulView? initialCache secretKey message signerResult = none →
      cost signerResult = 0)
    (hon : ∀ signerResult ∈ support
        ((simulateQ romImpl (signWithView secretKey message)).run initialCache),
      ∀ view, freshSuccessfulView? initialCache secretKey message signerResult = some view →
      cost signerResult ≤ risk view) :
    (∑' signerResult,
      Pr[= signerResult |
        (simulateQ romImpl (signWithView secretKey message)).run initialCache] *
          cost signerResult) ≤
      ∑ view, Pr[fun value : FewTimeView => value = view |
        ($ᵗ FewTimeView : ProbComp FewTimeView)] * risk view := by
  have hbound := tsum_probOutput_mul_le_classifiedRisk
    ((simulateQ romImpl (signWithView secretKey message)).run initialCache)
    (freshSuccessfulView? initialCache secretKey message) risk cost hoff hon
  refine hbound.trans ?_
  apply Finset.sum_le_sum
  intro view _
  apply mul_le_mul' _ le_rfl
  simpa only [freshSuccessfulView?_eq_some_iff] using
    probEvent_signWithView_freshSuccessful_le_uniform secretKey message initialCache
      (fun value => value = view)

theorem Concrete.tsum_probOutput_signWithView_fixedPrehit_mul_le_of_enncard_le
    (secretKey : SecretKey) (message : Message)
    (initialCache : QueryCache HashSpec) (target : HashInput) (P : FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 126) (hcache : QueryCache.enncard initialCache ≤ q)
    (cost : ((Option Signature × Option FewTimeView) × QueryCache HashSpec) → ℝ≥0∞)
    (epsilon : ℝ≥0∞)
    (hoff : ∀ signerResult ∈ support
        ((simulateQ romImpl (signWithView secretKey message)).run initialCache),
      ¬ PrehitSuccessfulSignerView (onlyInputCache initialCache target)
        secretKey message P signerResult → cost signerResult = 0)
    (hon : ∀ signerResult ∈ support
        ((simulateQ romImpl (signWithView secretKey message)).run initialCache),
      PrehitSuccessfulSignerView (onlyInputCache initialCache target)
        secretKey message P signerResult → cost signerResult ≤ epsilon) :
    (∑' signerResult,
      Pr[= signerResult |
        (simulateQ romImpl (signWithView secretKey message)).run initialCache] *
          cost signerResult) ≤
      ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ * epsilon := by
  calc
    (∑' signerResult,
        Pr[= signerResult |
          (simulateQ romImpl (signWithView secretKey message)).run initialCache] *
            cost signerResult) ≤
        Pr[PrehitSuccessfulSignerView (onlyInputCache initialCache target)
            secretKey message P |
          (simulateQ romImpl (signWithView secretKey message)).run initialCache] * epsilon :=
      tsum_probOutput_mul_le_gated _ _ _ _ hoff hon
    _ ≤ ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ * epsilon := by
      apply mul_le_mul' _ le_rfl
      exact probEvent_signWithView_fixedPrehit_le_race_of_enncard_le
        secretKey message initialCache target P q hq hcache

theorem Concrete.tsum_probOutput_randomOracle_fresh_admissible_view_mul_le_expected
    (input : HashInput) (cache : QueryCache HashSpec) (hcache : cache input = none)
    (cost : HashOutput × QueryCache HashSpec → ℝ≥0∞)
    (risk : FewTimeView → ℝ≥0∞)
    (hoff : ∀ source ∈ support ((randomOracle input).run cache),
      signAttemptResultOfOutput source.1 = none → cost source = 0)
    (hon : ∀ source ∈ support ((randomOracle input).run cache),
      signAttemptResultOfOutput source.1 ≠ none →
      cost source ≤ risk (hashOutputFewTimeView source.1)) :
    (∑' source, Pr[= source | (randomOracle input).run cache] * cost source) ≤
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        ∑ view, Pr[fun value : FewTimeView => value = view |
          ($ᵗ FewTimeView : ProbComp FewTimeView)] * risk view := by
  let classify : HashOutput × QueryCache HashSpec → Option FewTimeView :=
    fun source => if signAttemptResultOfOutput source.1 = none then none
      else some (hashOutputFewTimeView source.1)
  refine tsum_probOutput_mul_le_uniformClassifiedRisk
    ((randomOracle input).run cache) classify
    ($ᵗ FewTimeView : ProbComp FewTimeView)
    ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ risk cost ?_ ?_ ?_
  · intro view
    calc
      Pr[fun source => classify source = some view | (randomOracle input).run cache] =
          Pr[fun source : HashOutput × QueryCache HashSpec =>
            signAttemptResultOfOutput source.1 ≠ none ∧
              hashOutputFewTimeView source.1 = view |
            (randomOracle input).run cache] := by
        apply probEvent_congr'
        · intro source _
          simp only [classify]
          by_cases hsuccessful : signAttemptResultOfOutput source.1 ≠ none
          · simp [hsuccessful]
          · simp [not_ne_iff.mp hsuccessful]
        · rfl
      _ = ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
          Pr[fun value : FewTimeView => value = view |
            ($ᵗ FewTimeView : ProbComp FewTimeView)] :=
        probEvent_randomOracle_fresh_admissible_view input cache hcache
          (fun value => value = view)
      _ ≤ _ := le_rfl
  · intro source hsource hnone
    apply hoff source hsource
    by_contra hsuccessful
    simp [classify, hsuccessful] at hnone
  · intro source hsource view hsome
    have hsuccessful : signAttemptResultOfOutput source.1 ≠ none := by
      intro hnone
      simp [classify, hnone] at hsome
    have hview : hashOutputFewTimeView source.1 = view := by
      simpa [classify, hsuccessful] using hsome
    rw [← hview]
    exact hon source hsource hsuccessful

end SphincsSecurity
