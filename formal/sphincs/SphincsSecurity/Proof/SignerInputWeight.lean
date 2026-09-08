import SphincsSecurity.Proof.ObservedSignerOccupancy

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def successfulSignerInputWeight (key : SecretKey) (message : Message)
    (weight : HashInput → FewTimeView → ENNReal)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : ENNReal :=
  match result.1.1, result.1.2 with
  | some signature, some view => weight
      (tweakableHashInput key.parameter .message (messageDigestPayload key.root message signature.randomness)) view
  | _, _ => 0

noncomputable def cachedSignerInputWeight (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (weight : HashInput → FewTimeView → ENNReal) (input : HashInput) : ENNReal :=
  match before input with
  | none => 0
  | some output =>
      if (∃ randomness, input = tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) ∧
          Admissible (truncateMessageDigest output) then weight input (hashOutputFewTimeView output) else 0

theorem successfulSignerInputWeight_le_fresh_add_prehit (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    successfulSignerInputWeight key message weight result ≤
      (∑' view, if FreshSuccessfulSignerView before key message (· = view) result then uniformWeight view else 0) +
      (∑' input, if PrehitSuccessfulSignerView (onlyInputCache before input) key message (fun _ => True) result then
        cachedSignerInputWeight key message before weight input else 0) := by
  cases hresponse : result.1.1 with
  | none => simp only [successfulSignerInputWeight, hresponse]; exact bot_le
  | some signature =>
      cases hview : result.1.2 with
      | none => simp only [successfulSignerInputWeight, hresponse, hview]; exact bot_le
      | some view =>
          have hshape : result.1 = (some signature, some view) := Prod.ext hresponse hview
          have hresult' : ((some signature, some view), result.2) ∈ support
              ((simulateQ romImpl (signWithView key message)).run before) := by
            have heq : result = ((some signature, some view), result.2) := Prod.ext hshape rfl
            rwa [heq] at hresult
          let input := tweakableHashInput key.parameter .message (messageDigestPayload key.root message signature.randomness)
          simp only [successfulSignerInputWeight, hresponse, hview]
          cases hbefore : before input with
          | none =>
              have hfresh : FreshSuccessfulSignerView before key message (· = view) result :=
                ⟨signature, view, hshape, hbefore, rfl⟩
              apply (hweight input view).trans
              apply le_trans ?_ le_self_add
              exact (le_of_eq (if_pos hfresh).symm).trans (ENNReal.le_tsum view)
          | some output =>
              obtain ⟨afterOutput, hafter, hadmissible, hselected⟩ := signWithView_successful_cached_output key message before result.2 signature (some view) hresult'
              have hcache := simulateQ_romImpl_cache_le (signWithView key message) before result hresult
              have hout : output = afterOutput := Option.some.inj ((hcache hbefore).symm.trans hafter)
              subst afterOutput
              have hviewOutput : view = hashOutputFewTimeView output := Option.some.inj hselected
              have hsource : cachedSignerInputWeight key message before weight input = weight input view := by
                simp only [cachedSignerInputWeight, hbefore]
                rw [if_pos ⟨⟨signature.randomness, rfl⟩, hadmissible⟩, ← hviewOutput]
              have hprehit : PrehitSuccessfulSignerView (onlyInputCache before input) key message (fun _ => True) result := by
                refine ⟨signature, view, hshape, output, ?_, trivial⟩
                simpa [onlyInputCache, input] using hbefore
              apply le_trans ?_ (le_add_left le_rfl)
              rw [← hsource]
              exact (le_of_eq (if_pos hprehit).symm).trans (ENNReal.le_tsum input)

theorem expected_successfulSignerInputWeight_le_freshMass_add_reuseWeight (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view)
    (reuseWeight : ENNReal)
    (hreuse : ∀ input, Pr[PrehitSuccessfulSignerView (onlyInputCache before input) key message (fun _ => True) |
      (simulateQ romImpl (signWithView key message)).run before] ≤ reuseWeight) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      successfulSignerInputWeight key message weight result) ≤
      freshDigestSelectionProbability key message before *
        (∑' view, Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] * uniformWeight view) +
        (∑' input, cachedSignerInputWeight key message before weight input) * reuseWeight := by
  have hexpect {α : Type} (event : α → ((Option Signature × Option FewTimeView) × QueryCache HashSpec) → Prop)
      (value : α → ENNReal) :
      (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        ∑' index, if event index result then value index else 0) =
        ∑' index, Pr[event index | (simulateQ romImpl (signWithView key message)).run before] * value index := by
    simp only [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro index
    rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro result
    split_ifs <;> simp
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        ((∑' view, if FreshSuccessfulSignerView before key message (· = view) result then uniformWeight view else 0) +
          ∑' input, if PrehitSuccessfulSignerView (onlyInputCache before input) key message (fun _ => True) result then
            cachedSignerInputWeight key message before weight input else 0) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
      · exact mul_le_mul' le_rfl (successfulSignerInputWeight_le_fresh_add_prehit key message before weight uniformWeight hweight result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ = (∑' view, Pr[FreshSuccessfulSignerView before key message (· = view) |
          (simulateQ romImpl (signWithView key message)).run before] * uniformWeight view) +
        ∑' input, Pr[PrehitSuccessfulSignerView (onlyInputCache before input) key message (fun _ => True) |
          (simulateQ romImpl (signWithView key message)).run before] * cachedSignerInputWeight key message before weight input := by
      simp only [mul_add, ENNReal.tsum_add, hexpect]
    _ ≤ (∑' view, (freshDigestSelectionProbability key message before *
          Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)]) * uniformWeight view) +
        ∑' input, reuseWeight * cachedSignerInputWeight key message before weight input := by
      apply add_le_add
      · apply ENNReal.tsum_le_tsum
        intro view
        apply mul_le_mul' _ le_rfl
        simpa only [probEvent_eq_eq_probOutput] using probEvent_signWithView_freshSuccessful_le_mass_mul_uniform key message before (· = view)
      · exact ENNReal.tsum_le_tsum (fun input => mul_le_mul'
          (hreuse input) le_rfl)
    _ = _ := by
      simp only [mul_assoc, ENNReal.tsum_mul_left]
      rw [mul_comm reuseWeight]

theorem expected_successfulSignerInputWeight_le_mass_mul (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      successfulSignerInputWeight key message weight result) ≤
      freshDigestSelectionProbability key message before *
        (∑' view, Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] * uniformWeight view) +
        (∑' input, cachedSignerInputWeight key message before weight input) * digestReuseWeight q :=
  expected_successfulSignerInputWeight_le_freshMass_add_reuseWeight key message before weight uniformWeight hweight
    (digestReuseWeight q) (fun input =>
      probEvent_signWithView_fixedPrehit_le_digestReuseWeight key message before input (fun _ => True) q hq hcache)

theorem expected_successfulSignerInputWeight_le (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      successfulSignerInputWeight key message weight result) ≤
      (∑' view, Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] * uniformWeight view) +
        (∑' input, cachedSignerInputWeight key message before weight input) * digestReuseWeight q :=
  (expected_successfulSignerInputWeight_le_mass_mul key message before weight uniformWeight hweight q hq hcache).trans
    (add_le_add (mul_le_of_le_one_left' (freshDigestSelectionProbability_le_one key message before)) le_rfl)

end SphincsSecurity.Concrete
