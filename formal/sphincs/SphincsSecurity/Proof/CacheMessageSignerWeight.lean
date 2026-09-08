import SphincsSecurity.Proof.SignerInputWeight
import SphincsSecurity.Proof.CacheMessageWeight

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem successfulSignerInputWeight_const (key : SecretKey) (message : Message) (weight : FewTimeView → ENNReal)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) :
    successfulSignerInputWeight key message (fun _ source => weight source) result = successfulSignerViewWeight weight result := by
  cases result.1.1 <;> cases result.1.2 <;> rfl

theorem cachedSignerInputWeight_le_cacheMessageEntryWeight (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (weight : HashInput → FewTimeView → ENNReal) (input : HashInput) :
    cachedSignerInputWeight key message before weight input ≤ cacheMessageEntryWeight key.parameter weight before input := by
  unfold cachedSignerInputWeight cacheMessageEntryWeight
  cases before input with
  | none => exact le_rfl
  | some output =>
      simp only
      split_ifs with hsource htarget
      · exact le_rfl
      · obtain ⟨randomness, heq⟩ := hsource.1
        exact (htarget ⟨⟨messageDigestPayload key.root message randomness, heq.symm⟩, hsource.2⟩).elim
      · exact bot_le
      · exact le_rfl

theorem expected_successfulSignerInputWeight_le_allMessage_of_reuseWeight (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view)
    (reuseWeight : ENNReal)
    (hreuse : ∀ input, Pr[PrehitSuccessfulSignerView (onlyInputCache before input) key message (fun _ => True) |
      (simulateQ romImpl (signWithView key message)).run before] ≤ reuseWeight) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      successfulSignerInputWeight key message weight result) ≤
      freshDigestSelectionProbability key message before *
        (∑' view, Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] * uniformWeight view) +
        cacheMessageWeight key.parameter weight before * reuseWeight := by
  apply (expected_successfulSignerInputWeight_le_freshMass_add_reuseWeight key message before weight uniformWeight hweight reuseWeight hreuse).trans
  exact add_le_add le_rfl (mul_le_mul'
    (ENNReal.tsum_le_tsum (cachedSignerInputWeight_le_cacheMessageEntryWeight key message before weight)) le_rfl)

theorem expected_successfulSignerInputWeight_le_allMessage_mass_mul (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      successfulSignerInputWeight key message weight result) ≤
      freshDigestSelectionProbability key message before *
        (∑' view, Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] * uniformWeight view) +
        cacheMessageWeight key.parameter weight before * digestReuseWeight q :=
  expected_successfulSignerInputWeight_le_allMessage_of_reuseWeight key message before weight uniformWeight hweight
    (digestReuseWeight q) (fun input =>
      probEvent_signWithView_fixedPrehit_le_digestReuseWeight key message before input (fun _ => True) q hq hcache)

theorem expected_successfulSignerInputWeight_le_allMessage (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      successfulSignerInputWeight key message weight result) ≤
      (∑' view, Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] * uniformWeight view) +
        cacheMessageWeight key.parameter weight before * digestReuseWeight q :=
  (expected_successfulSignerInputWeight_le_allMessage_mass_mul key message before weight uniformWeight hweight q hq hcache).trans
    (add_le_add (mul_le_of_le_one_left' (freshDigestSelectionProbability_le_one key message before)) le_rfl)

end SphincsSecurity.Concrete
