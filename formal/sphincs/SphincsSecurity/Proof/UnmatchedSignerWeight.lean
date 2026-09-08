import SphincsSecurity.Proof.ExactSignerReuse
import SphincsSecurity.Proof.CacheMessageSignerWeight

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def unmatchedCachedSignerWeight (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (weight : HashInput → FewTimeView → ENNReal) : ENNReal :=
  cacheMessageWeight key.parameter (fun input view =>
    if ∃ randomness, input = tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)
    then 0 else weight input view) cache

theorem cachedSignerWeight_add_unmatched (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (weight : HashInput → FewTimeView → ENNReal) :
    (∑' input, cachedSignerInputWeight key message cache weight input) + unmatchedCachedSignerWeight key message cache weight =
      cacheMessageWeight key.parameter weight cache := by
  unfold unmatchedCachedSignerWeight cacheMessageWeight
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro input
  cases hc : cache input with
  | none => simp only [cachedSignerInputWeight, cacheMessageEntryWeight, hc, zero_add]
  | some output =>
      by_cases hsource : ∃ randomness, input =
          tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)
      · have hmessage : FtsProbeSimulation.MessageHashInput key.parameter input := by
          obtain ⟨randomness, heq⟩ := hsource
          exact ⟨messageDigestPayload key.root message randomness, heq.symm⟩
        simp only [cachedSignerInputWeight, cacheMessageEntryWeight, hc, hsource, hmessage, true_and, if_true, ite_self, add_zero]
      · simp only [cachedSignerInputWeight, cacheMessageEntryWeight, hc, hsource, false_and, if_false, zero_add]

theorem expected_successfulSignerInputWeight_add_unmatched_le
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      successfulSignerInputWeight key message weight result) +
      exactDigestReuseWeight key message before * unmatchedCachedSignerWeight key message before weight ≤
      freshDigestSelectionProbability key message before *
        (∑' view, Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] * uniformWeight view) +
        cacheMessageWeight key.parameter weight before * exactDigestReuseWeight key message before := by
  apply (add_le_add (expected_successfulSignerInputWeight_le_exactReuse key message before weight uniformWeight hweight) le_rfl).trans_eq
  rw [mul_comm (exactDigestReuseWeight key message before), add_assoc, ← add_mul, cachedSignerWeight_add_unmatched]

end SphincsSecurity.Concrete
