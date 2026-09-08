import SphincsSecurity.Proof.NewTargetEnvelopeTransform
import SphincsSecurity.Proof.SigningSurvivalAfterEncoding

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_guarded_charge_le_event_add_excess {α : Type} (computation : ProbComp α)
    (charge : α → ENNReal) (selected live : α → Prop) (allowance : ENNReal)
    (hzero : ∀ result ∈ support computation, ¬ selected result → charge result = 0) :
    (∑' result, Pr[= result | computation] * (if live result then charge result else 0)) ≤
      allowance * Pr[fun result => selected result ∧ live result | computation] +
        ∑' result, Pr[= result | computation] * (charge result - allowance) := by
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support computation
  · by_cases hs : selected result
    · by_cases hl : live result
      · simp only [hs, hl, and_self, if_true]
        rw [mul_comm allowance, ← mul_add]
        exact mul_le_mul' le_rfl le_add_tsub
      · simp only [hl, and_false, if_false, mul_zero, zero_le]
    · simp only [hs, false_and, if_false, mul_zero, zero_add, hzero result hr hs,
        zero_tsub, ite_self, mul_zero, le_refl]
  · rw [probOutput_eq_zero_of_not_mem_support hr]
    simp

namespace Concrete.FtsProbeSimulation

noncomputable def signingNewTargetCoverage
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (hit : Bool)
    (log : QueryLog SigningSpec) (uniform reuse arrival : ENNReal) (queries signings : Nat) : ENNReal :=
  ∑' result, Pr[= result | runExceptionMonitor exception (signWithView key message) cache hit] *
    if result.2 = false then
      newTargetEnvelopeCharge key cache result.1.2 (log ++ [⟨message, result.1.1.1⟩])
        uniform reuse arrival queries signings ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹
    else 0

noncomputable def newTargetCoverageExcess
    (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (reference : HashInput)
    (uniform reuse arrival : ENNReal) (queries signings : Nat) : ENNReal :=
  ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
    (targetShapeEnvelope uniform reuse arrival queries signings
      (targetShapeMoments key cache log reference source) ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ -
        28504 * (Fintype.card Digest : ENNReal)⁻¹)

theorem newTargetCoverageExcess_fresh_payload_eq
    (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter cache key.root log) (first second : HashInput)
    (hfirst : cache (tweakableHashInput key.parameter .message first) = none)
    (hsecond : cache (tweakableHashInput key.parameter .message second) = none)
    (uniform reuse arrival : ENNReal) (queries signings : Nat) :
    newTargetCoverageExcess key cache log first uniform reuse arrival queries signings =
      newTargetCoverageExcess key cache log second uniform reuse arrival queries signings := by
  simp only [newTargetCoverageExcess, targetShapeMoments_fresh_payload_eq key cache log first second hfirst hsecond hsigned]

theorem newTargetCoverageExcess_le_indexEnvelope
    (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter cache key.root log)
    (reference : HashInput) (hreference : cache (tweakableHashInput key.parameter .message reference) = none)
    (uniform reuse arrival : ENNReal) (queries signings : Nat) :
    newTargetCoverageExcess key cache log reference uniform reuse arrival queries signings ≤
      (Fintype.card Index : ENNReal)⁻¹ *
        targetIndexEnvelope uniform reuse arrival queries signings (targetIndexMoments key cache log) 0 14 *
          ((2 ^ 140 : Nat) : ENNReal)⁻¹ := by
  have hvalid : TargetShapeValid ∅ (Finset.univ : Finset FtsTree) := by
    constructor <;> intro group hgroup <;> exact (Finset.notMem_empty group hgroup).elim
  calc
    _ ≤ ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        (targetShapeEnvelope uniform reuse arrival queries signings (targetShapeMoments key cache log reference source)
          ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) :=
      ENNReal.tsum_le_tsum fun _ => mul_le_mul' le_rfl tsub_le_self
    _ = _ := by
      simp only [← mul_assoc, ENNReal.tsum_mul_right]
      rw [expected_fresh_targetShapeEnvelope key cache log reference hreference hsigned uniform reuse arrival queries signings
        ∅ Finset.univ hvalid]
      rfl

theorem signingNewTargetCoverage_le_credit_add_excess
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (hit : Bool)
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter cache key.root log)
    (reference : HashInput) (hreference : cache (tweakableHashInput key.parameter .message reference) = none)
    (uniform reuse arrival : ENNReal) (queries signings : Nat) :
    signingNewTargetCoverage exception key message cache hit log uniform reuse arrival queries signings ≤
      signingSurvivalCredit exception key message cache hit * (Fintype.card Digest : ENNReal)⁻¹ +
        newTargetCoverageExcess key cache log reference uniform reuse arrival queries signings := by
  let charge := fun result : (Option Signature × Option FewTimeView) × QueryCache HashSpec =>
    newTargetEnvelopeCharge key cache result.2 (log ++ [⟨message, result.1.1⟩])
      uniform reuse arrival queries signings ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹
  let allowance : ENNReal := 28504 * (Fintype.card Digest : ENNReal)⁻¹
  have hsplit := expected_guarded_charge_le_event_add_excess
    (runExceptionMonitor exception (signWithView key message) cache hit) (fun result => charge result.1)
    (fun result => NewAdmissibleSignerView cache key (fun _ => True) result.1) (fun result => result.2 = false) allowance
    (fun result _ hnone => by
      dsimp only [charge]
      rw [newTargetEnvelopeCharge_of_no_new key cache result.1.2 _ uniform reuse arrival queries signings ∅ Finset.univ
        (fun payload output hfresh hafter hadmissible => hnone ⟨payload, output, hfresh, hafter, hadmissible, trivial⟩), zero_mul])
  simp only [charge] at hsplit
  unfold signingNewTargetCoverage
  apply hsplit.trans
  apply add_le_add
  · have h := mul_le_mul' (newAdmissible_survival_le_signingSurvivalCredit exception key message cache hit (fun _ => True))
      (le_refl ((Fintype.card Digest : ENNReal)⁻¹))
    convert h using 1
    dsimp only [allowance]
    ring
  · have hproject : (∑' result, Pr[= result | runExceptionMonitor exception (signWithView key message) cache hit] *
        (charge result.1 - allowance)) =
        ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run cache] * (charge result - allowance) := by
      rw [← runExceptionMonitor_project exception (signWithView key message) cache hit, tsum_probOutput_map_mul]
    rw [hproject]
    exact expected_signWithView_newTargetEnvelopeCharge_transform_le key message cache log hsigned reference hreference
      uniform reuse arrival queries signings ∅ Finset.univ
      (fun value => value * ((2 ^ 140 : Nat) : ENNReal)⁻¹ - allowance) (by simp)

theorem expected_encodingPairs_add_newTargetCoverage_le_reserved_add_excess
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (cap : Nat) (hcapMax : cap ≤ 2 ^ 127)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool)
    (hcap : ∀ result ∈ support ((simulateQ romImpl (sign key message)).run cache), QueryCache.enncard result.2 ≤ cap)
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter cache key.root log)
    (reference : HashInput) (hreference : cache (tweakableHashInput key.parameter .message reference) = none)
    (uniform reuse arrival : ENNReal) (queries signings : Nat) :
    expectedPreExceptionCharge exception (encodingPairIncrementCharge key) (sign key message) cache hit *
        (Fintype.card Digest : ENNReal)⁻¹ +
      signingNewTargetCoverage exception key message cache hit log uniform reuse arrival queries signings ≤
      expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter) (sign key message) cache hit *
          (Fintype.card Digest : ENNReal)⁻¹ +
        newTargetCoverageExcess key cache log reference uniform reuse arrival queries signings := by
  have h := add_le_add (le_refl (expectedPreExceptionCharge exception (encodingPairIncrementCharge key)
    (sign key message) cache hit * (Fintype.card Digest : ENNReal)⁻¹))
    (signingNewTargetCoverage_le_credit_add_excess exception key message cache hit
    log hsigned reference hreference uniform reuse arrival queries signings)
  apply h.trans
  rw [← add_assoc, ← add_mul]
  exact add_le_add (mul_le_mul' (expected_encodingPairs_add_survival_sign_le_reserved exception key message cap hcapMax
    cache hfinite hit hcap) le_rfl) le_rfl

end Concrete.FtsProbeSimulation
end SphincsSecurity
