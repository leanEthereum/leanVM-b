import SphincsSecurity.Proof.ExactSigningEnvelopeGap
import SphincsSecurity.Proof.SigningCoverageExecutionPayment

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation
attribute [local instance] Classical.propDecidable

noncomputable def remainingRawIndexSigningGap (key : SecretKey) (cap budget : Nat)
    (state : CoverLogState) (message : Message) : TargetShapeVector :=
  fun G R => if ValidSigningStep state.2 (.inr message) then
    rawIndexNonfreshSigningGap key cap budget (signatureLimit - (state.2.length + 1)) state message G R +
      rawIndexReuseSigningGap key cap budget (signatureLimit - (state.2.length + 1)) state message G R +
      signingQueryCommutationGap (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        budget (signatureLimit - (state.2.length + 1)) (observedRawIndexShapeVector key state) G R
    else 0

theorem expected_logTraced_sign_cappedRemainingRawIndex_add_gap_le
    (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      cappedRemainingRawIndexEnvelope key cap budget result.2 groups remaining) +
      remainingRawIndexSigningGap key cap budget state message groups remaining ≤
      cappedRemainingRawIndexEnvelope key cap budget state groups remaining := by
  by_cases hactive : ValidSigningStep state.2 (.inr message)
  · have hremaining : signatureLimit - state.2.length = signatureLimit - (state.2.length + 1) + 1 := by
      have hlength : state.2.length < signatureLimit := hactive
      omega
    rw [remainingRawIndexSigningGap, if_pos hactive, ← add_assoc, ← add_assoc,
      cappedRemainingRawIndexEnvelope, if_pos hactive.valid_before, hremaining]
    apply le_trans (add_le_add (add_le_add (add_le_add ?_ le_rfl) le_rfl) le_rfl)
      (expected_logTraced_sign_rawIndexEnvelope_add_selection_gaps_le key cap budget
        (signatureLimit - (state.2.length + 1)) hcap state hsigned hcache message groups remaining hvalid)
    apply ENNReal.tsum_le_tsum
    intro result
    by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
    · have hlog : result.2.2.length = state.2.length + 1 := by
        rw [logTracedMappedAdversaryImpl_run_map, support_map] at hr
        obtain ⟨base, _, rfl⟩ := hr
        simp only [signingLogFragment, List.length_append, List.length_singleton]
      apply mul_le_mul' le_rfl
      unfold cappedRemainingRawIndexEnvelope
      split_ifs
      · rw [hlog]
        exact le_rfl
      · exact zero_le
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
  · rw [remainingRawIndexSigningGap, if_neg hactive, add_zero]
    exact expected_logTraced_sign_cappedRemainingRawIndex_fixed_le key cap budget hcap state hsigned hcache
      message groups remaining hvalid

noncomputable def signingCoverageEnvelopeGap (key : SecretKey) (cap budget : Nat)
    (message : Message) (state : CoverLogState) : ENNReal :=
  remainingRawIndexSigningGap key cap budget state message ∅ Finset.univ * (budget : ENNReal) *
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) * ((2 ^ 140 : Nat) : ENNReal)⁻¹

theorem expected_surviving_sign_remainingCoverage_add_gap_le_before_add_new
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (message : Message) (state : CoverLogState) (hit : Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (hcache : QueryCache.enncard state.1 ≤ cap) :
    expectedSurvivingSigningPotential exception key message state hit (fun current =>
      remainingCoveragePotential key cap budget current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) +
      signingCoverageEnvelopeGap key cap budget message state ≤
      remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ +
        signingNewTargetCoverage exception key message state.1 hit state.2 (Fintype.card Index : ENNReal)⁻¹
          (digestReuseWeight cap) (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
          budget (signatureLimit - (state.2.length + 1)) := by
  let factor : ENNReal := (budget : ENNReal) *
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) * ((2 ^ 140 : Nat) : ENNReal)⁻¹
  have hvalid : TargetShapeValid ∅ (Finset.univ : Finset FtsTree) := by constructor <;> simp
  have hraw := (add_le_add (expected_surviving_signWithView_le_logTraced exception key message state hit
    (fun current => cappedRemainingRawIndexEnvelope key cap budget current ∅ Finset.univ)) le_rfl).trans
      (expected_logTraced_sign_cappedRemainingRawIndex_add_gap_le key cap budget hcap state hsigned hcache message ∅ Finset.univ hvalid)
  change expectedSurvivingSigningPotential exception key message state hit
      (fun current => cappedRemainingRawIndexEnvelope key cap budget current ∅ Finset.univ) +
    remainingRawIndexSigningGap key cap budget state message ∅ Finset.univ ≤
      cappedRemainingRawIndexEnvelope key cap budget state ∅ Finset.univ at hraw
  have heq : (fun current => remainingCoveragePotential key cap budget current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) =
      fun current => cappedRemainingCachedTargetEnvelope key cap budget current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ +
        cappedRemainingRawIndexEnvelope key cap budget current ∅ Finset.univ * factor := by
    funext current
    dsimp only [remainingCoveragePotential, factor]
    ring
  rw [heq, expectedSurvivingSigningPotential_add,
    expectedSurvivingSigningPotential_mul exception key message state hit
      (fun current => cappedRemainingRawIndexEnvelope key cap budget current ∅ Finset.univ) factor]
  have h := add_le_add
    (expected_surviving_sign_cachedRemaining_le_old_add_new_all exception key cap budget hcap message state hit hsigned hcache)
    (mul_le_mul' hraw (le_refl factor))
  unfold signingCoverageEnvelopeGap remainingCoveragePotential
  dsimp only [factor] at h ⊢
  convert h using 1 <;> first | rfl | ring

theorem expected_surviving_sign_coverage_pairs_refund_gap_le_reserved_add_residual
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (cap budget : Nat) (hcapMax : cap ≤ 2 ^ 127) (message : Message) (state : CoverLogState) (hit : Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (hcache : QueryCache.enncard state.1 ≤ cap)
    (hcost : signingExecutionHashCost (.inr message) ≤ budget)
    (hcap : ∀ result ∈ support ((simulateQ romImpl (sign key message)).run state.1), QueryCache.enncard result.2 ≤ cap) :
    expectedSurvivingSigningPotential exception key message state hit (fun current =>
      remainingCoveragePotential key cap (budget - signingExecutionHashCost (.inr message)) current ∅ Finset.univ *
        ((2 ^ 140 : Nat) : ENNReal)⁻¹) +
      expectedPreExceptionCharge exception (encodingPairIncrementCharge key) (sign key message) state.1 hit *
        (Fintype.card Digest : ENNReal)⁻¹ + signingCoverageExecutionRefund key cap budget message state +
      signingCoverageEnvelopeGap key cap (budget - signingExecutionHashCost (.inr message)) message state ≤
      remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ +
        expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter)
          (sign key message) state.1 hit * (Fintype.card Digest : ENNReal)⁻¹ +
        signingRemainingCoverageResidual key cap budget message state := by
  have hcoverage := expected_surviving_sign_remainingCoverage_add_gap_le_before_add_new exception key cap
    (budget - signingExecutionHashCost (.inr message)) hcapMax message state hit hsigned hcache
  have hpayment := expected_encodingPairs_add_newTargetCoverage_le_reserved_add_residual exception key message cap hcapMax
    state.1 (Finite.of_enncard_le hcache) hit hcap state.2 (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
    (budget - signingExecutionHashCost (.inr message)) (signatureLimit - (state.2.length + 1))
  have h := add_le_add (add_le_add hcoverage (le_refl
    (expectedPreExceptionCharge exception (encodingPairIncrementCharge key) (sign key message) state.1 hit *
      (Fintype.card Digest : ENNReal)⁻¹))) (le_refl (signingCoverageExecutionRefund key cap budget message state))
  have hcombined := add_le_add (le_of_eq (remainingCoverage_add_signingExecutionRefund key cap budget message state hcost)) hpayment
  unfold signingRemainingCoverageResidual
  convert h.trans (by convert hcombined using 1; first | rfl | ring) using 1 <;> first | rfl | ring

end SphincsSecurity.Concrete
