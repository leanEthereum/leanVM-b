import SphincsSecurity.Proof.RemainingSigningCoverageSplit

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def coverageExecutionRefund (key : SecretKey) (cap budget cost : Nat) (state : CoverLogState) : ENNReal :=
  (cappedRemainingRawIndexEnvelope key cap budget state ∅ Finset.univ *
      (cost : ENNReal) *
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) +
    remainingCoverageExecutionGap key cap budget (cost) 0 state ∅ Finset.univ) *
      ((2 ^ 140 : Nat) : ENNReal)⁻¹

theorem remainingCoverage_add_executionRefund (key : SecretKey) (cap budget cost : Nat) (state : CoverLogState)
    (hcost : cost ≤ budget) :
    remainingCoveragePotential key cap (budget - cost) state ∅ Finset.univ *
        ((2 ^ 140 : Nat) : ENNReal)⁻¹ + coverageExecutionRefund key cap budget cost state =
      remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ := by
  have hvalid : TargetShapeValid ∅ (Finset.univ : Finset FtsTree) := by constructor <;> simp
  have h := remainingCoveragePotential_add_executionGap key cap budget (cost) 0
    (cost) hcost (Nat.zero_add _) state ∅ Finset.univ hvalid
  simpa only [coverageExecutionRefund, remainingCoveragePotential, Nat.add_zero, add_mul] using
    congrArg (fun value => value * ((2 ^ 140 : Nat) : ENNReal)⁻¹) h

noncomputable def signingCoverageExecutionRefund (key : SecretKey) (cap budget : Nat) (message : Message) (state : CoverLogState) : ENNReal :=
  coverageExecutionRefund key cap budget (signingExecutionHashCost (.inr message)) state

theorem remainingCoverage_add_signingExecutionRefund (key : SecretKey) (cap budget : Nat) (message : Message) (state : CoverLogState)
    (hcost : signingExecutionHashCost (.inr message) ≤ budget) :
    remainingCoveragePotential key cap (budget - signingExecutionHashCost (.inr message)) state ∅ Finset.univ *
        ((2 ^ 140 : Nat) : ENNReal)⁻¹ + signingCoverageExecutionRefund key cap budget message state =
      remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ :=
  remainingCoverage_add_executionRefund key cap budget (signingExecutionHashCost (.inr message)) state hcost

theorem expected_surviving_sign_remainingCoverage_le_before_add_new
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (message : Message) (state : CoverLogState) (hit : Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (hcache : QueryCache.enncard state.1 ≤ cap) :
    expectedSurvivingSigningPotential exception key message state hit (fun current =>
      remainingCoveragePotential key cap budget current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) ≤
      remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ +
        signingNewTargetCoverage exception key message state.1 hit state.2 (Fintype.card Index : ENNReal)⁻¹
          (digestReuseWeight cap) (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
          budget (signatureLimit - (state.2.length + 1)) := by
  let factor : ENNReal := (budget : ENNReal) *
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) * ((2 ^ 140 : Nat) : ENNReal)⁻¹
  have hvalid : TargetShapeValid ∅ (Finset.univ : Finset FtsTree) := by constructor <;> simp
  have hraw := (expected_surviving_signWithView_le_logTraced exception key message state hit
    (fun current => cappedRemainingRawIndexEnvelope key cap budget current ∅ Finset.univ)).trans
      (expected_logTraced_sign_cappedRemainingRawIndex_fixed_le key cap budget hcap state hsigned hcache message ∅ Finset.univ hvalid)
  have heq : (fun current => remainingCoveragePotential key cap budget current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) =
      fun current => cappedRemainingCachedTargetEnvelope key cap budget current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ +
        cappedRemainingRawIndexEnvelope key cap budget current ∅ Finset.univ * factor := by
    funext current
    dsimp only [remainingCoveragePotential, factor]
    ring
  rw [heq, expectedSurvivingSigningPotential_add,
    expectedSurvivingSigningPotential_mul exception key message state hit
      (fun current => cappedRemainingRawIndexEnvelope key cap budget current ∅ Finset.univ) factor]
  apply le_trans (add_le_add
    (expected_surviving_sign_cachedRemaining_le_old_add_new_all exception key cap budget hcap message state hit hsigned hcache)
    (mul_le_mul' hraw (le_refl factor)))
  apply le_of_eq
  dsimp only [remainingCoveragePotential, factor]
  ring

noncomputable def signingRemainingCoverageResidual (key : SecretKey) (cap budget : Nat) (message : Message) (state : CoverLogState) : ENNReal :=
  signingNewTargetCoverageResidual key message state.1 state.2 (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
    (budget - signingExecutionHashCost (.inr message)) (signatureLimit - (state.2.length + 1))

theorem expected_surviving_sign_coverage_pairs_refund_le_reserved_add_residual
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (cap budget : Nat) (hcapMax : cap ≤ 2 ^ 127) (message : Message) (state : CoverLogState) (hit : Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (hcache : QueryCache.enncard state.1 ≤ cap)
    (hcost : signingExecutionHashCost (.inr message) ≤ budget)
    (hcap : ∀ result ∈ support ((simulateQ romImpl (sign key message)).run state.1), QueryCache.enncard result.2 ≤ cap) :
    expectedSurvivingSigningPotential exception key message state hit (fun current =>
      remainingCoveragePotential key cap (budget - signingExecutionHashCost (.inr message)) current ∅ Finset.univ *
        ((2 ^ 140 : Nat) : ENNReal)⁻¹) +
      expectedPreExceptionCharge exception (encodingPairIncrementCharge key) (sign key message) state.1 hit *
        (Fintype.card Digest : ENNReal)⁻¹ + signingCoverageExecutionRefund key cap budget message state ≤
      remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ +
        expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter) (sign key message) state.1 hit *
          (Fintype.card Digest : ENNReal)⁻¹ + signingRemainingCoverageResidual key cap budget message state := by
  have hcoverage := expected_surviving_sign_remainingCoverage_le_before_add_new exception key cap
    (budget - signingExecutionHashCost (.inr message)) hcapMax message state hit hsigned hcache
  have hpayment := expected_encodingPairs_add_newTargetCoverage_le_reserved_add_residual exception key message cap hcapMax
    state.1 (Finite.of_enncard_le hcache) hit hcap state.2 (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
    (budget - signingExecutionHashCost (.inr message)) (signatureLimit - (state.2.length + 1))
  have h := add_le_add (add_le_add hcoverage (le_refl
    (expectedPreExceptionCharge exception (encodingPairIncrementCharge key) (sign key message) state.1 hit *
      (Fintype.card Digest : ENNReal)⁻¹))) (le_refl (signingCoverageExecutionRefund key cap budget message state))
  apply h.trans
  have hcombined := add_le_add (le_of_eq (remainingCoverage_add_signingExecutionRefund key cap budget message state hcost)) hpayment
  unfold signingRemainingCoverageResidual
  convert hcombined using 1 <;> ring

theorem expected_surviving_sign_remainingCoverage_eq_zero_of_inactive
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (cap budget : Nat) (message : Message) (state : CoverLogState) (hit : Bool)
    (hinactive : ¬ ValidSigningStep state.2 (.inr message)) :
    expectedSurvivingSigningPotential exception key message state hit (fun current =>
      remainingCoveragePotential key cap budget current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) = 0 := by
  have hinvalid (signature : Option Signature) : ¬ SigningTranscript.Valid (state.2 ++ [⟨message, signature⟩]) := by
    have hlength : ¬ state.2.length < signatureLimit := hinactive
    simp only [SigningTranscript.Valid, List.length_append, List.length_singleton]
    omega
  simp only [expectedSurvivingSigningPotential, remainingCoveragePotential, cappedRemainingCachedTargetEnvelope,
    cappedRemainingRawIndexEnvelope, if_neg (hinvalid _), zero_mul, zero_add, ite_self, mul_zero, tsum_zero]

theorem expected_surviving_sign_coverage_pairs_refund_le_reserved_of_inactive
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (cap budget : Nat) (hcapMax : cap ≤ 2 ^ 127) (message : Message) (state : CoverLogState) (hit : Bool)
    (hinactive : ¬ ValidSigningStep state.2 (.inr message)) (hcache : QueryCache.enncard state.1 ≤ cap)
    (hcost : signingExecutionHashCost (.inr message) ≤ budget)
    (hcap : ∀ result ∈ support ((simulateQ romImpl (sign key message)).run state.1), QueryCache.enncard result.2 ≤ cap) :
    expectedSurvivingSigningPotential exception key message state hit (fun current =>
      remainingCoveragePotential key cap (budget - signingExecutionHashCost (.inr message)) current ∅ Finset.univ *
        ((2 ^ 140 : Nat) : ENNReal)⁻¹) +
      expectedPreExceptionCharge exception (encodingPairIncrementCharge key) (sign key message) state.1 hit *
        (Fintype.card Digest : ENNReal)⁻¹ + signingCoverageExecutionRefund key cap budget message state ≤
      remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ +
        expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter) (sign key message) state.1 hit *
          (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [expected_surviving_sign_remainingCoverage_eq_zero_of_inactive exception key cap _ message state hit hinactive, zero_add]
  have hrefund : signingCoverageExecutionRefund key cap budget message state ≤
      remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ :=
    le_add_self.trans_eq (remainingCoverage_add_signingExecutionRefund key cap budget message state hcost)
  have hpairs := mul_le_mul' (expectedPreException_signingEncodingPairs_le_reserved exception key message cap hcapMax
    state.1 (Finite.of_enncard_le hcache) hit hcap) (le_refl (Fintype.card Digest : ENNReal)⁻¹)
  exact (add_le_add hpairs hrefund).trans_eq (add_comm _ _)

end SphincsSecurity.Concrete
