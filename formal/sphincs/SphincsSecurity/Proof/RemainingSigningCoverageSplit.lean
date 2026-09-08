import SphincsSecurity.Proof.RemainingSigningCoverage
import SphincsSecurity.Proof.SigningCoverageSurvivalPayment

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedSurvivingSigningPotential
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (state : CoverLogState) (hit : Bool) (weight : CoverLogState → ENNReal) : ENNReal :=
  ∑' result, Pr[= result | runExceptionMonitor exception (signWithView key message) state.1 hit] *
    (if result.2 = false then weight (result.1.2, state.2 ++ [⟨message, result.1.1.1⟩]) else 0)

theorem expectedSurvivingSigningPotential_add
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (state : CoverLogState) (hit : Bool) (first second : CoverLogState → ENNReal) :
    expectedSurvivingSigningPotential exception key message state hit (fun current => first current + second current) =
      expectedSurvivingSigningPotential exception key message state hit first +
        expectedSurvivingSigningPotential exception key message state hit second := by
  unfold expectedSurvivingSigningPotential
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  split_ifs <;> simp only [mul_add, mul_zero, zero_add]

theorem expectedSurvivingSigningPotential_mul
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (state : CoverLogState) (hit : Bool) (weight : CoverLogState → ENNReal) (factor : ENNReal) :
    expectedSurvivingSigningPotential exception key message state hit (fun current => weight current * factor) =
      expectedSurvivingSigningPotential exception key message state hit weight * factor := by
  unfold expectedSurvivingSigningPotential
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro result
  split_ifs <;> simp only [mul_assoc, mul_zero, zero_mul]

theorem expectedSurvivingSigningPotential_eq_sign
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (state : CoverLogState) (hit : Bool) (weight : CoverLogState → ENNReal) :
    expectedSurvivingSigningPotential exception key message state hit weight =
      ∑' result, Pr[= result | runExceptionMonitor exception (sign key message) state.1 hit] *
        (if result.2 = false then weight (result.1.2, state.2 ++ [⟨message, result.1.1⟩]) else 0) := by
  rw [← signWithView_fst key message, runExceptionMonitor_map, tsum_probOutput_map_mul]
  rfl

theorem expected_surviving_signWithView_le_logTraced
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (state : CoverLogState) (hit : Bool) (weight : CoverLogState → ENNReal) :
    (∑' result, Pr[= result | runExceptionMonitor exception (signWithView key message) state.1 hit] *
      (if result.2 = false then weight (result.1.2, state.2 ++ [⟨message, result.1.1.1⟩]) else 0)) ≤
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] * weight result.2 := by
  calc
    _ ≤ ∑' result, Pr[= result | runExceptionMonitor exception (signWithView key message) state.1 hit] *
        weight (result.1.2, state.2 ++ [⟨message, result.1.1.1⟩]) := by
      apply ENNReal.tsum_le_tsum
      intro result
      apply mul_le_mul' le_rfl
      split_ifs
      · exact le_rfl
      · exact zero_le
    _ = ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run state.1] *
        weight (result.2, state.2 ++ [⟨message, result.1.1⟩]) := by
      rw [← runExceptionMonitor_project exception (signWithView key message) state.1 hit, tsum_probOutput_map_mul]
    _ = _ := by
      rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
      have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
          (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
        (simulateQ_signWithView_fst_run key message state.1).symm
      rw [hrun, tsum_probOutput_map_mul]
      rfl

theorem expected_logTraced_sign_oldRemainingCachedTarget_le
    (key : SecretKey) (cap budget signatures : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      cacheMessageWeight key.parameter (fun input target =>
        remainingTargetEnvelope key cap budget (payloadOf input) target signatures result.2 groups remaining) state.1) ≤
      remainingCachedTargetEnvelope key cap budget (signatures + 1) state groups remaining := by
  rw [expected_cacheMessageWeight]
  apply cacheMessageWeight_mono
  intro input target
  exact expected_logTraced_sign_remainingTarget_le key cap budget (payloadOf input) target signatures hcap state hsigned hcache
    message groups remaining hvalid

theorem expected_surviving_sign_cachedRemaining_le_old_add_new
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (message : Message)
    (state : CoverLogState) (hit : Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (hcache : QueryCache.enncard state.1 ≤ cap)
    (hactive : ValidSigningStep state.2 (.inr message)) :
    (∑' result, Pr[= result | runExceptionMonitor exception (signWithView key message) state.1 hit] *
      (if result.2 = false then
        cappedRemainingCachedTargetEnvelope key cap budget (result.1.2, state.2 ++ [⟨message, result.1.1.1⟩]) ∅ Finset.univ *
          ((2 ^ 140 : Nat) : ENNReal)⁻¹ else 0)) ≤
      cappedRemainingCachedTargetEnvelope key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ +
        FtsProbeSimulation.signingNewTargetCoverage exception key message state.1 hit state.2 (Fintype.card Index : ENNReal)⁻¹
          (digestReuseWeight cap) (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
          budget (signatureLimit - (state.2.length + 1)) := by
  let signatures := signatureLimit - (state.2.length + 1)
  let old := fun after : CoverLogState => cacheMessageWeight key.parameter (fun input target =>
    remainingTargetEnvelope key cap budget (payloadOf input) target signatures after ∅ Finset.univ) state.1
  have hvalid : TargetShapeValid ∅ (Finset.univ : Finset FtsTree) := by constructor <;> simp
  have hlength : state.2.length < signatureLimit := hactive
  have hremaining : signatures + 1 = signatureLimit - state.2.length := by dsimp [signatures]; omega
  have hold := (expected_surviving_signWithView_le_logTraced exception key message state hit old).trans
    (expected_logTraced_sign_oldRemainingCachedTarget_le key cap budget signatures hcap state hsigned hcache message ∅ Finset.univ hvalid)
  rw [hremaining] at hold
  rw [cappedRemainingCachedTargetEnvelope, if_pos hactive.valid_before]
  apply le_trans ?_ (add_le_add (mul_le_mul' hold (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹))) le_rfl)
  rw [FtsProbeSimulation.signingNewTargetCoverage, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (runExceptionMonitor exception (signWithView key message) state.1 hit)
  · have hraw := runExceptionMonitor_support_project exception (signWithView key message) state.1 hit hr
    have hle := simulateQ_romImpl_cache_le (signWithView key message) state.1 result.1 hraw
    have hafter : SigningTranscript.Valid (state.2 ++ [⟨message, result.1.1.1⟩]) := by
      simpa only [SigningTranscript.Valid, List.length_append, List.length_singleton] using Nat.succ_le_of_lt hlength
    by_cases hh : result.2 = false
    · simp only [hh, if_true, cappedRemainingCachedTargetEnvelope, if_pos hafter, List.length_append, List.length_singleton]
      rw [remainingCachedTargetEnvelope_split key cap budget signatures state.1 _ hle, add_mul, mul_add, mul_assoc]
    · simp only [hh, Bool.true_eq_false, if_false, mul_zero, zero_mul, zero_add, le_refl]
  · rw [probOutput_eq_zero_of_not_mem_support hr]
    simp only [zero_mul, zero_add, le_refl]

theorem expected_surviving_sign_cachedRemaining_le_old_add_new_all
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (message : Message)
    (state : CoverLogState) (hit : Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (hcache : QueryCache.enncard state.1 ≤ cap) :
    expectedSurvivingSigningPotential exception key message state hit (fun current =>
      cappedRemainingCachedTargetEnvelope key cap budget current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) ≤
      cappedRemainingCachedTargetEnvelope key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ +
        FtsProbeSimulation.signingNewTargetCoverage exception key message state.1 hit state.2 (Fintype.card Index : ENNReal)⁻¹
          (digestReuseWeight cap) (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
          budget (signatureLimit - (state.2.length + 1)) := by
  by_cases hactive : ValidSigningStep state.2 (.inr message)
  · exact expected_surviving_sign_cachedRemaining_le_old_add_new exception key cap budget hcap message state hit hsigned hcache hactive
  · have hlength : ¬ state.2.length < signatureLimit := hactive
    have hinvalid (signature : Option Signature) : ¬ SigningTranscript.Valid (state.2 ++ [⟨message, signature⟩]) := by
      simp only [SigningTranscript.Valid, List.length_append, List.length_singleton]
      omega
    simp only [expectedSurvivingSigningPotential, cappedRemainingCachedTargetEnvelope, if_neg (hinvalid _), zero_mul,
      ite_self, mul_zero, tsum_zero, zero_le]

end SphincsSecurity.Concrete
