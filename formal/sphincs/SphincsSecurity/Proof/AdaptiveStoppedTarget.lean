import SphincsSecurity.Proof.StoppedTargetCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

theorem expected_runWithFailure_target_le_stopped_arrival
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hsigned : SigningDigestsCached parameter state.1 root state.2)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run state),
      QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | runWithFailure exception parameter root otsTable ftsTable
        (withSigningLog computation state.2) frame state.1 hit failed] *
      survivingLogPotential (fun current => cappedCachedTargetEnvelope (secretKey parameter root otsTable ftsTable) q current groups remaining)
        (result.1.2.1.2, result.1.2.1.1.2) result.1.2.2 result.2) ≤
      survivingLogPotential (fun current => cappedCachedTargetEnvelope (secretKey parameter root otsTable ftsTable) q current groups remaining) state hit failed +
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
          expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (targetArrivalHashCost parameter)
            groups remaining computation frame state hit failed := by
  let key := secretKey parameter root otsTable ftsTable
  let potential := fun current => cappedCachedTargetEnvelope key q current groups remaining
  let arrival : ENNReal := ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹
  induction computation using OracleComp.inductionOn generalizing frame state hit failed with
  | pure value =>
      simp only [withSigningLog_pure, runWithFailure_pure, tsum_probOutput_pure_mul, expectedStoppedIndexCharge,
        expectedStoppedLogCharge_pure, mul_zero, add_zero, Prod.mk.eta, le_refl]
  | query_bind input next ih =>
      have htail := simulateQ_logTraced_tail_cache_bound key q input next state hbudget
      have hbefore := simulateQ_logTraced_initial_cache_bound key q (OracleSpec.query input >>= next) state hbudget
      have hstep := stepWithFailure_survivingTarget_le exception parameter root otsTable ftsTable q hq input frame state hit failed
        hsigned hbefore (fun result hresult => simulateQ_logTraced_initial_cache_bound key q (next result.1) result.2 (htail result hresult)) groups remaining hvalid
      rw [withSigningLog_query_bind, runWithFailure_query_bind, tsum_probOutput_bind_mul]
      calc
        _ ≤ ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
            (survivingLogPotential potential (stepSigningLogState input state.2 result) result.1.2.2 result.2 +
              arrival * expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (targetArrivalHashCost parameter)
                groups remaining (next result.1.2.1.1) result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed)
          · have hlogged := stepWithFailure_logged_support exception parameter root otsTable ftsTable input frame state.1 state.2 hit failed result hresult
            exact mul_le_mul' le_rfl (ih result.1.2.1.1 result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2
              (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned _ hlogged) (htail _ hlogged))
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
            survivingLogPotential potential (stepSigningLogState input state.2 result) result.1.2.2 result.2) +
            arrival * ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
              expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (targetArrivalHashCost parameter)
                groups remaining (next result.1.2.1.1) result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2 := by
          simp_rw [mul_add, mul_left_comm (Pr[= _ | _])]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
        _ ≤ (survivingLogPotential potential state hit failed +
            arrival * survivingLogPotential (fun current => (targetArrivalHashCost parameter current.1 input : ENNReal) *
              cappedRawIndexCacheEnvelope key q current groups remaining) state hit failed) +
            arrival * ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
              expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (targetArrivalHashCost parameter)
                groups remaining (next result.1.2.1.1) result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2 := add_le_add hstep le_rfl
        _ = _ := by
          simp only [expectedStoppedIndexCharge]
          rw [expectedStoppedLogCharge_query_bind]
          dsimp only [potential, key, arrival]
          ring

theorem expected_runWithFailure_target_add_unused_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hsigned : SigningDigestsCached parameter state.1 root state.2)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run state),
      QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | runWithFailure exception parameter root otsTable ftsTable
        (withSigningLog computation state.2) frame state.1 hit failed] *
      survivingLogPotential (fun current => cappedCachedTargetEnvelope (secretKey parameter root otsTable ftsTable) q current groups remaining)
        (result.1.2.1.2, result.1.2.1.1.2) result.1.2.2 result.2) +
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
        expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (unusedTargetHashCost parameter)
          groups remaining computation frame state hit failed ≤
      survivingLogPotential (fun current => cappedCachedTargetEnvelope (secretKey parameter root otsTable ftsTable) q current groups remaining) state hit failed +
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
          expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (fun _ => signingMacroHashCost)
            groups remaining computation frame state hit failed := by
  apply (add_le_add (expected_runWithFailure_target_le_stopped_arrival exception parameter root otsTable ftsTable q hq
    computation frame state hit failed hsigned hbudget groups remaining hvalid) le_rfl).trans_eq
  rw [add_assoc, ← mul_add, expectedStoppedIndexCharge_arrival_add_unused]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
