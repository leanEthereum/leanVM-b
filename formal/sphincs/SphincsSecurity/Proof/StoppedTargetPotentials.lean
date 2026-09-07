import SphincsSecurity.Proof.StoppedTargetStep

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def survivingLogPotential (potential : CoverLogState → ENNReal)
    (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  if hit || failed then 0 else potential state

theorem stepWithFailure_expect_surviving_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (potential : CoverLogState → ENNReal) (bound : ENNReal)
    (hbound : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable) input).run state] *
      potential result.2) ≤ bound) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
      survivingLogPotential potential (stepSigningLogState input state.2 result) result.1.2.2 result.2) ≤
      if hit || failed then 0 else bound := by
  by_cases hstop : (hit || failed) = true
  · rw [if_pos hstop]
    apply le_of_eq
    apply ENNReal.tsum_eq_zero.mpr
    intro result
    by_cases hresult : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed)
    · rw [survivingLogPotential, if_pos (stepWithFailure_stopped exception parameter root otsTable ftsTable input frame state.1 hit failed hstop result hresult), mul_zero]
    · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
  · rw [if_neg hstop]
    apply le_trans ?_ hbound
    rw [← stepWithFailure_expect_logged exception parameter root otsTable ftsTable input frame state.1 state.2 hit failed (fun _ => potential)]
    apply ENNReal.tsum_le_tsum
    intro result
    apply mul_le_mul' le_rfl
    unfold survivingLogPotential
    split_ifs
    · exact bot_le
    · exact le_rfl

theorem stepWithFailure_survivingRawIndex_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (input : (OracleWorld + SigningSpec).Domain)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hcache : QueryCache.enncard state.1 ≤ q)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable) input).run state),
      QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
      survivingLogPotential (fun current => cappedRawIndexCacheEnvelope (secretKey parameter root otsTable ftsTable) q current groups remaining)
        (stepSigningLogState input state.2 result) result.1.2.2 result.2) ≤
      survivingLogPotential (fun current => cappedRawIndexCacheEnvelope (secretKey parameter root otsTable ftsTable) q current groups remaining) state hit failed :=
  stepWithFailure_expect_surviving_le exception parameter root otsTable ftsTable input frame state hit failed _ _
    (expected_logTraced_cappedRawIndexCacheEnvelope_le (secretKey parameter root otsTable ftsTable) q hq state hsigned hcache input hcap groups remaining hvalid)

theorem stepWithFailure_survivingTarget_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (input : (OracleWorld + SigningSpec).Domain)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hcache : QueryCache.enncard state.1 ≤ q)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable) input).run state),
      QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
      survivingLogPotential (fun current => cappedCachedTargetEnvelope (secretKey parameter root otsTable ftsTable) q current groups remaining)
        (stepSigningLogState input state.2 result) result.1.2.2 result.2) ≤
      survivingLogPotential (fun current => cappedCachedTargetEnvelope (secretKey parameter root otsTable ftsTable) q current groups remaining) state hit failed +
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
          survivingLogPotential (fun current => (targetArrivalHashCost parameter current.1 input : ENNReal) *
            cappedRawIndexCacheEnvelope (secretKey parameter root otsTable ftsTable) q current groups remaining) state hit failed := by
  have h := stepWithFailure_expect_surviving_le exception parameter root otsTable ftsTable input frame state hit failed
    (fun current => cappedCachedTargetEnvelope (secretKey parameter root otsTable ftsTable) q current groups remaining) _
    (expected_logTraced_cappedCachedTargetEnvelope_le_arrival (secretKey parameter root otsTable ftsTable) q hq state hsigned hcache input hcap groups remaining hvalid)
  apply h.trans_eq
  unfold survivingLogPotential
  split_ifs
  · simp
  · rw [mul_left_comm]
    rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
