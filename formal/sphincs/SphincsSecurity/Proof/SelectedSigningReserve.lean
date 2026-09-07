import SphincsSecurity.Proof.FtsSigningReserve
import SphincsSecurity.Proof.FewTimeSignerView

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem preExceptionSurvivalCost_signAfterDigest
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    PreExceptionSurvivalCost exception (nonMessageNonEncodingHashCharge key.parameter)
      (liftM (signAfterDigest key randomness index leaves)) 28504 := by
  rw [signAfterDigest, liftM_bind]
  apply preExceptionSurvivalCost_bind _ _ _ _ 28504 0
  · intro cache hit
    exact expected_reserved_ftsOpen_ge_survival exception key.parameter index leaves (key.ftsSecret index) cache hit
  · intro path
    exact preExceptionSurvivalCost_zero _ _ _

theorem expectedPreExceptionCharge_signWithView_eq_sign
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal) (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception charge (signWithView key message) cache hit =
      expectedPreExceptionCharge exception charge (sign key message) cache hit := by
  rw [← signWithView_fst, map_eq_bind_pure_comp, expectedPreExceptionCharge_bind]
  simp only [Function.comp_apply, expectedPreExceptionCharge_pure, mul_zero, tsum_zero, add_zero]

theorem expected_signingReserve_ge_selected_survival
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hit : Bool) :
    (28504 : ENNReal) * Pr[fun result => result.1.1.2.isSome ∧ result.2 = false |
      runExceptionMonitor exception (signWithView key message) cache hit] ≤
      expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter) (sign key message) cache hit := by
  rw [← expectedPreExceptionCharge_signWithView_eq_sign, signWithView, runExceptionMonitor_bind, expectedPreExceptionCharge_bind]
  apply le_trans ?_ (le_add_self : _ ≤ expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter)
    (signDigestLoop digestAttemptLimit key message) cache hit + _)
  rw [probEvent_bind_eq_tsum, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [mul_left_comm]
  apply mul_le_mul' le_rfl
  cases selected : result.1.1 with
  | none => simp [runExceptionMonitor]
  | some data =>
      obtain ⟨randomness, index, leaves⟩ := data
      have hcost := preExceptionSurvivalCost_bind exception (nonMessageNonEncodingHashCharge key.parameter)
        (liftM (signAfterDigest key randomness index leaves) : OracleComp OracleWorld _)
        (fun signature => pure (signature, some (selectedFewTimeView index leaves))) 28504 0
        (preExceptionSurvivalCost_signAfterDigest exception key randomness index leaves)
        (fun _ => preExceptionSurvivalCost_zero _ _ _)
      apply le_trans ?_ (hcost result.1.2 result.2)
      apply mul_le_mul' le_rfl
      apply probEvent_mono
      intro final _ hfinal
      exact hfinal.2

end SphincsSecurity.Concrete.FtsProbeSimulation
