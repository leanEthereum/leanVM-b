import SphincsSecurity.Proof.StoppedTargetPotentials
import SphincsSecurity.Proof.StoppedSigningLog
import SphincsSecurity.Proof.TargetArrivalCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedStoppedLogCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : CoverLogState → (OracleWorld + SigningSpec).Domain → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : Option Frame → CoverLogState → Bool → Bool → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ => 0)
    (fun input _ next frame state hit failed =>
      survivingLogPotential (fun current => charge current input) state hit failed +
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
          next result.1.2.1.1 result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2) computation

@[simp] theorem expectedStoppedLogCharge_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : CoverLogState → (OracleWorld + SigningSpec).Domain → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (value : α) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedStoppedLogCharge exception charge parameter root otsTable ftsTable (pure value) frame state hit failed = 0 := rfl

theorem expectedStoppedLogCharge_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : CoverLogState → (OracleWorld + SigningSpec).Domain → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedStoppedLogCharge exception charge parameter root otsTable ftsTable (OracleSpec.query input >>= next) frame state hit failed =
      survivingLogPotential (fun current => charge current input) state hit failed +
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
          expectedStoppedLogCharge exception charge parameter root otsTable ftsTable (next result.1.2.1.1)
            result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2 := rfl

theorem expectedStoppedLogCharge_add
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (first second : CoverLogState → (OracleWorld + SigningSpec).Domain → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedStoppedLogCharge exception (fun current input => first current input + second current input)
        parameter root otsTable ftsTable computation frame state hit failed =
      expectedStoppedLogCharge exception first parameter root otsTable ftsTable computation frame state hit failed +
        expectedStoppedLogCharge exception second parameter root otsTable ftsTable computation frame state hit failed := by
  induction computation using OracleComp.inductionOn generalizing frame state hit failed with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedStoppedLogCharge_query_bind, expectedStoppedLogCharge_query_bind, expectedStoppedLogCharge_query_bind]
      simp_rw [ih, mul_add, ENNReal.tsum_add]
      unfold survivingLogPotential
      split_ifs
      · simp only [zero_add]
      · ac_rfl

noncomputable abbrev expectedStoppedIndexCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (cost : QueryCache HashSpec → (OracleWorld + SigningSpec).Domain → Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  expectedStoppedLogCharge exception (fun current input => (cost current.1 input : ENNReal) *
    cappedRawIndexCacheEnvelope (secretKey parameter root otsTable ftsTable) q current groups remaining)
    parameter root otsTable ftsTable computation frame state hit failed

theorem expectedStoppedIndexCharge_arrival_add_unused
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (targetArrivalHashCost parameter)
        groups remaining computation frame state hit failed +
      expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (unusedTargetHashCost parameter)
        groups remaining computation frame state hit failed =
      expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (fun _ => signingMacroHashCost)
        groups remaining computation frame state hit failed := by
  simp only [expectedStoppedIndexCharge]
  rw [← expectedStoppedLogCharge_add]
  simp_rw [← add_mul, ← Nat.cast_add, targetArrivalHashCost_add_unused]

theorem expectedStoppedIndexCharge_le_unstopped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (cost : QueryCache HashSpec → (OracleWorld + SigningSpec).Domain → Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedStoppedIndexCharge exception parameter root otsTable ftsTable q cost groups remaining computation frame state hit failed ≤
      expectedWeightedIndexCharge (secretKey parameter root otsTable ftsTable) q cost groups remaining computation state := by
  induction computation using OracleComp.inductionOn generalizing frame state hit failed with
  | pure value => exact le_rfl
  | query_bind input next ih =>
      simp only [expectedStoppedIndexCharge] at ih ⊢
      rw [expectedStoppedLogCharge_query_bind, expectedWeightedIndexCharge_query_bind]
      apply add_le_add
      · unfold survivingLogPotential
        split_ifs
        · exact bot_le
        · exact le_rfl
      · rw [← stepWithFailure_expect_logged exception parameter root otsTable ftsTable input frame state.1 state.2 hit failed
          (fun value current => expectedWeightedIndexCharge (secretKey parameter root otsTable ftsTable) q cost groups remaining (next value) current)]
        exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl
          (ih result.1.2.1.1 result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
