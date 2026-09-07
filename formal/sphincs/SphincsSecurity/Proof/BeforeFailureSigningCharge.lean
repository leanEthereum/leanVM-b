import SphincsSecurity.Proof.JointProbeMessageHashBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def beforeFailureSigningStepCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal) (key : SecretKey)
    (cache : QueryCache HashSpec) (hit failed : Bool) : (OracleWorld + SigningSpec).Domain → ENNReal
  | .inl _ => 0
  | .inr message => if failed then 0 else expectedPreExceptionCharge exception charge (sign key message) cache hit

noncomputable def expectedBeforeFailureSigningCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Option Frame → QueryCache HashSpec → Bool → Bool → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ => 0)
    (fun input _ next frame cache hit failed =>
      beforeFailureSigningStepCharge exception charge (secretKey parameter root otsTable ftsTable) cache hit failed input +
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          next result.1.2.1.1 result.1.1 result.1.2.1.2 result.1.2.2 result.2) computation

@[simp] theorem expectedBeforeFailureSigningCharge_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (value : α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureSigningCharge exception charge parameter root otsTable ftsTable (pure value) frame cache hit failed = 0 := rfl

theorem expectedBeforeFailureSigningCharge_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureSigningCharge exception charge parameter root otsTable ftsTable (OracleSpec.query input >>= next) frame cache hit failed =
      beforeFailureSigningStepCharge exception charge (secretKey parameter root otsTable ftsTable) cache hit failed input +
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          expectedBeforeFailureSigningCharge exception charge parameter root otsTable ftsTable (next result.1.2.1.1)
            result.1.1 result.1.2.1.2 result.1.2.2 result.2 := rfl

theorem expectedBeforeFailureCharge_eq_outer_add_signing
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureCharge exception charge parameter root otsTable ftsTable computation frame cache hit failed =
      expectedBeforeFailureOuterCharge exception charge parameter root otsTable ftsTable computation frame cache hit failed +
        expectedBeforeFailureSigningCharge exception charge parameter root otsTable ftsTable computation frame cache hit failed := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedBeforeFailureCharge_query_bind, expectedBeforeFailureOuterCharge_query_bind, expectedBeforeFailureSigningCharge_query_bind]
      have hhead : (if failed then 0 else expectedPreExceptionCharge exception charge
          (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache hit) =
          (if hit || failed then 0 else outerHashQueryCharge charge input cache) +
            beforeFailureSigningStepCharge exception charge (secretKey parameter root otsTable ftsTable) cache hit failed input := by
        cases input with
        | inl query =>
            simp only [beforeFailureSigningStepCharge, outerHashQueryCharge, add_zero, expandedAdversaryImpl]
            rw [expectedPreExceptionCharge_query]
            cases hit <;> cases failed <;> simp
        | inr message =>
            simp only [beforeFailureSigningStepCharge, outerHashQueryCharge, ite_self, zero_add, expandedAdversaryImpl, scheme]
      rw [hhead]
      simp_rw [ih, mul_add, ENNReal.tsum_add]
      ac_rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
