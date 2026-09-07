import SphincsSecurity.Proof.PreExceptionQueryCharge

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem expectedPreExceptionCharge_mono
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (left right : QueryCache HashSpec → HashInput → ENNReal)
    (hle : ∀ cache input, left cache input ≤ right cache input)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception left computation cache hit ≤ expectedPreExceptionCharge exception right computation cache hit := by
  calc
    _ ≤ expectedPreExceptionCharge exception left computation cache hit +
        expectedPreExceptionCharge exception (fun cache input => right cache input - left cache input) computation cache hit := le_self_add
    _ = expectedPreExceptionCharge exception (fun cache input => left cache input + (right cache input - left cache input)) computation cache hit :=
      (expectedPreExceptionCharge_add exception _ _ computation cache hit).symm
    _ = _ := by
      congr 1
      funext cache input
      exact add_tsub_cancel_of_le (hle cache input)

end SphincsSecurity
