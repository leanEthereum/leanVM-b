import SphincsSecurity.Proof.SigningStoppedStructuralBudget
import SphincsSecurity.Proof.PreExceptionOuterCharge
import SphincsSecurity.Proof.JointProbeNonSecretStructuralBudget

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

theorem expectedPreStructuralCharge_expanded_le_preHashQueries_add_preOuterNonSecret
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (signingStructuralCharge secretKey)
        (simulateQ (expandedAdversaryImpl secretKey) computation) cache hit ≤
      expectedPreExceptionCharge exception (fun _ _ => 1) (simulateQ (expandedAdversaryImpl secretKey) computation) cache hit +
        expectedPreExceptionOuterCharge exception secretKey (fun _ input =>
          if FtsProbeSimulation.NonSecretHashInput secretKey.parameter input then 1 else 0) computation cache hit := by
  apply expectedPreExceptionCharge_expanded_le_add_outer
  · exact parentStoppedEncoding_add_ftsParent_le_one_add_nonSecret secretKey
  · exact expectedPreExceptionCharge_sign_le_preHashQueries exception secretKey

end SphincsSecurity.Concrete
