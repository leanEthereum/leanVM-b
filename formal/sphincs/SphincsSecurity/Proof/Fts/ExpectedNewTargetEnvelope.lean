import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.DigestCompletionNewTarget
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_signWithView_newTargetEnvelopeCharge_le_mass_mul (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩]) uniform reuse arrival queries signings groups remaining) ≤
        freshDigestSelectionProbability key message before *
          ((Fintype.card Index : ENNReal)⁻¹ *
            targetIndexEnvelope uniform reuse arrival queries signings (targetIndexMoments key before log) groups.card remaining.card) := by
  rw [signWithView_run_eq_digestCompletion]
  exact expected_digestCompletion_newTargetEnvelopeCharge_le_mass_mul key message before
    (originalDigestCompletion key) id (fun loop _ result hr => originalDigestCompletion_preservesMessages key loop result hr)
    log hsigned uniform reuse arrival queries signings groups remaining hvalid

end SphincsSecurity.Concrete
