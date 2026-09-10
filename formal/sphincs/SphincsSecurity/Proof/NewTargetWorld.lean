import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.NewTargetEnvelopeCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem newTargetEnvelopeCharge_cacheQuery (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) :
    newTargetEnvelopeCharge key before (before.cacheQuery input output) log uniform reuse arrival queries signings groups remaining =
      if MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
        targetShapeEnvelope uniform reuse arrival queries signings
          (targetShapeMoments key (before.cacheQuery input output) log (payloadOf input) (hashOutputFewTimeView output)) groups remaining else 0 := by
  unfold newTargetEnvelopeCharge
  rw [cacheMessageWeight_cacheQuery key.parameter _ before input output hfresh,
    cacheMessageWeight_fresh_restriction, zero_add]
  simp only [hfresh, if_true]

end SphincsSecurity.Concrete
