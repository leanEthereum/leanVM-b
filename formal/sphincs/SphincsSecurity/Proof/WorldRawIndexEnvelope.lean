import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FreshTargetShapeAverage
import SphincsSecurity.Proof.InterleavedCoverStep
import SphincsSecurity.Proof.TargetShapeCardinality

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def observedRawIndexShapeVector (key : SecretKey) (state : CoverLogState) : TargetShapeVector :=
  liftTargetIndexVector (targetIndexMoments key state.1 state.2)

end SphincsSecurity.Concrete
