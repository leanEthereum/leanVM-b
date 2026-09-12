import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FreshTargetShapeAverage
import SphincsSecurity.Proof.Fts.InterleavedCoverStep
import SphincsSecurity.Proof.Fts.TargetShapeCardinality
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def observedRawIndexShapeVector (key : SecretKey) (state : CoverLogState) : TargetShapeVector :=
  liftTargetIndexVector (targetIndexMoments key state.1 state.2)

end SphincsSecurity.Concrete
