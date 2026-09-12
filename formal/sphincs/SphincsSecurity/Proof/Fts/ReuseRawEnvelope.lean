import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.TargetShapeEnvelope
import SphincsSecurity.Proof.Fts.WorldRawIndexEnvelope
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def reuseRawEnvelope (key : SecretKey) (reuse : ENNReal) (queries signatures : Nat)
    (state : CoverLogState) : TargetShapeVector :=
  targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries signatures
    (observedRawIndexShapeVector key state)

end SphincsSecurity.Concrete
