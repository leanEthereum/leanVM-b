import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.TargetMomentShapes

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem TargetShapeValid.empty (remaining : Finset FtsTree) : TargetShapeValid ∅ remaining := by
  constructor <;> intro group hgroup <;> exact (Finset.notMem_empty group hgroup).elim

end SphincsSecurity.Concrete
