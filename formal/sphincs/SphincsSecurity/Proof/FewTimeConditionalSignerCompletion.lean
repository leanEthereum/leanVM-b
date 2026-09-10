import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeCoverageCompletion

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def CompletesSomeFewTimeTarget {α : Type} {n : Nat} (targets : Finset α)
    (views : α → Fin n → Option FewTimeView) (targetView : α → FewTimeView) (source : FewTimeView) : Prop :=
  ∃ target ∈ targets, CompletesFewTimeView (views target) (targetView target) source

end SphincsSecurity.Concrete
