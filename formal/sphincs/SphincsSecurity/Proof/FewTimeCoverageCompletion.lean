import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeConditionalCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def uncoveredFewTimeTrees {n : Nat} (views : Fin n → Option FewTimeView)
    (target : FewTimeView) : Finset FtsTree :=
  Finset.univ.filter (fun tree => ¬ ∃ slot view,
    views slot = some view ∧ view.1 = target.1 ∧ view.2 tree = target.2 tree)

def insertFewTimeView {n : Nat} (views : Fin n → Option FewTimeView) (source : FewTimeView) :
    Fin (n + 1) → Option FewTimeView := Fin.cons (some source) views

def CompletesFewTimeView {n : Nat} (views : Fin n → Option FewTimeView)
    (target source : FewTimeView) : Prop :=
  ¬ CoveredFewTimeView views target ∧ CoveredFewTimeView (insertFewTimeView views source) target

noncomputable def completionProbability {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) : ENNReal :=
  if CoveredFewTimeView views target then 0 else
    (((2 ^ ftsTreeHeight) ^ (ftsTrees - 1 - (uncoveredFewTimeTrees views target).card) : Nat) : ENNReal) /
      (Fintype.card FewTimeView : ENNReal)

end SphincsSecurity.Concrete
