import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.TargetAssignmentCount
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem targetTreeMatchCount_log (log : List α) (view : α → Option FewTimeView) (target : FewTimeView) (tree : FtsTree) :
    targetTreeMatchCount (fun slot => view (log.get slot)) target tree =
      (log.map (fun entry => if ∃ source, view entry = some source ∧ source.1 = target.1 ∧ source.2 tree = target.2 tree then 1 else 0)).sum := by
  rw [targetTreeMatchCount, ← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map log
    (fun entry => if ∃ source, view entry = some source ∧ source.1 = target.1 ∧ source.2 tree = target.2 tree then 1 else 0))

theorem targetTreeMatchCount_log_append (log suffix : List α) (view : α → Option FewTimeView) (target : FewTimeView) (tree : FtsTree) :
    targetTreeMatchCount (fun slot => view ((log ++ suffix).get slot)) target tree =
      targetTreeMatchCount (fun slot => view (log.get slot)) target tree +
        targetTreeMatchCount (fun slot => view (suffix.get slot)) target tree := by
  simp only [targetTreeMatchCount_log, List.map_append, List.sum_append]

end SphincsSecurity.Concrete
