import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePlanExecution

/-!
# Root-aware comparison probe

The delayed comparison schedule executes the root-aware candidate selected from one outer hash
query. When the ordinary structural planner already selected a candidate this is the existing
planned suffix. Otherwise an encoding-domain layer-root guess is installed as one proof-only probe
before the same probe-free action.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 100000 in
theorem probingHashQuery_eq_plan_then_afterPlan
    (parameter : PublicParameter) (input : HashInput) :
    probingHashQuery parameter input = (do
      let plan ← planProbingHashQuery parameter input
      probingHashQueryAfterPlan parameter input plan) := by
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases hposition : decodePosition? parameter input with
      | none =>
          exact probingHashQuery_eq_plan_then_afterPlan_of_probe_some_nonleaf parameter input
            candidate hprobe (by
              rintro ⟨lay, tree, leafIdx, heq⟩
              simp [hposition] at heq)
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              exact probingHashQuery_eq_plan_then_afterPlan_leaf parameter input candidate lay
                tree leafIdx hprobe hposition
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              exact probingHashQuery_eq_plan_then_afterPlan_of_probe_some_nonleaf parameter input
                candidate hprobe (by
                  rintro ⟨lay, tree, leafIdx, heq⟩
                  simp [hposition] at heq)
  | none =>
      cases hposition : decodePosition? parameter input with
      | none =>
          exact probingHashQuery_eq_plan_then_afterPlan_of_probe_none_nonnode parameter input
            hprobe (by
              rintro ⟨lay, tree, level, nodeIdx, heq⟩
              simp [hposition] at heq)
      | some position =>
          cases position with
          | node lay tree level nodeIdx =>
              exact probingHashQuery_eq_plan_then_afterPlan_node parameter input lay tree level
                nodeIdx hprobe hposition
          | chain | leaf | ftsLeaf | ftsNode | ftsRoots =>
              exact probingHashQuery_eq_plan_then_afterPlan_of_probe_none_nonnode parameter input
                hprobe (by
                  rintro ⟨lay, tree, level, nodeIdx, heq⟩
                  simp [hposition] at heq)

end SphincsSecurity.Concrete.OtsProbeSimulation
