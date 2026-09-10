import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeCanonicalQuerySelection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open _root_.OracleComp.DeferredSampling

attribute [local instance] Classical.propDecidable

noncomputable def canonicalTraceCharge
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ℝ≥0∞)
    (history : List CanonicalQuerySelection) : ℝ≥0∞ :=
  (history.map fun selection => CanonicalQuerySelection.charge charge (some selection)).sum

theorem canonicalTraceCharge_eq_tsum_selection
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ℝ≥0∞)
    (history : List CanonicalQuerySelection) :
    canonicalTraceCharge charge history = ∑' ordinal : Nat, CanonicalQuerySelection.charge charge (history[ordinal]?) := by
  induction history with
  | nil => simp [canonicalTraceCharge, CanonicalQuerySelection.charge]
  | cons head tail ih =>
      rw [tsum_eq_zero_add' ENNReal.summable]
      simpa only [canonicalTraceCharge, List.map_cons, List.sum_cons, List.getElem?_cons_zero,
        List.getElem?_cons_succ] using congrArg (CanonicalQuerySelection.charge charge (some head) + ·) ih

end SphincsSecurity.Concrete.OtsProbeSimulation
