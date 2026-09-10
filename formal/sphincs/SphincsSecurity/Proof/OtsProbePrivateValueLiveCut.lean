import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeHistoryLiveRisk
import SphincsSecurity.Proof.OtsProbePrivateValueCompletion
import SphincsSecurity.Proof.OtsProbePrivateValueExecution

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem retainCompletableResult_replacePrivateRunResult
    (target : Position) (before after : HashOutput) (result : ResolvedRunResult α)
    (hreplaceable : PrivatePositionReplaceable target before after result.context) :
    retainCompletableResult (some (replacePrivateRunResult target after result)) =
      (retainCompletableResult (some result)).map (replacePrivateRunResult target after) := by
  have hcomplete := deferredCompletable_replacePrivatePosition_iff target before after result.context result.table hreplaceable
  simp only [retainCompletableResult, replacePrivateRunResult]
  rw [hcomplete]
  split_ifs <;> rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
