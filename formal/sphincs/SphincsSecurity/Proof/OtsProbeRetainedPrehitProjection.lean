import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.EncodingPrehitViewedProjection
import SphincsSecurity.Proof.OtsProbePrehitQueryTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open SphincsSecurity.Concrete.TightEncoding

set_option backward.isDefEq.respectTransparency false

theorem encodingPrehitViewedAdversaryImpl_cacheFlag_projection
    (accountingKey secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : ViewedFullTraceState × Bool) :
    (fun result => ((result.1, result.2.1.cache), result.2.2)) <$>
      (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state =
      runEncodingPrehitMonitor accountingKey (simulateQ (expandedAdversaryImpl secretKey) computation) state.1.cache state.2 := by
  calc
    _ = (fun result : α × ((QueryCache HashSpec × Bool) × QueryLog SigningSpec) =>
        ((result.1, result.2.1.1), result.2.1.2)) <$>
        (Prod.map id encodingPrehitViewedLogState <$>
          (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state) := by
      rw [Functor.map_map]
      rfl
    _ = runEncodingPrehitMonitor accountingKey (Prod.fst <$>
        (simulateQ (forwardOracles + signingOracle scheme secretKey) computation).run) state.1.cache state.2 := by
      rw [encodingPrehitViewedAdversaryImpl_log_projection, runEncodingPrehitMonitor_map, Functor.map_map]
    _ = _ := by
      rw [forwardOracles_add_signingOracle_eq_withTraceAppend, QueryImpl.fst_map_run_withTraceAppend]

theorem runPrehitQueryTrace_monitor_projection
    (accountingKey secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : ViewedFullTraceState × Bool) :
    (fun result => ((result.1.1, result.1.2.1.cache), result.1.2.2)) <$>
      runPrehitQueryTrace accountingKey secretKey computation state =
      runEncodingPrehitMonitor accountingKey (simulateQ (expandedAdversaryImpl secretKey) computation) state.1.cache state.2 := by
  rw [← encodingPrehitViewedAdversaryImpl_cacheFlag_projection accountingKey secretKey computation state,
    ← runPrehitQueryTrace_projection, Functor.map_map]

def retainedRestVerdict (result : RetainedRestResult) : Bool :=
  decide (SigningTranscript.Valid result.1.2 ∧ ¬SigningTranscript.Contains result.1.2 result.1.1) && result.2

end SphincsSecurity.Concrete.OtsProbeSimulation
