import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.EncodingPrehitViewedTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem encodingPrehitViewedAdversaryImpl_cache_projection
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool) :
    (fun result => (result.1, result.2.1.cache)) <$>
      (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state =
      (simulateQ (unloggedMappedAdversaryImpl secretKey) computation).run state.1.cache := by
  calc
    _ = (fun result : α × ViewedFullTraceState => (result.1, result.2.cache)) <$>
        (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey) computation).run state.1 := by
      rw [← encodingPrehitViewedAdversaryImpl_projection accountingKey secretKey computation state]
      simp only [Functor.map_map]
      rfl
    _ = Prod.map id Prod.fst <$>
        (simulateQ (fullTracedMappedAdversaryImpl secretKey) computation).run state.1.base := by
      rw [← viewedFullTracedMappedAdversaryImpl_projection secretKey computation state.1]
      simp only [Functor.map_map]
      rfl
    _ = _ := _root_.OracleComp.extendState_run_proj_eq (unloggedMappedAdversaryImpl secretKey)
      fullAdversaryTraceUpdate computation state.1.cache state.1.trace

end SphincsSecurity.Concrete.OtsProbeSimulation
