import XmssSecurity.Proof.CappedGlobalFirstLaneErasure
import XmssSecurity.Proof.FirstLaneEagerSimulation

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

theorem simulate_globalFirstLaneEagerTrace_chainProjection
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp GlobalFirstLaneWorld α) :
    (fun result => (result.1, result.2.chainActions)) <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          computation).run =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneErase computation)).run := by
  induction computation using OracleComp.inductionOn with
  | pure result =>
      simp [globalFirstLaneErase,
        FirstLaneOracleSimulation.ActionTrace.chainActions]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, WriterT.run_bind', map_bind]
      rw [globalFirstLaneErase, simulateQ_query_bind, simulateQ_bind,
        WriterT.run_bind']
      have hmap : Prod.map id (fun x => x) =
          (id : α × RevealProbeOracleSimulation.ActionTrace
            GlobalChainValueIndex →
            α × RevealProbeOracleSimulation.ActionTrace
              GlobalChainValueIndex) := by
        funext result
        cases result
        rfl
      cases input with
      | uniform n =>
          simp [globalFirstLaneEraseImpl,
            FirstLaneOracleSimulation.eagerTraceImpl,
            FirstLaneOracleSimulation.eagerImpl,
            FirstLaneOracleSimulation.traceFragment,
            FirstLaneOracleSimulation.ActionTrace.chainActions_append,
            RevealProbeOracleSimulation.uniformQuery,
            RevealProbeOracleSimulation.eagerTraceImpl,
            RevealProbeOracleSimulation.eagerImpl,
            RevealProbeOracleSimulation.traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell]
          simp [FirstLaneOracleSimulation.ActionTrace.chainActions]
          apply bind_congr
          intro output
          rw [hmap, id_map]
          simpa [FirstLaneOracleSimulation.eagerTraceImpl,
            RevealProbeOracleSimulation.eagerTraceImpl,
            globalFirstLaneErase,
            FirstLaneOracleSimulation.ActionTrace.chainActions,
            Prod.map] using ih output
      | encodingQuery epoch | encodingSignAttempt epoch =>
          simp [globalFirstLaneEraseImpl,
            FirstLaneOracleSimulation.eagerTraceImpl,
            FirstLaneOracleSimulation.eagerImpl,
            FirstLaneOracleSimulation.traceFragment,
            FirstLaneOracleSimulation.ActionTrace.chainActions_append,
            RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell]
          simp [FirstLaneOracleSimulation.ActionTrace.chainActions]
          apply bind_congr
          intro output
          rw [hmap, id_map]
          simpa [FirstLaneOracleSimulation.eagerTraceImpl,
            RevealProbeOracleSimulation.eagerTraceImpl,
            globalFirstLaneErase,
            FirstLaneOracleSimulation.ActionTrace.chainActions,
            Prod.map] using ih output
      | probe index target =>
          simp [globalFirstLaneEraseImpl,
            FirstLaneOracleSimulation.eagerTraceImpl,
            FirstLaneOracleSimulation.eagerImpl,
            FirstLaneOracleSimulation.traceFragment,
            FirstLaneOracleSimulation.ActionTrace.chainActions_append,
            RevealProbeOracleSimulation.probeQuery,
            RevealProbeOracleSimulation.eagerTraceImpl,
            RevealProbeOracleSimulation.eagerImpl,
            RevealProbeOracleSimulation.traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell]
          simp [FirstLaneOracleSimulation.ActionTrace.chainActions]
          have h := ih PUnit.unit
          simp only [FirstLaneOracleSimulation.eagerTraceImpl,
            RevealProbeOracleSimulation.eagerTraceImpl,
            globalFirstLaneErase] at h
          rw [← h]
          simp [Functor.map_map,
            FirstLaneOracleSimulation.ActionTrace.chainActions]
      | reveal index =>
          simp [globalFirstLaneEraseImpl,
            FirstLaneOracleSimulation.eagerTraceImpl,
            FirstLaneOracleSimulation.eagerImpl,
            FirstLaneOracleSimulation.traceFragment,
            FirstLaneOracleSimulation.ActionTrace.chainActions_append,
            RevealProbeOracleSimulation.revealQuery,
            RevealProbeOracleSimulation.eagerTraceImpl,
            RevealProbeOracleSimulation.eagerImpl,
            RevealProbeOracleSimulation.traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell]
          simp [FirstLaneOracleSimulation.ActionTrace.chainActions]
          have h := ih (table index)
          simp only [FirstLaneOracleSimulation.eagerTraceImpl,
            RevealProbeOracleSimulation.eagerTraceImpl,
            globalFirstLaneErase] at h
          rw [← h]
          simp [Functor.map_map,
            FirstLaneOracleSimulation.ActionTrace.chainActions]

end XmssSecurity.CappedChain
