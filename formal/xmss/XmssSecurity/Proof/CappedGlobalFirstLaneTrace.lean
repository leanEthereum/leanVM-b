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
      cases input with
      | uniform n =>
          simp [globalFirstLaneEraseImpl,
            FirstLaneOracleSimulation.uniformQuery,
            FirstLaneOracleSimulation.eagerTraceImpl,
            FirstLaneOracleSimulation.eagerImpl,
            FirstLaneOracleSimulation.traceFragment,
            FirstLaneOracleSimulation.ActionTrace.chainActions_append,
            RevealProbeOracleSimulation.uniformQuery,
            RevealProbeOracleSimulation.eagerTraceImpl,
            RevealProbeOracleSimulation.eagerImpl,
            RevealProbeOracleSimulation.traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell, ih]
          simp [FirstLaneOracleSimulation.ActionTrace.chainActions, ih]
          apply bind_congr
          intro output
          have hmap : Prod.map id (fun x => x) =
              (id : α × RevealProbeOracleSimulation.ActionTrace
                GlobalChainValueIndex →
                α × RevealProbeOracleSimulation.ActionTrace
                  GlobalChainValueIndex) := by
            funext result
            cases result
            rfl
          rw [hmap, id_map]
          simpa [FirstLaneOracleSimulation.eagerTraceImpl,
            RevealProbeOracleSimulation.eagerTraceImpl,
            globalFirstLaneErase, FirstLaneOracleSimulation.ActionTrace.chainActions,
            Prod.map] using ih output
      | encodingQuery epoch =>
          simp [globalFirstLaneEraseImpl,
            FirstLaneOracleSimulation.eagerTraceImpl,
            FirstLaneOracleSimulation.eagerImpl,
            FirstLaneOracleSimulation.traceFragment,
            FirstLaneOracleSimulation.ActionTrace.chainActions_append,
            RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell, ih]
          simp [FirstLaneOracleSimulation.ActionTrace.chainActions, ih]
          apply bind_congr
          intro output
          have hmap : Prod.map id (fun x => x) =
              (id : α × RevealProbeOracleSimulation.ActionTrace
                GlobalChainValueIndex →
                α × RevealProbeOracleSimulation.ActionTrace
                  GlobalChainValueIndex) := by
            funext result
            cases result
            rfl
          rw [hmap, id_map]
          simpa [FirstLaneOracleSimulation.eagerTraceImpl,
            RevealProbeOracleSimulation.eagerTraceImpl,
            globalFirstLaneErase, FirstLaneOracleSimulation.ActionTrace.chainActions,
            Prod.map] using ih output
      | encodingSignAttempt epoch =>
          simp [globalFirstLaneEraseImpl,
            FirstLaneOracleSimulation.eagerTraceImpl,
            FirstLaneOracleSimulation.eagerImpl,
            FirstLaneOracleSimulation.traceFragment,
            FirstLaneOracleSimulation.ActionTrace.chainActions_append,
            RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell, ih]
          simp [FirstLaneOracleSimulation.ActionTrace.chainActions, ih]
          apply bind_congr
          intro output
          have hmap : Prod.map id (fun x => x) =
              (id : α × RevealProbeOracleSimulation.ActionTrace
                GlobalChainValueIndex →
                α × RevealProbeOracleSimulation.ActionTrace
                  GlobalChainValueIndex) := by
            funext result
            cases result
            rfl
          rw [hmap, id_map]
          simpa [FirstLaneOracleSimulation.eagerTraceImpl,
            RevealProbeOracleSimulation.eagerTraceImpl,
            globalFirstLaneErase, FirstLaneOracleSimulation.ActionTrace.chainActions,
            Prod.map] using ih output
      | probe index target =>
          simp [globalFirstLaneEraseImpl,
            FirstLaneOracleSimulation.probeQuery,
            FirstLaneOracleSimulation.eagerTraceImpl,
            FirstLaneOracleSimulation.eagerImpl,
            FirstLaneOracleSimulation.traceFragment,
            FirstLaneOracleSimulation.ActionTrace.chainActions_append,
            RevealProbeOracleSimulation.probeQuery,
            RevealProbeOracleSimulation.eagerTraceImpl,
            RevealProbeOracleSimulation.eagerImpl,
            RevealProbeOracleSimulation.traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell, ih]
          simp [FirstLaneOracleSimulation.ActionTrace.chainActions, ih,
            Functor.map_map]
          have h := ih PUnit.unit
          simp only [FirstLaneOracleSimulation.eagerTraceImpl,
            RevealProbeOracleSimulation.eagerTraceImpl,
            globalFirstLaneErase] at h
          rw [← h]
          simp [Functor.map_map,
            FirstLaneOracleSimulation.ActionTrace.chainActions]
      | reveal index =>
          simp [globalFirstLaneEraseImpl,
            FirstLaneOracleSimulation.revealQuery,
            FirstLaneOracleSimulation.eagerTraceImpl,
            FirstLaneOracleSimulation.eagerImpl,
            FirstLaneOracleSimulation.traceFragment,
            FirstLaneOracleSimulation.ActionTrace.chainActions_append,
            RevealProbeOracleSimulation.revealQuery,
            RevealProbeOracleSimulation.eagerTraceImpl,
            RevealProbeOracleSimulation.eagerImpl,
            RevealProbeOracleSimulation.traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell, ih]
          simp [FirstLaneOracleSimulation.ActionTrace.chainActions, ih,
            Functor.map_map]
          have h := ih (table index)
          simp only [FirstLaneOracleSimulation.eagerTraceImpl,
            RevealProbeOracleSimulation.eagerTraceImpl,
            globalFirstLaneErase] at h
          rw [← h]
          simp [Functor.map_map,
            FirstLaneOracleSimulation.ActionTrace.chainActions]

theorem map_globalFirstLaneEagerExperiment_chainProjection
    (computation : OracleComp GlobalFirstLaneWorld α) :
    (fun result =>
        (result.1, (result.2.1, result.2.2.chainActions))) <$>
        FirstLaneOracleSimulation.eagerExperiment computation =
      RevealProbeOracleSimulation.eagerExperiment
        (globalFirstLaneErase computation) := by
  unfold FirstLaneOracleSimulation.eagerExperiment
    RevealProbeOracleSimulation.eagerExperiment
  rw [map_bind]
  apply bind_congr
  intro table
  rw [← simulate_globalFirstLaneEagerTrace_chainProjection table computation]
  rw [map_bind]
  simp only [map_eq_bind_pure_comp, pure_bind, bind_assoc,
    Function.comp_apply]

theorem evalDist_globalFirstLanePublic_chainProjection_eq_globalHigh
    (adversary : Adversary Concrete.scheme) :
    evalDist ((fun result =>
        (result.1, (result.2.1, result.2.2.chainActions))) <$>
          FirstLaneOracleSimulation.eagerExperiment
            (globalFirstLanePublicProgram adversary)) =
      evalDist (RevealProbeOracleSimulation.eagerExperiment
        (globalHighDirectPublicProgram adversary)) := by
  rw [map_globalFirstLaneEagerExperiment_chainProjection]
  rw [(globalFirstLaneErase_publicProgram adversary).eq]

end XmssSecurity.CappedChain
