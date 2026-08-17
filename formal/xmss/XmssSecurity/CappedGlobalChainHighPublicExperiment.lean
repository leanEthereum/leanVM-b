import XmssSecurity.CappedGlobalChainHighPublicProgram

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem traceAgrees_of_all_probes
    (table : Index → Digest)
    (trace : RevealProbeOracleSimulation.ActionTrace Index)
    (hprobes : ∀ action ∈ trace, ∃ index target,
      action = .probe index target) :
    RevealProbeOracleSimulation.TraceAgrees table trace := by
  induction trace with
  | nil => trivial
  | cons action rest ih =>
      obtain ⟨index, target, rfl⟩ := hprobes action (by simp)
      simp only [RevealProbeOracleSimulation.TraceAgrees]
      apply ih
      intro candidate hcandidate
      exact hprobes candidate (by simp [hcandidate])

theorem globalHighDirectForgeryPrimaryProbeTrace_all_probes
    (result : GlobalHighDirectResult) (action :
      RevealProbeOracleSimulation.ObservedAction GlobalChainValueIndex)
    (haction : action ∈ globalHighDirectForgeryPrimaryProbeTrace result) :
    ∃ index target, action = .probe index target := by
  unfold globalHighDirectForgeryPrimaryProbeTrace
    globalForgeryPrimaryProbeTrace at haction
  simp only [List.mem_ofFn] at haction
  obtain ⟨chain, rfl⟩ := haction
  exact ⟨_, _, rfl⟩

theorem globalHighDirectForgeryPrimaryProbeTrace_agrees
    (table : GlobalChainValueIndex → Digest)
    (result : GlobalHighDirectResult) :
    RevealProbeOracleSimulation.TraceAgrees table
      (globalHighDirectForgeryPrimaryProbeTrace result) := by
  apply traceAgrees_of_all_probes
  intro action haction
  exact globalHighDirectForgeryPrimaryProbeTrace_all_probes result action
    haction

theorem simulate_eagerTrace_bind_emitObservedTrace
    (table : Index → Digest)
    (computation : OracleComp (RevealProbeOracleSimulation.World Index) α)
    (suffix : α → RevealProbeOracleSimulation.ActionTrace Index)
    (hagrees : ∀ result, RevealProbeOracleSimulation.TraceAgrees table
      (suffix result)) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table) (do
      let result ← computation
      RevealProbeOracleSimulation.emitObservedTrace (suffix result))).run =
    (fun result => ((), result.2 ++ suffix result.1)) <$>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        computation).run := by
  rw [simulateQ_bind, WriterT.run_bind']
  apply bind_congr
  intro result
  rcases result with ⟨result, trace⟩
  simp only [Function.comp_apply]
  rw [RevealProbeOracleSimulation.simulate_eagerTrace_emitObservedTrace]
  · rfl
  · exact hagrees result

noncomputable def globalHighDirectPublicProgram
    (adversary : Adversary Concrete.cappedScheme) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      Unit := do
  let result ← globalHighDirectProgram adversary
  RevealProbeOracleSimulation.emitObservedTrace
    (globalHighDirectForgeryPrimaryProbeTrace result)

theorem eagerExperiment_globalHighDirectPublicProgram_eq_append
    (adversary : Adversary Concrete.cappedScheme) :
    RevealProbeOracleSimulation.eagerExperiment
      (globalHighDirectPublicProgram adversary) =
    appendGlobalHighDirectPublicTrace <$>
      globalHighDirectEagerExperiment adversary := by
  unfold globalHighDirectPublicProgram globalHighDirectEagerExperiment
    RevealProbeOracleSimulation.eagerExperiment
  simp only [map_bind]
  apply bind_congr
  intro table
  rw [simulate_eagerTrace_bind_emitObservedTrace table
    (globalHighDirectProgram adversary)
    globalHighDirectForgeryPrimaryProbeTrace
    (globalHighDirectForgeryPrimaryProbeTrace_agrees table)]
  simp [appendGlobalHighDirectPublicTrace, map_eq_bind_pure_comp,
    bind_assoc]

theorem evalDist_globalHighMonitoredPublicProjection_eq_publicExperiment
    (adversary : Adversary Concrete.cappedScheme) :
    evalDist (globalHighMonitoredPublicProjection <$>
      globalHighMonitoredProgram adversary) =
    evalDist (RevealProbeOracleSimulation.eagerExperiment
      (globalHighDirectPublicProgram adversary)) := by
  rw [evalDist_globalHighMonitoredPublicProjection_eq_append_direct]
  rw [eagerExperiment_globalHighDirectPublicProgram_eq_append]

end XmssSecurity.CappedChain
