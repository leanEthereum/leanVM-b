import XmssSecurity.Proof.CappedGlobalChainHighPublicProgram

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

noncomputable def globalHighDirectPublicProgram
    (adversary : Adversary Concrete.scheme) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      Unit := do
  let result ← globalHighDirectProgram adversary
  RevealProbeOracleSimulation.emitObservedTrace
    (globalHighDirectForgeryPrimaryProbeTrace result)

end XmssSecurity.CappedChain
