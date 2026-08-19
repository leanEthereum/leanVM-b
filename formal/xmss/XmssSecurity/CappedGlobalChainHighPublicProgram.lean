import XmssSecurity.CappedGlobalChainHighDirectDistribution

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

def globalHighDirectErasedResult
    (result : GlobalHighDirectResult) :
    ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) :=
  let keyView := result.1.1
  let execution := result.2
  ((((keyView.publicKey, keyView.secretKey), keyView.cache),
    (actionTraceOutcome keyView.publicKey keyView.secretKey
      (execution.1, []), execution.2.cache)), [])

noncomputable def globalHighDirectForgeryPrimaryProbeTrace
    (result : GlobalHighDirectResult) :
    RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  globalForgeryPrimaryProbeTrace (globalHighDirectErasedResult result)

theorem observedProbeCount_globalForgeryPrimaryProbeTrace
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)) :
    RevealProbeOracleSimulation.observedProbeCount
      (globalForgeryPrimaryProbeTrace result) = numChains := by
  have hcount : ∀ trace : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex,
      (∀ action ∈ trace, ∃ index target, action = .probe index target) →
      RevealProbeOracleSimulation.observedProbeCount trace = trace.length := by
    intro trace hprobes
    induction trace with
    | nil => rfl
    | cons action rest ih =>
        obtain ⟨index, target, rfl⟩ := hprobes action (by simp)
        simp only [RevealProbeOracleSimulation.observedProbeCount,
          List.length_cons, Nat.succ.injEq]
        apply ih
        intro candidate hcandidate
        exact hprobes candidate (by simp [hcandidate])
  rw [hcount]
  · unfold globalForgeryPrimaryProbeTrace
    simp [numChains]
  · intro action haction
    unfold globalForgeryPrimaryProbeTrace at haction
    simp only [List.mem_ofFn] at haction
    obtain ⟨chain, rfl⟩ := haction
    exact ⟨_, _, rfl⟩

theorem observedProbeCount_globalHighDirectForgeryPrimaryProbeTrace
    (result : GlobalHighDirectResult) :
    RevealProbeOracleSimulation.observedProbeCount
        (globalHighDirectForgeryPrimaryProbeTrace result) = numChains := by
  unfold globalHighDirectForgeryPrimaryProbeTrace
  exact observedProbeCount_globalForgeryPrimaryProbeTrace _

noncomputable def appendGlobalHighDirectPublicTrace
    (result : (GlobalChainValueIndex → Digest) ×
      (GlobalHighDirectResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    (GlobalChainValueIndex → Digest) ×
      (Unit × RevealProbeOracleSimulation.ActionTrace
        GlobalChainValueIndex) :=
  (result.1, ((), result.2.2 ++
    globalHighDirectForgeryPrimaryProbeTrace result.2.1))

theorem globalForgeryPrimaryProbeTrace_eq_of_public_fields
    (left right : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace))
    (hsecret : left.1.1.1.2 = right.1.1.1.2)
    (hforgery : left.1.2.1.forgery = right.1.2.1.forgery)
    (hcache : left.1.2.2 = right.1.2.2) :
    globalForgeryPrimaryProbeTrace left =
      globalForgeryPrimaryProbeTrace right := by
  unfold globalForgeryPrimaryProbeTrace actionTracedForgeryEncoding
  rw [hsecret, hforgery, hcache]

theorem globalHighMonitored_forgeryProbeTrace_eq_direct
    (result : GlobalHighMonitoredProgramResult) :
    globalForgeryPrimaryProbeTrace (globalHighMonitoredErasedResult result) =
      globalHighDirectForgeryPrimaryProbeTrace
        (globalHighMonitoredDirectProjection result).2.1 := by
  unfold globalHighDirectForgeryPrimaryProbeTrace
  apply globalForgeryPrimaryProbeTrace_eq_of_public_fields <;> rfl

theorem globalHighMonitoredPublicProjection_eq_append_direct
    (result : GlobalHighMonitoredProgramResult) :
    globalHighMonitoredPublicProjection result =
      appendGlobalHighDirectPublicTrace
        (globalHighMonitoredDirectProjection result) := by
  unfold globalHighMonitoredPublicProjection appendGlobalHighDirectPublicTrace
    globalHighMonitoredDirectProjection
  rw [globalHighMonitored_forgeryProbeTrace_eq_direct result]
  rfl

theorem evalDist_map_congr_of_evalDist_eq
    (project : α → β) (left right : ProbComp α)
    (hdist : evalDist left = evalDist right) :
    evalDist (project <$> left) = evalDist (project <$> right) := by
  rw [evalDist_map, evalDist_map, hdist]

theorem evalDist_map_factor_of_evalDist_eq
    (project : α → γ) (outer : β → γ) (inner : α → β)
    (left : ProbComp α) (right : ProbComp β)
    (hproject : project = outer ∘ inner)
    (hdist : evalDist (inner <$> left) = evalDist right) :
    evalDist (project <$> left) = evalDist (outer <$> right) := by
  subst project
  simpa [Functor.map_map, Function.comp_def] using
    (evalDist_map_congr_of_evalDist_eq outer (inner <$> left) right hdist)

theorem evalDist_globalHighMonitoredPublicProjection_eq_append_direct
    (adversary : Adversary Concrete.scheme) :
    evalDist (globalHighMonitoredPublicProjection <$>
      globalHighMonitoredProgram adversary) =
    evalDist (appendGlobalHighDirectPublicTrace <$>
      globalHighDirectEagerExperiment adversary) := by
  have hprojection : globalHighMonitoredPublicProjection =
      appendGlobalHighDirectPublicTrace ∘
        globalHighMonitoredDirectProjection := by
    funext result
    exact globalHighMonitoredPublicProjection_eq_append_direct result
  exact evalDist_map_factor_of_evalDist_eq
    globalHighMonitoredPublicProjection appendGlobalHighDirectPublicTrace
      globalHighMonitoredDirectProjection (globalHighMonitoredProgram adversary)
        (globalHighDirectEagerExperiment adversary) hprojection
          (evalDist_globalHighMonitoredDirectProjection_eq_eagerExperiment
            adversary)

end XmssSecurity.CappedChain
