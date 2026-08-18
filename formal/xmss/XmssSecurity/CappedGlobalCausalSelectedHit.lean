import XmssSecurity.CappedGlobalCausalSelectedExperiment

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

theorem globalCausalSelectedContinuation_eq_pure
    (keyResult : (PublicKey × SecretKey) × GlobalCausalHashState)
    (table : GlobalChainValueIndex → Digest)
    (execution : ((((Forgery × Bool) × AttackerActionTrace) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    globalCausalSelectedContinuation keyResult table execution =
      pure (globalCausalDetailedResult keyResult execution.1,
        execution.2 ++
          (globalSelectedUnrevealedProbes
            (globalCausalDetailedResult keyResult execution.1)).map
              (fun probe =>
                RevealProbeOracleSimulation.ObservedAction.probe
                  probe.1 probe.2)) := by
  simp [globalCausalSelectedContinuation,
    simulate_eagerTrace_emitGlobalProbes]

theorem globalCausalSelectedTrace_eagerHit_of_selected_hit
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (execution : ((((Forgery × Bool) × AttackerActionTrace) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (base : GlobalChainValueIndex → Digest)
    (hexecution : execution ∈ support
      (globalCausalLazyDetailedGameAfterKeygen adversary
        (globalCausalKeyResultOfReal keyResult).1.1
        (globalCausalKeyResultOfReal keyResult).1.2
        (globalCausalKeyResultOfReal keyResult).2.finishKeygen))
    (hhit : let causalKeyResult := globalCausalKeyResultOfReal keyResult
      let detailed := globalCausalDetailedResult causalKeyResult execution.1
      let table := globalCausalInstalledTable execution.1.2 base
      ∃ probe ∈ globalSelectedUnrevealedProbes detailed,
        table probe.1 = probe.2) :
    let causalKeyResult := globalCausalKeyResultOfReal keyResult
    let detailed := globalCausalDetailedResult causalKeyResult execution.1
    let table := globalCausalInstalledTable execution.1.2 base
    RevealProbeOracleSimulation.EagerHit
      (table, (detailed, execution.2 ++
        (globalSelectedUnrevealedProbes detailed).map
          (fun selected =>
            RevealProbeOracleSimulation.ObservedAction.probe
              selected.1 selected.2))) := by
  let causalKeyResult := globalCausalKeyResultOfReal keyResult
  let detailed := globalCausalDetailedResult causalKeyResult execution.1
  let table := globalCausalInstalledTable execution.1.2 base
  obtain ⟨probe, hprobe, htable⟩ := hhit
  have hcovered :=
    globalCausalLazyDetailedGameAfterKeygen_support_returnedCovered
      adversary causalKeyResult.1.1 causalKeyResult.1.2
        causalKeyResult.2.finishKeygen (by intro index; rfl)
        execution hexecution
  have hnoExecutionReveal : ∀ value,
      RevealProbeOracleSimulation.ObservedAction.reveal probe.1 value ∉
        execution.2 := by
    intro value hreveal
    have hprobeNotCovered :=
      globalSelectedUnrevealedProbes_avoids_covered detailed probe hprobe
    exact hprobeNotCovered (hcovered.2 probe.1 value hreveal)
  have hprobeInTrace :
      RevealProbeOracleSimulation.ObservedAction.probe probe.1 probe.2 ∈
        execution.2 ++
          (globalSelectedUnrevealedProbes detailed).map
            (fun selected =>
              RevealProbeOracleSimulation.ObservedAction.probe
                selected.1 selected.2) := by
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨probe, hprobe, rfl⟩
  have hnoReveal : ∀ value,
      RevealProbeOracleSimulation.ObservedAction.reveal probe.1 value ∉
        execution.2 ++
          (globalSelectedUnrevealedProbes detailed).map
            (fun selected =>
              RevealProbeOracleSimulation.ObservedAction.probe
                selected.1 selected.2) := by
    intro value hreveal
    rw [List.mem_append] at hreveal
    exact hreveal.elim (hnoExecutionReveal value) (by
      intro hemitted
      rw [List.mem_map] at hemitted
      obtain ⟨selected, _hselected, heq⟩ := hemitted
      cases heq)
  unfold RevealProbeOracleSimulation.EagerHit
  rw [RevealProbeOracleSimulation.traceHits_eq_true_iff_hasHit]
  exact RevealProbeOracleSimulation.HasHit.of_mem_probe_of_no_reveal
    table _ probe.1 probe.2 hprobeInTrace hnoReveal htable

set_option maxRecDepth 500000 in
set_option linter.constructorNameAsVariable false in
theorem globalCausalSelectedLazyExperiment_support_eagerHit_of_selected_hit
    (adversary : Adversary Concrete.scheme)
    (result : (GlobalChainValueIndex → Digest) ×
      (DetailedActionTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hresult : result ∈ support
      (globalCausalSelectedLazyExperiment adversary))
    (hhit : ∃ probe ∈ globalSelectedUnrevealedProbes result.2.1,
      result.1 probe.1 = probe.2) :
    RevealProbeOracleSimulation.EagerHit result := by
  unfold globalCausalSelectedLazyExperiment at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, _hkeyResult, hafterKeygen⟩ := hresult
  unfold globalCausalSelectedLazyAfterKeygenExperiment at hafterKeygen
  rw [mem_support_bind_iff] at hafterKeygen
  obtain ⟨execution, hexecution, hbaseBind⟩ := hafterKeygen
  rw [mem_support_bind_iff] at hbaseBind
  obtain ⟨base, _hbase, hselectedBind⟩ := hbaseBind
  dsimp only at hselectedBind
  rw [mem_support_bind_iff] at hselectedBind
  obtain ⟨selected, hselected, hresultPure⟩ := hselectedBind
  simp only [support_pure, Set.mem_singleton_iff] at hresultPure
  rw [globalCausalSelectedContinuation_eq_pure] at hselected
  simp only [support_pure, Set.mem_singleton_iff] at hselected
  rw [hresultPure] at hhit ⊢
  rw [hselected] at hhit ⊢
  exact globalCausalSelectedTrace_eagerHit_of_selected_hit
    adversary keyResult execution base hexecution hhit

end XmssSecurity.CappedChain
