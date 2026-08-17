import XmssSecurity.CappedGlobalChainHighWholeCoverage

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem globalRunObserved_eq_true_of_probe_mem_of_no_reveal
    (table : GlobalChainValueIndex → Digest)
    (state : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (index : GlobalChainValueIndex) (target : Digest)
    (hhidden : state.revealed index = none)
    (hprobe : RevealProbeOracleSimulation.ObservedAction.probe index target ∈
      trace)
    (hhit : table index = target)
    (hnoreveal : ∀ value,
      RevealProbeOracleSimulation.ObservedAction.reveal index value ∉ trace) :
    RevealProbeOracleSimulation.runObserved table state trace = true := by
  induction trace generalizing state with
  | nil => simp at hprobe
  | cons action trace ih =>
      cases action with
      | probe candidate candidateTarget =>
          rw [List.mem_cons] at hprobe
          rcases hprobe with heq | htail
          · cases heq
            rw [RevealProbeOracleSimulation.runObserved, hhidden]
            apply RevealProbeOracleSimulation.runObserved_eq_true_of_tableHits
            unfold RevealProbeOracleSimulation.tableHits
            simp only [decide_eq_true_eq]
            refine ⟨index, ?_⟩
            simp [AdaptiveRevealMonitor.State.addPending, hhit]
          · simp only [RevealProbeOracleSimulation.runObserved]
            cases hrevealed : state.revealed candidate with
            | some value =>
                apply ih state hhidden htail
                intro revealValue hmem
                exact hnoreveal revealValue (by simp [hmem])
            | none =>
                apply ih (state.addPending candidate candidateTarget)
                · exact hhidden
                · exact htail
                · intro revealValue hmem
                  exact hnoreveal revealValue (by simp [hmem])
      | reveal candidate value =>
          have hne : candidate ≠ index := by
            intro heq
            subst candidate
            exact hnoreveal value (by simp)
          have htail :
              RevealProbeOracleSimulation.ObservedAction.probe index target ∈
                trace := by
            simpa using hprobe
          simp only [RevealProbeOracleSimulation.runObserved]
          cases hrevealed : state.revealed candidate with
          | some previous =>
              apply ih state hhidden htail
              intro revealValue hmem
              exact hnoreveal revealValue (by simp [hmem])
          | none =>
              by_cases hearly : table candidate ∈ state.pending candidate
              · simp [hearly]
              · rw [if_neg hearly]
                apply ih (state.install candidate (table candidate))
                · simpa [AdaptiveRevealMonitor.State.install,
                    Function.update_of_ne (Ne.symm hne)] using hhidden
                · exact htail
                · intro revealValue hmem
                  exact hnoreveal revealValue (by simp [hmem])

def globalHighMonitoredErasedResult
    (result : GlobalHighMonitoredProgramResult) :
    ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) :=
  let keyView := result.1.1.1
  let execution := result.2
  ((((keyView.publicKey, keyView.secretKey), keyView.cache),
    (actionTraceOutcome keyView.publicKey keyView.secretKey
      (execution.1, execution.2.2), execution.2.1.causal.cache)),
    execution.2.2)

noncomputable def globalForgeryPrimaryProbeTrace
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)) :
    RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  let encoding := actionTracedForgeryEncoding result
  List.ofFn fun chain : ChainIndex =>
    RevealProbeOracleSimulation.ObservedAction.probe
      (chain, result.1.2.1.forgery.epoch, encoding chain)
      (result.1.2.1.forgery.signature.chainValue chain)

noncomputable def globalHighMonitoredPublicProjection
    (result : GlobalHighMonitoredProgramResult) :
    (GlobalChainValueIndex → Digest) ×
      (Unit × RevealProbeOracleSimulation.ActionTrace
        GlobalChainValueIndex) :=
  (result.1.1.2,
    ((), result.2.2.1.trace ++ globalForgeryPrimaryProbeTrace
      (globalHighMonitoredErasedResult result)))

theorem globalForgeryPrimaryProbeTrace_mem
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace))
    (chain : ChainIndex) :
    RevealProbeOracleSimulation.ObservedAction.probe
        (chain, result.1.2.1.forgery.epoch,
          actionTracedForgeryEncoding result chain)
        (result.1.2.1.forgery.signature.chainValue chain) ∈
      globalForgeryPrimaryProbeTrace result := by
  simp [globalForgeryPrimaryProbeTrace]

theorem sourceGlobalTracedProgram_support_keyView
    (adversary : Adversary Concrete.scheme)
    (result : SourceGlobalTracedProgramResult)
    (hresult : result ∈ support (sourceGlobalTracedProgram adversary)) :
    result.1 ∈ support trajectoryProgrammedGlobalChainKeygen := by
  unfold sourceGlobalTracedProgram at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyView, hkeyView, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨execution, _hexecution, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact hkeyView

theorem globalHighMonitoredProgram_support_info
    (adversary : Adversary Concrete.scheme)
    (result : GlobalHighMonitoredProgramResult)
    (hresult : result ∈ support (globalHighMonitoredProgram adversary)) :
    result.1.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen ∧
      result.2 ∈ support
        (globalHighMonitoredDetailedExecution adversary result.1) := by
  unfold globalHighMonitoredProgram at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨right, hright, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨execution, hexecution, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact ⟨coupledGlobalChainKeygenWithBaseHighFull_support_keyView right
    hright, hexecution⟩

set_option maxRecDepth 1000000 in
theorem sourceGlobal_origin_implies_right_publicObservedHit
    (adversary : Adversary Concrete.scheme)
    (left : SourceGlobalTracedProgramResult)
    (right : GlobalHighMonitoredProgramResult)
    (hleftSupport : left ∈ support (sourceGlobalTracedProgram adversary))
    (hrightSupport : right ∈ support (globalHighMonitoredProgram adversary))
    (hrel : SourceGlobalHighMonitoredProgramRelation left right)
    (horigin : GlobalWinningOutcomeChainValueHasKeygenOrigin
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.1.2
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.2.2
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.1.1.2
      (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.2.1) :
    RevealProbeOracleSimulation.ObservedHit
      (globalHighMonitoredPublicProjection right) := by
  rcases hrel.2.1 with hgood | hbad
  · obtain ⟨chain, hchainOrigin⟩ := horigin
    obtain ⟨encoding, hdecode, hvalue⟩ :=
      winningOutcomeChainValueHasKeygenOrigin_eq_table
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.1.2
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.2.2
        (eraseGlobalChainKeygenView
          (sourceGlobalProgramResult left)).1.1.1.2
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult left)).1.2.1
        chain hchainOrigin
    have hleftKeySupport :=
      sourceGlobalTracedProgram_support_keyView adversary left hleftSupport
    obtain ⟨hrightKeySupport, hrightExecutionSupport⟩ :=
      globalHighMonitoredProgram_support_info adversary right hrightSupport
    obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal,
      _hretained⟩ := hgood.2.1
    have hparameter : left.1.secretKey.parameter =
        right.1.1.1.secretKey.parameter :=
      (programmedGlobal_secretKey_parameter_eq left.1 right.1 hrel.1
        hleftKeySupport hrightKeySupport).symm
    have hforgery : left.2.1.1 = right.2.1.1 :=
      congrArg Prod.fst hgood.1
    have htrace : left.2.2.2 = right.2.2.2 := hgood.2.2
    have hdecodeLeft : TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash left.2.2.1
          left.1.secretKey.parameter left.2.1.1.epoch
          (left.2.1.1.message, left.2.1.1.signature.randomness)) =
        some encoding := by
      simpa [sourceGlobalProgramResult, sourceGlobalExecutionResult,
        eraseGlobalChainKeygenView, actionTraceOutcome,
        Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey] using hdecode
    have hsourceUnrevealed :
        (chain, left.2.1.1.epoch, encoding chain) ∉
          GlobalReturnedChainValueCovered left.2.2.1 left.1.secretKey
            left.2.2.2.toSigningLog := by
      change (_, _) ∉ ReturnedChainValueCovered _ _ _ chain
      rw [returnedChainValueCovered_iff_mem_indices]
      exact hchainOrigin.1.forged_chain_coordinate_not_mem_returned encoding
        hdecodeLeft
    have hhash : Concrete.CacheView.encodingHash left.2.2.1
          left.1.secretKey.parameter left.2.1.1.epoch
          (left.2.1.1.message, left.2.1.1.signature.randomness) =
        Concrete.CacheView.encodingHash right.2.2.1.causal.cache
          left.1.secretKey.parameter left.2.1.1.epoch
          (left.2.1.1.message, left.2.1.1.signature.randomness) := by
      unfold Concrete.CacheView.encodingHash Concrete.CacheView.digestAt
      rw [hcausal.1 _ ⟨left.2.1.1.epoch, left.2.1.1.message,
        left.2.1.1.signature.randomness, rfl⟩]
    have hrightDecode : TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash right.2.2.1.causal.cache
          right.1.1.1.secretKey.parameter right.2.1.1.epoch
          (right.2.1.1.message, right.2.1.1.signature.randomness)) =
        some encoding := by
      rw [← hparameter, ← hforgery, ← hhash]
      exact hdecodeLeft
    have hencoding : actionTracedForgeryEncoding
        (globalHighMonitoredErasedResult right) = encoding := by
      unfold actionTracedForgeryEncoding
      rw [show Concrete.CacheView.encodingHash
          (globalHighMonitoredErasedResult right).1.2.2
          (globalHighMonitoredErasedResult right).1.1.1.2.parameter
          (globalHighMonitoredErasedResult right).1.2.1.forgery.epoch
          ((globalHighMonitoredErasedResult right).1.2.1.forgery.message,
            (globalHighMonitoredErasedResult
              right).1.2.1.forgery.signature.randomness) =
          Concrete.CacheView.encodingHash right.2.2.1.causal.cache
            right.1.1.1.secretKey.parameter right.2.1.1.epoch
            (right.2.1.1.message, right.2.1.1.signature.randomness) by
        rfl]
      rw [hrightDecode]
      rfl
    have hleftTable := trajectoryProgrammedGlobalChainKeygen_support_table
      left.1 hleftKeySupport
    have htables : left.1.table = right.1.1.2 :=
      hrel.1.1.toStable.1.1
    have hvalueLeft : left.2.1.1.signature.chainValue chain =
        globalKeygenChainValueTable left.1.cache left.1.secretKey
          (chain, left.2.1.1.epoch, encoding chain) := by
      simpa [sourceGlobalProgramResult, sourceGlobalExecutionResult,
        eraseGlobalChainKeygenView, actionTraceOutcome,
        globalKeygenChainValueTable, Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey, keygenChainValueTable] using hvalue
    have hrightValue : right.1.1.2
        (chain, right.2.1.1.epoch, encoding chain) =
          right.2.1.1.signature.chainValue chain := by
      rw [hforgery, hleftTable, htables] at hvalueLeft
      exact hvalueLeft.symm
    have hrightUnrevealed :
        (chain, right.2.1.1.epoch, encoding chain) ∉
          GlobalReturnedChainValueCovered right.2.2.1.causal.cache
            right.1.1.1.secretKey right.2.2.2.toSigningLog := by
      intro hmem
      apply hsourceUnrevealed
      apply globalReturnedChainValueCovered_of_comparableCaches
        left.1.secretKey.parameter left.2.2.1 right.2.2.1.causal.cache
          left.1.secretKey right.1.1.1.secretKey left.2.2.2.toSigningLog
            right.2.2.2.toSigningLog
      · rfl
      · exact hparameter.symm
      · exact congrArg AttackerActionTrace.toSigningLog htrace.symm
      · exact hcausal.1
      · simpa [hforgery] using hmem
    have hcovered :=
      globalHighMonitoredDetailedExecution_support_returnedCovered adversary
        right.1 right.2 hrightExecutionSupport
    let index : GlobalChainValueIndex :=
      (chain, right.2.1.1.epoch, encoding chain)
    let target := right.2.1.1.signature.chainValue chain
    have hprobe : RevealProbeOracleSimulation.ObservedAction.probe index target ∈
        right.2.2.1.trace ++ globalForgeryPrimaryProbeTrace
          (globalHighMonitoredErasedResult right) := by
      apply List.mem_append_right
      change RevealProbeOracleSimulation.ObservedAction.probe
          (chain, right.2.1.1.epoch, encoding chain)
          (right.2.1.1.signature.chainValue chain) ∈
        globalForgeryPrimaryProbeTrace
          (globalHighMonitoredErasedResult right)
      have hprimary := globalForgeryPrimaryProbeTrace_mem
        (globalHighMonitoredErasedResult right) chain
      rw [congrFun hencoding chain] at hprimary
      simpa [globalHighMonitoredErasedResult, actionTraceOutcome] using hprimary
    have hnoreveal : ∀ value,
        RevealProbeOracleSimulation.ObservedAction.reveal index value ∉
          right.2.2.1.trace ++ globalForgeryPrimaryProbeTrace
            (globalHighMonitoredErasedResult right) := by
      intro value hmem
      rcases List.mem_append.mp hmem with hprefix | hsuffix
      · exact hrightUnrevealed
          (hcovered.2 index value (by simpa [index] using hprefix))
      · simp [globalForgeryPrimaryProbeTrace] at hsuffix
    unfold RevealProbeOracleSimulation.ObservedHit
    dsimp only [globalHighMonitoredPublicProjection]
    apply globalRunObserved_eq_true_of_probe_mem_of_no_reveal
      right.1.1.2 AdaptiveRevealMonitor.State.empty
        (right.2.2.1.trace ++ globalForgeryPrimaryProbeTrace
          (globalHighMonitoredErasedResult right)) index target
    · simp [AdaptiveRevealMonitor.State.empty]
    · exact hprobe
    · simpa [index, target] using hrightValue
    · exact hnoreveal
  · unfold RevealProbeOracleSimulation.ObservedHit
    dsimp only [globalHighMonitoredPublicProjection]
    apply RevealProbeOracleSimulation.runObserved_append_eq_true_of_prefix
    exact right.2.2.1.bad_implies_runObserved right.1.1.2 hrel.2.2 hbad

theorem sourceGlobal_origin_probability_le_publicObservedHit
    (adversary : Adversary Concrete.scheme) :
    Pr[fun left : SourceGlobalTracedProgramResult =>
        GlobalWinningOutcomeChainValueHasKeygenOrigin
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult left)).1.1.2
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult left)).1.2.2
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult left)).1.1.1.2
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult left)).1.2.1 |
      sourceGlobalTracedProgram adversary] ≤
    Pr[fun right : GlobalHighMonitoredProgramResult =>
        RevealProbeOracleSimulation.ObservedHit
          (globalHighMonitoredPublicProjection right) |
      globalHighMonitoredProgram adversary] := by
  apply probEvent_le_of_relTriple
    (relTriple_with_support
      (relTriple_sourceGlobal_globalHighMonitored_program adversary))
  intro left right hrel horigin
  exact sourceGlobal_origin_implies_right_publicObservedHit adversary left right
    hrel.2.1 hrel.2.2 hrel.1 horigin

theorem evalDist_sourceGlobalErased_eq_originalActionTraced
    (adversary : Adversary Concrete.scheme) :
    evalDist ((fun left : SourceGlobalTracedProgramResult =>
        eraseGlobalChainKeygenView (sourceGlobalProgramResult left)) <$>
      sourceGlobalTracedProgram adversary) =
    evalDist (detailedGameWithKeygenCacheAndActionTrace adversary) := by
  calc
    _ = evalDist (eraseGlobalChainKeygenView <$>
        (sourceGlobalProgramResult <$> sourceGlobalTracedProgram adversary)) := by
      simp [Functor.map_map]
    _ = evalDist (eraseGlobalChainKeygenView <$>
        trajectoryProgrammedGlobalChainDetailedGame adversary) := by
      rw [sourceGlobalTracedProgram_eq_trajectoryProgrammedDetailedGame]
    _ = _ :=
      (evalDist_originalActionTracedGame_eq_erase_globalProgrammed
        adversary).symm

theorem globalWinningChainOrigin_probability_le_publicObservedHit
    (adversary : Adversary Concrete.scheme) :
    Pr[fun result =>
        GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
          result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
    Pr[fun right : GlobalHighMonitoredProgramResult =>
        RevealProbeOracleSimulation.ObservedHit
          (globalHighMonitoredPublicProjection right) |
      globalHighMonitoredProgram adversary] := by
  calc
    _ = Pr[fun result =>
          GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.1.2
            result.1.2.2 result.1.1.1.2 result.1.2.1 |
        detailedGameWithKeygenCacheAndActionTrace adversary] := by
      rw [← detailedGameWithKeygenCacheAndActionTrace_projection,
        probEvent_map]
      rfl
    _ = Pr[fun left : SourceGlobalTracedProgramResult =>
          GlobalWinningOutcomeChainValueHasKeygenOrigin
            (eraseGlobalChainKeygenView
              (sourceGlobalProgramResult left)).1.1.2
            (eraseGlobalChainKeygenView
              (sourceGlobalProgramResult left)).1.2.2
            (eraseGlobalChainKeygenView
              (sourceGlobalProgramResult left)).1.1.1.2
            (eraseGlobalChainKeygenView
              (sourceGlobalProgramResult left)).1.2.1 |
        sourceGlobalTracedProgram adversary] := by
      let event := fun result :
          ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
            (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) =>
        GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.1.2
          result.1.2.2 result.1.1.1.2 result.1.2.1
      let project := fun left : SourceGlobalTracedProgramResult =>
        eraseGlobalChainKeygenView (sourceGlobalProgramResult left)
      change Pr[event | detailedGameWithKeygenCacheAndActionTrace adversary] =
        Pr[event ∘ project | sourceGlobalTracedProgram adversary]
      rw [← probEvent_map]
      exact probEvent_congr' (fun _ _ => Iff.rfl)
        (evalDist_sourceGlobalErased_eq_originalActionTraced adversary).symm
    _ ≤ _ := sourceGlobal_origin_probability_le_publicObservedHit adversary

end XmssSecurity.CappedChain
