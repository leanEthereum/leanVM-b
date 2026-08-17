import XmssSecurity.CappedGlobalCausalInstalledTable
import XmssSecurity.CappedGlobalCausalSigningResampling

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable local instance globalCausalInstalledSampleableChainTable :
    SampleableType (GlobalChainValueIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainValueIndex → Digest)

noncomputable def globalCausalLazyAttackerHashStep
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    ProbComp ((HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  match globalCausalAttackerHashPlan secretKey input state with
  | .cached output =>
      pure ((output, globalCausalRecordedState secretKey input state), [])
  | .redirect output =>
      pure ((output,
        { (globalCausalRecordedState secretKey input state) with
          cache := (globalCausalRecordedState secretKey input state).cache.cacheQuery
            input output }), [])
  | .fresh => do
      let hashResult ← (randomOracle input).run
        (globalCausalRecordedState secretKey input state).cache
      pure ((hashResult.1,
        { (globalCausalRecordedState secretKey input state) with
          cache := hashResult.2 }), [])
  | .reveal index =>
      match state.revealed index with
      | some value => do
          let output ← Rom.sampleHashOutputWithDigest value
          pure ((output, globalCausalRevealResultState secretKey input state
            index value output),
            [RevealProbeOracleSimulation.ObservedAction.reveal index value])
      | none => do
          let output ← $ᵗ HashOutput
          let value := truncateHash output
          pure ((output, globalCausalRevealResultState secretKey input state
            index value output),
            [RevealProbeOracleSimulation.ObservedAction.reveal index value])

noncomputable def globalCausalInstalledRevealContinuation
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((HashOutput × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α)
    (base : GlobalChainValueIndex → Digest) (value : Digest)
    (output : HashOutput) : ProbComp α :=
  continuation
    (globalCausalInstalledTable
      (globalCausalRevealResultState secretKey input state index value output) base)
    ((output, globalCausalRevealResultState secretKey input state
      index value output),
      [RevealProbeOracleSimulation.ObservedAction.reveal index value])

theorem globalCausalInstalledRevealContinuation_update_base
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((HashOutput × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α)
    (base : GlobalChainValueIndex → Digest) (value : Digest)
    (output : HashOutput) :
    globalCausalInstalledRevealContinuation secretKey input state index
        continuation (Function.update base index value) value output =
      globalCausalInstalledRevealContinuation secretKey input state index
        continuation base value output := by
  unfold globalCausalInstalledRevealContinuation
  rw [globalCausalInstalledTable_update_base_of_revealed
    (globalCausalRevealResultState secretKey input state index value output)
    base index value value
    (globalCausalRevealResultState_revealed_self
      secretKey input state index value output)]

noncomputable def globalCausalProgrammedRevealContinuation
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((HashOutput × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    ProbComp α := do
  let output ← $ᵗ HashOutput
  let base ← $ᵗ (GlobalChainValueIndex → Digest)
  let value := truncateHash output
  globalCausalInstalledRevealContinuation secretKey input state index
    continuation (Function.update base index value) value output

noncomputable def globalCausalFreshBaseRevealContinuation
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((HashOutput × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    ProbComp α := do
  let output ← $ᵗ HashOutput
  let base ← $ᵗ (GlobalChainValueIndex → Digest)
  let value := truncateHash output
  globalCausalInstalledRevealContinuation secretKey input state index
    continuation base value output

theorem evalDist_globalCausalProgrammedRevealContinuation_eq_freshBase
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((HashOutput × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    𝒟[globalCausalProgrammedRevealContinuation secretKey input state
      index continuation] =
    𝒟[globalCausalFreshBaseRevealContinuation secretKey input state
      index continuation] := by
  unfold globalCausalProgrammedRevealContinuation
    globalCausalFreshBaseRevealContinuation
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro output
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro base
  rw [globalCausalInstalledRevealContinuation_update_base]

set_option maxRecDepth 100000 in
theorem evalDist_installed_globalCausalAttackerHashQuery_continuation_eq_lazy
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((HashOutput × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let table := globalCausalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQuery secretKey input).run state)).run
      continuation (globalCausalInstalledTable result.1.2 base) result] =
    𝒟[do
      let result ← globalCausalLazyAttackerHashStep secretKey input state
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      continuation (globalCausalInstalledTable result.1.2 base) result] := by
  generalize hplan : globalCausalAttackerHashPlan secretKey input state = plan
  cases plan with
  | cached output =>
      simp only [globalCausalLazyAttackerHashStep, hplan, pure_bind]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      simp_rw [globalCausalAttackerHashQuery_run, hplan]
      simp
  | redirect output =>
      simp only [globalCausalLazyAttackerHashStep, hplan, pure_bind]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      simp_rw [globalCausalAttackerHashQuery_run, hplan]
      simp
  | fresh =>
      simp only [globalCausalLazyAttackerHashStep, hplan, pure_bind]
      calc
        _ = 𝒟[do
            let base ← $ᵗ (GlobalChainValueIndex → Digest)
            let hashResult ← (randomOracle input).run
              (globalCausalRecordedState secretKey input state).cache
            continuation
              (globalCausalInstalledTable
                { (globalCausalRecordedState secretKey input state) with
                  cache := hashResult.2 } base)
              ((hashResult.1,
                { (globalCausalRecordedState secretKey input state) with
                  cache := hashResult.2 }), [])] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro base
          simp_rw [globalCausalAttackerHashQuery_run, hplan]
          rw [simulate_eagerTrace_globalCausalHashQuery]
          simp [GlobalCausalHashState.setCache, map_eq_bind_pure_comp]
        _ = _ := by
          rw [OracleComp.DeferredSampling.evalDist_bind_comm]
          simp [bind_assoc]
  | reveal index =>
      cases hrevealed : state.revealed index with
      | some value =>
          simp only [globalCausalLazyAttackerHashStep, hplan, hrevealed,
            pure_bind]
          calc
            _ = 𝒟[do
                let base ← $ᵗ (GlobalChainValueIndex → Digest)
                let output ← Rom.sampleHashOutputWithDigest value
                continuation
                  (globalCausalInstalledTable
                    (globalCausalRevealResultState secretKey input state
                      index value output) base)
                  ((output, globalCausalRevealResultState secretKey input state
                    index value output),
                    [RevealProbeOracleSimulation.ObservedAction.reveal
                      index value])] := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro base
              simp_rw [globalCausalAttackerHashQuery_run, hplan]
              unfold globalCausalRevealHashQuery
              rw [RevealProbeOracleSimulation.simulate_eagerTrace_reveal_then_liftProbComp]
              simp [globalCausalInstalledTable_of_revealed
                state base index value hrevealed, map_eq_bind_pure_comp]
            _ = _ := by
              rw [OracleComp.DeferredSampling.evalDist_bind_comm]
              simp [bind_assoc]
      | none =>
          simp only [globalCausalLazyAttackerHashStep, hplan, hrevealed,
            pure_bind]
          calc
            _ = 𝒟[do
                let base ← $ᵗ (GlobalChainValueIndex → Digest)
                let output ← Rom.sampleHashOutputWithDigest (base index)
                let value := base index
                globalCausalInstalledRevealContinuation secretKey input state
                  index continuation base value output] := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro base
              simp_rw [globalCausalAttackerHashQuery_run, hplan]
              unfold globalCausalRevealHashQuery
              rw [RevealProbeOracleSimulation.simulate_eagerTrace_reveal_then_liftProbComp]
              simp [globalCausalInstalledTable_of_not_revealed
                state base index hrevealed,
                globalCausalInstalledRevealContinuation,
                map_eq_bind_pure_comp]
            _ = 𝒟[globalCausalProgrammedRevealContinuation
                secretKey input state index continuation] := by
              unfold globalCausalProgrammedRevealContinuation
              exact
                (RevealProbeOracleSimulation.evalDist_uniformTable_bind_programmedCoordinate_continuation
                  index (globalCausalInstalledRevealContinuation
                    secretKey input state index continuation))
            _ = 𝒟[globalCausalFreshBaseRevealContinuation
                secretKey input state index continuation] :=
              evalDist_globalCausalProgrammedRevealContinuation_eq_freshBase
                secretKey input state index continuation
            _ = _ := by
              unfold globalCausalFreshBaseRevealContinuation
              simp [globalCausalInstalledRevealContinuation, bind_assoc]

def globalPrependRevealTrace
    (index : GlobalChainValueIndex) (value : Digest)
    (result : (Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    (Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  (result.1,
    RevealProbeOracleSimulation.ObservedAction.reveal index value :: result.2)

theorem simulate_eagerTrace_revealGlobalSignatureChains_cons
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chain : ChainIndex) (chains : List ChainIndex)
    (signature : Signature) (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((revealGlobalSignatureChains request encoding (chain :: chains)
        signature).run state)).run =
      globalPrependRevealTrace
        (chain, request.epoch, encoding chain)
        (table (chain, request.epoch, encoding chain)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((revealGlobalSignatureChains request encoding chains
            (replaceSignatureChainValue signature chain
              (table (chain, request.epoch, encoding chain)))).run
            (state.recordReveal (chain, request.epoch, encoding chain)
              (table (chain, request.epoch, encoding chain))))).run := by
  rw [revealGlobalSignatureChains]
  change (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table) (do
      let value ← RevealProbeOracleSimulation.revealQuery
        (chain, request.epoch, encoding chain)
      (revealGlobalSignatureChains request encoding chains
        (replaceSignatureChainValue signature chain value)).run
          (state.recordReveal
            (chain, request.epoch, encoding chain) value))).run = _
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_revealQuery]
  simp only [pure_bind, map_eq_bind_pure_comp]
  apply bind_congr
  intro result
  rfl

noncomputable def globalCausalLazyRevealSignatureChains
    (request : SignRequest) (encoding : ChainIndex → Digit) :
    List ChainIndex → Signature → GlobalCausalHashState →
      ProbComp ((Signature × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
  | [], signature, state => pure ((signature, state), [])
  | chain :: chains, signature, state =>
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      match state.revealed index with
      | some value => do
          let tail ← globalCausalLazyRevealSignatureChains request encoding
            chains (replaceSignatureChainValue signature chain value)
              (state.recordReveal index value)
          pure (globalPrependRevealTrace index value tail)
      | none => do
          let value ← $ᵗ Digest
          let tail ← globalCausalLazyRevealSignatureChains request encoding
            chains (replaceSignatureChainValue signature chain value)
              (state.recordReveal index value)
          pure (globalPrependRevealTrace index value tail)

def globalPrependRevealContinuation
    (index : GlobalChainValueIndex) (value : Digest)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((Signature × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α)
    (table : GlobalChainValueIndex → Digest)
    (result : (Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : ProbComp α :=
  continuation table (globalPrependRevealTrace index value result)

theorem globalSignatureRevealResult_installedInvariant
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState)
    (hagrees : GlobalCausalRevealsAgree table state) :
    GlobalCausalRevealsAgree table
        (globalSignatureRevealResult table request encoding chains
          signature state).2 ∧
      GlobalCausalRevealsLe state
        (globalSignatureRevealResult table request encoding chains
          signature state).2 := by
  induction chains generalizing signature state with
  | nil => exact ⟨hagrees, GlobalCausalRevealsLe.refl state⟩
  | cons chain chains ih =>
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      let value := table index
      have hcompatible : ∀ previous,
          state.revealed index = some previous → previous = value := by
        intro previous hprevious
        exact (hagrees index previous hprevious).symm
      have hstep : GlobalCausalRevealsLe state
          (state.recordReveal index value) :=
        GlobalCausalRevealsLe.recordReveal state index value hcompatible
      have hagrees' : GlobalCausalRevealsAgree table
          (state.recordReveal index value) :=
        hagrees.recordReveal index value rfl
      have htail := ih
        (replaceSignatureChainValue signature chain value)
        (state.recordReveal index value) hagrees'
      rw [globalSignatureRevealResult]
      exact ⟨htail.1, hstep.trans htail.2⟩

set_option maxRecDepth 200000 in
theorem evalDist_installed_revealGlobalSignatureChains_continuation_eq_lazy
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((Signature × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let table := globalCausalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((revealGlobalSignatureChains request encoding chains signature).run
          state)).run
      continuation (globalCausalInstalledTable result.1.2 base) result] =
    𝒟[do
      let result ← globalCausalLazyRevealSignatureChains
        request encoding chains signature state
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      continuation (globalCausalInstalledTable result.1.2 base) result] := by
  induction chains generalizing signature state continuation with
  | nil =>
      simp [revealGlobalSignatureChains,
        globalCausalLazyRevealSignatureChains,
        RevealProbeOracleSimulation.eagerTraceImpl]
  | cons chain chains ih =>
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      cases hrevealed : state.revealed index with
      | some value =>
          have hrevealed' : state.revealed
              (chain, request.epoch, encoding chain) = some value := by
            simpa [index] using hrevealed
          simp only [globalCausalLazyRevealSignatureChains, hrevealed',
            bind_assoc]
          calc
            _ = 𝒟[do
                let base ← $ᵗ (GlobalChainValueIndex → Digest)
                let result ← (simulateQ
                  (RevealProbeOracleSimulation.eagerTraceImpl
                    (globalCausalInstalledTable
                      (state.recordReveal index value) base))
                  ((revealGlobalSignatureChains request encoding chains
                    (replaceSignatureChainValue signature chain value)).run
                      (state.recordReveal index value))).run
                globalPrependRevealContinuation index value continuation
                  (globalCausalInstalledTable result.1.2 base) result] := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro base
              rw [simulate_eagerTrace_revealGlobalSignatureChains_cons,
                globalCausalInstalledTable_of_revealed
                  state base index value hrevealed]
              have htable : globalCausalInstalledTable
                  (state.recordReveal index value) base =
                    globalCausalInstalledTable state base := by
                rw [globalCausalInstalledTable_recordReveal]
                rw [← globalCausalInstalledTable_of_revealed
                  state base index value hrevealed]
                exact Function.update_eq_self index
                  (globalCausalInstalledTable state base)
              rw [← htable]
              simp [globalPrependRevealContinuation,
                globalPrependRevealTrace, map_eq_bind_pure_comp, index]
            _ = 𝒟[do
                let result ← globalCausalLazyRevealSignatureChains
                  request encoding chains
                    (replaceSignatureChainValue signature chain value)
                      (state.recordReveal index value)
                let base ← $ᵗ (GlobalChainValueIndex → Digest)
                globalPrependRevealContinuation index value continuation
                  (globalCausalInstalledTable result.1.2 base) result] :=
              ih (replaceSignatureChainValue signature chain value)
                (state.recordReveal index value)
                (globalPrependRevealContinuation index value continuation)
            _ = _ := by
              simp [globalPrependRevealContinuation,
                globalPrependRevealTrace, bind_assoc, index]
      | none =>
          have hrevealed' : state.revealed
              (chain, request.epoch, encoding chain) = none := by
            simpa [index] using hrevealed
          simp only [globalCausalLazyRevealSignatureChains, hrevealed',
            bind_assoc]
          calc
            _ = 𝒟[do
                let base ← $ᵗ (GlobalChainValueIndex → Digest)
                let value := base index
                let result ← (simulateQ
                  (RevealProbeOracleSimulation.eagerTraceImpl
                    (globalCausalInstalledTable
                      (state.recordReveal index value) base))
                  ((revealGlobalSignatureChains request encoding chains
                    (replaceSignatureChainValue signature chain value)).run
                      (state.recordReveal index value))).run
                globalPrependRevealContinuation index value continuation
                  (globalCausalInstalledTable result.1.2 base) result] := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro base
              rw [simulate_eagerTrace_revealGlobalSignatureChains_cons,
                globalCausalInstalledTable_of_not_revealed
                  state base index hrevealed]
              have htable : globalCausalInstalledTable
                  (state.recordReveal index (base index)) base =
                    globalCausalInstalledTable state base := by
                rw [globalCausalInstalledTable_recordReveal]
                rw [← globalCausalInstalledTable_of_not_revealed
                  state base index hrevealed]
                exact Function.update_eq_self index
                  (globalCausalInstalledTable state base)
              rw [← htable]
              simp [
                globalPrependRevealContinuation,
                globalPrependRevealTrace, map_eq_bind_pure_comp, index]
            _ = 𝒟[do
                let value ← $ᵗ Digest
                let base ← $ᵗ (GlobalChainValueIndex → Digest)
                let result ← (simulateQ
                  (RevealProbeOracleSimulation.eagerTraceImpl
                    (globalCausalInstalledTable
                      (state.recordReveal index value)
                        (Function.update base index value)))
                  ((revealGlobalSignatureChains request encoding chains
                    (replaceSignatureChainValue signature chain value)).run
                      (state.recordReveal index value))).run
                globalPrependRevealContinuation index value continuation
                  (globalCausalInstalledTable result.1.2
                    (Function.update base index value)) result] := by
              exact
                RevealProbeOracleSimulation.evalDist_uniformTable_bind_coordinate_continuation
                  index (fun base value => do
                    let result ← (simulateQ
                      (RevealProbeOracleSimulation.eagerTraceImpl
                        (globalCausalInstalledTable
                          (state.recordReveal index value) base))
                      ((revealGlobalSignatureChains request encoding chains
                        (replaceSignatureChainValue signature chain value)).run
                          (state.recordReveal index value))).run
                    globalPrependRevealContinuation index value continuation
                      (globalCausalInstalledTable result.1.2 base) result)
            _ = 𝒟[do
                let value ← $ᵗ Digest
                let base ← $ᵗ (GlobalChainValueIndex → Digest)
                let result ← (simulateQ
                  (RevealProbeOracleSimulation.eagerTraceImpl
                    (globalCausalInstalledTable
                      (state.recordReveal index value) base))
                  ((revealGlobalSignatureChains request encoding chains
                    (replaceSignatureChainValue signature chain value)).run
                      (state.recordReveal index value))).run
                globalPrependRevealContinuation index value continuation
                  (globalCausalInstalledTable result.1.2 base) result] := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro value
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro base
              have hinitial : globalCausalInstalledTable
                  (state.recordReveal index value)
                    (Function.update base index value) =
                globalCausalInstalledTable
                  (state.recordReveal index value) base :=
                globalCausalInstalledTable_update_base_of_revealed
                  (state.recordReveal index value) base index value value
                    (by simp [GlobalCausalHashState.recordReveal])
              rw [hinitial]
              rw [simulate_eagerTrace_revealGlobalSignatureChains]
              simp only [pure_bind]
              let table := globalCausalInstalledTable
                (state.recordReveal index value) base
              have hinvariant :=
                globalSignatureRevealResult_installedInvariant table request
                  encoding chains
                    (replaceSignatureChainValue signature chain value)
                      (state.recordReveal index value)
                        (globalCausalRevealsAgree_globalCausalInstalledTable
                          (state.recordReveal index value) base)
              have hfinal :
                  (globalSignatureRevealResult table request encoding chains
                    (replaceSignatureChainValue signature chain value)
                      (state.recordReveal index value)).2.revealed index =
                    some value :=
                hinvariant.2 index value
                  (by simp [GlobalCausalHashState.recordReveal])
              rw [globalCausalInstalledTable_update_base_of_revealed
                _ base index value value hfinal]
            _ = 𝒟[do
                let value ← $ᵗ Digest
                let result ← globalCausalLazyRevealSignatureChains
                  request encoding chains
                    (replaceSignatureChainValue signature chain value)
                      (state.recordReveal index value)
                let base ← $ᵗ (GlobalChainValueIndex → Digest)
                globalPrependRevealContinuation index value continuation
                  (globalCausalInstalledTable result.1.2 base) result] := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro value
              exact ih (replaceSignatureChainValue signature chain value)
                (state.recordReveal index value)
                (globalPrependRevealContinuation index value continuation)
            _ = _ := by
              simp [globalPrependRevealContinuation,
                globalPrependRevealTrace, bind_assoc, index]

def globalAttachSomeSignature
    (result : (Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  ((some result.1.1, result.1.2), result.2)

noncomputable def globalCausalLazyRevealSignatureOption
    (secretKey : SecretKey) (request : SignRequest)
    (signatureOption : Option Signature) (state : GlobalCausalHashState) :
    ProbComp ((Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  match signatureOption with
  | none => pure ((none, state), [])
  | some signature =>
      match TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash state.cache secretKey.parameter
            request.epoch (request.message, signature.randomness)) with
      | none => pure ((some signature, state), [])
      | some encoding =>
          globalAttachSomeSignature <$>
            globalCausalLazyRevealSignatureChains request encoding allChains
              signature state

def globalAttachSomeSignatureContinuation
    (continuation : (GlobalChainValueIndex → Digest) →
      ((Option Signature × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α)
    (table : GlobalChainValueIndex → Digest)
    (result : (Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : ProbComp α :=
  continuation table (globalAttachSomeSignature result)

set_option maxRecDepth 200000 in
theorem evalDist_installed_revealGlobalSignatureOption_continuation_eq_lazy
    (secretKey : SecretKey) (request : SignRequest)
    (signatureOption : Option Signature) (state : GlobalCausalHashState)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((Option Signature × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let table := globalCausalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((revealGlobalSignatureOption secretKey request signatureOption).run
          state)).run
      continuation (globalCausalInstalledTable result.1.2 base) result] =
    𝒟[do
      let result ← globalCausalLazyRevealSignatureOption
        secretKey request signatureOption state
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      continuation (globalCausalInstalledTable result.1.2 base) result] := by
  cases signatureOption with
  | none =>
      simp [globalCausalLazyRevealSignatureOption,
        revealGlobalSignatureOption_run,
        RevealProbeOracleSimulation.eagerTraceImpl]
  | some signature =>
      cases hdecode : TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash state.cache secretKey.parameter
            request.epoch (request.message, signature.randomness)) with
      | none =>
          simp [globalCausalLazyRevealSignatureOption,
            revealGlobalSignatureOption_run, hdecode,
            RevealProbeOracleSimulation.eagerTraceImpl]
      | some encoding =>
          let attached := globalAttachSomeSignatureContinuation continuation
          have hchains :=
            evalDist_installed_revealGlobalSignatureChains_continuation_eq_lazy
              request encoding allChains signature state attached
          simpa [globalCausalLazyRevealSignatureOption,
            revealGlobalSignatureOption_run, hdecode,
            globalAttachSomeSignatureContinuation,
            globalAttachSomeSignature, attached,
            map_eq_bind_pure_comp, bind_assoc] using hchains

noncomputable def globalCausalLazySigningQuery
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (state : GlobalCausalHashState) :
    ProbComp ((Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) := do
  let signed ← (simulateQ xmssRomImpl
    (Concrete.cappedScheme.sign publicKey secretKey request.epoch request.message)).run
      state.cache
  globalCausalLazyRevealSignatureOption secretKey request signed.1
    { state with cache := signed.2 }

set_option maxRecDepth 200000 in
theorem evalDist_installed_globalCausalSigningQueryAfterRealRom_continuation_eq_lazy
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (state : GlobalCausalHashState)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((Option Signature × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let table := globalCausalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalCausalSigningQueryAfterRealRom
          publicKey secretKey request state)).run
      continuation (globalCausalInstalledTable result.1.2 base) result] =
    𝒟[do
      let result ← globalCausalLazySigningQuery
        publicKey secretKey request state
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      continuation (globalCausalInstalledTable result.1.2 base) result] := by
  unfold globalCausalLazySigningQuery
  calc
    _ = 𝒟[do
        let base ← $ᵗ (GlobalChainValueIndex → Digest)
        let signed ← (simulateQ xmssRomImpl
          (Concrete.cappedScheme.sign publicKey secretKey request.epoch
            request.message)).run state.cache
        let signedState := { state with cache := signed.2 }
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl
            (globalCausalInstalledTable signedState base))
          ((revealGlobalSignatureOption secretKey request signed.1).run
            signedState)).run
        continuation (globalCausalInstalledTable result.1.2 base) result] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      simp_rw [simulate_eagerTrace_globalCausalSigningQueryAfterRealRom]
      simp [globalCausalInstalledTable_setCache, bind_assoc]
    _ = 𝒟[do
        let signed ← (simulateQ xmssRomImpl
          (Concrete.cappedScheme.sign publicKey secretKey request.epoch
            request.message)).run state.cache
        let base ← $ᵗ (GlobalChainValueIndex → Digest)
        let signedState := { state with cache := signed.2 }
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl
            (globalCausalInstalledTable signedState base))
          ((revealGlobalSignatureOption secretKey request signed.1).run
            signedState)).run
        continuation (globalCausalInstalledTable result.1.2 base) result] :=
      OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = _ := by
      simp only [bind_assoc]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro signed
      exact
        evalDist_installed_revealGlobalSignatureOption_continuation_eq_lazy
          secretKey request signed.1 { state with cache := signed.2 }
            continuation

end XmssSecurity.CappedChain
