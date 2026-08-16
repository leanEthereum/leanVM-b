import XmssSecurity.CausalEagerHighVerifierRevealGameCache

open OracleComp OracleSpec

namespace XmssSecurity

set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 2000000 in
theorem filteredHighDetailedGameAfterKeygen_support_resultCovered_of_final
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.scheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (state : CausalHashState)
    (covered : Set ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (result : ((((Forgery × Bool) × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hdirect : ∀ request signature encoding,
      AttackerAction.sign request (some signature) ∈ result.1.1.2 →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash result.1.2.cache
          keyHigh.1.secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding →
      (request.epoch, encoding selected) ∈ covered)
    (hresult : FilteredHighDetailedRunSupport table adversary keyHigh selected
      state result) :
    CausalResultCovered covered result := by
  obtain ⟨handled, verifier, hhandled, hverifier, rfl⟩ :=
    filteredHighDetailedRunSupport_decompose table adversary keyHigh selected
      state result hresult
  rcases handled with
    ⟨⟨⟨forgery, attackerTrace⟩, handledState⟩, handledTrace⟩
  unfold FilteredHighRunSupport EagerTraceSupport at hhandled
  unfold EagerTraceSupport at hverifier
  dsimp only at hhandled hverifier hdirect ⊢
  have hhandledCacheLe : handledState.cache ≤ verifier.1.2.cache :=
    by
      apply filteredHighVerifier_support_scheme_cache_le
        (table := table) (keyHigh := keyHigh) (selected := selected)
        (publicKey := keyHigh.1.publicKey) (epoch := forgery.epoch)
        (message := forgery.message) (signature := forgery.signature)
        (state := handledState) (result := verifier)
      generalize (Concrete.scheme.verify keyHigh.1.publicKey forgery.epoch
        forgery.message forgery.signature : OracleComp OracleWorld Bool) =
          computation at hverifier ⊢
      exact hverifier
  have hhandledCovered :=
    simulate_filteredHighActionTraced_support_resultCovered_of_final table
      keyHigh selected (adversary.main keyHigh.1.publicKey) state covered
        verifier.1.2.cache attackerTrace hcovered hforward
        (fun request signature encoding haction hdecode =>
          hdirect request signature encoding haction hdecode)
        (((forgery, attackerTrace), handledState), handledTrace) hhandled
          hhandledCacheLe (fun action haction => haction)
  have hverifierCovered : CausalResultCovered covered verifier := by
    apply filteredHighVerifier_support_scheme_resultCovered
      (table := table) (keyHigh := keyHigh) (selected := selected)
      (publicKey := keyHigh.1.publicKey) (epoch := forgery.epoch)
      (message := forgery.message) (signature := forgery.signature)
      (state := handledState) (covered := covered)
      (hcovered := hhandledCovered.1) (hforward := hforward)
      (result := verifier)
    generalize (Concrete.scheme.verify keyHigh.1.publicKey forgery.epoch
      forgery.message forgery.signature : OracleComp OracleWorld Bool) =
        computation at hverifier ⊢
    exact hverifier
  exact ⟨hverifierCovered.1,
    hhandledCovered.2.append hverifierCovered.2⟩

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 2000000 in
theorem filteredHighDetailedGameAfterKeygen_support_returnedCovered
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.scheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (state : CausalHashState)
    (hinitial : ∀ index, state.revealed index = none)
    (result : ((((Forgery × Bool) × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighDetailedRunSupport table adversary keyHigh selected
      state result) :
    CausalResultCovered
      (ReturnedChainValueCovered result.1.2.cache keyHigh.1.secretKey
        result.1.1.2.toSigningLog selected) result := by
  apply filteredHighDetailedGameAfterKeygen_support_resultCovered_of_final
    table adversary keyHigh selected state
      (ReturnedChainValueCovered result.1.2.cache keyHigh.1.secretKey
        result.1.1.2.toSigningLog selected)
  · intro index value hrevealed
    rw [hinitial index] at hrevealed
    cases hrevealed
  · exact returnedChainValueCovered_forwardClosed result.1.2.cache
      keyHigh.1.secretKey result.1.1.2.toSigningLog selected
  · intro request signature encoding haction hdecode
    exact returnedChainValueCovered_contains_returned result.1.2.cache
      keyHigh.1.secretKey result.1.1.2.toSigningLog selected request signature
        encoding
        (result.1.1.2.sign_mem_toSigningLog request signature haction) hdecode
  · exact hresult

set_option maxHeartbeats 1000000 in
theorem filteredHighMonitoredDetailedExecution_support_returnedCovered
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.scheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (result : (Forgery × Bool) × MonitoredTracedState)
    (hresult : result ∈ support
      (filteredHighMonitoredDetailedExecution adversary keyHigh selected
        table)) :
    CausalResultCovered
      (ReturnedChainValueCovered result.2.1.causal.cache keyHigh.1.secretKey
        result.2.2.toSigningLog selected)
      (((((result.1, result.2.2), result.2.1.causal)),
        result.2.1.trace)) := by
  let projected :=
    ((((result.1, result.2.2), result.2.1.causal), result.2.1.trace))
  have hprojected : FilteredHighDetailedRunSupport table adversary keyHigh
      selected (filteredCausalKeygenState selected keyHigh.1) projected :=
    filteredHighMonitoredDetailedExecution_support_action_projection table
      adversary keyHigh selected result hresult
  simpa [projected] using
    (filteredHighDetailedGameAfterKeygen_support_returnedCovered table
      adversary keyHigh selected
        (filteredCausalKeygenState selected keyHigh.1)
          (filteredCausalKeygenState_revealed selected keyHigh.1) projected
            hprojected)

end XmssSecurity
