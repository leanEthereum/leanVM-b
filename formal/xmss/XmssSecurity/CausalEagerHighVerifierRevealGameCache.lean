import XmssSecurity.CausalEagerHighVerifierRevealScheme

open OracleComp OracleSpec

namespace XmssSecurity

set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000000 in
theorem filteredHighDetailedGameAfterKeygen_support_cache_le
    (table : ChainValueIndex → Digest)
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (state : CausalHashState)
    (result : ((((Forgery × Bool) × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : FilteredHighDetailedRunSupport table adversary keyHigh selected
      state result) :
    state.cache ≤ result.1.2.cache := by
  obtain ⟨handled, verifier, hhandled, hverifier, rfl⟩ :=
    filteredHighDetailedRunSupport_decompose table adversary keyHigh selected
      state result hresult
  rcases handled with
    ⟨⟨⟨forgery, attackerTrace⟩, handledState⟩, handledTrace⟩
  unfold FilteredHighRunSupport EagerTraceSupport at hhandled
  unfold EagerTraceSupport at hverifier
  dsimp only at hhandled hverifier ⊢
  have hhandledCache := simulate_filteredHighActionTraced_support_cache_le
    table keyHigh selected (adversary.main keyHigh.1.publicKey) state
      (((forgery, attackerTrace), handledState), handledTrace) hhandled
  have hverifierCache : handledState.cache ≤ verifier.1.2.cache := by
    apply filteredHighVerifier_support_scheme_cache_le
      (table := table) (keyHigh := keyHigh) (selected := selected)
      (publicKey := keyHigh.1.publicKey) (epoch := forgery.epoch)
      (message := forgery.message) (signature := forgery.signature)
      (state := handledState) (result := verifier)
    generalize (Concrete.singleAttemptScheme.verify keyHigh.1.publicKey forgery.epoch
      forgery.message forgery.signature : OracleComp OracleWorld Bool) =
        computation at hverifier ⊢
    exact hverifier
  exact hhandledCache.trans hverifierCache

end XmssSecurity
