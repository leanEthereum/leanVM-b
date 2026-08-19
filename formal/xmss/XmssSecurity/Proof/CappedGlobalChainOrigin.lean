import XmssSecurity.Proof.CappedGlobalCollisionProbability

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable def GlobalWinningOutcomeGuessesKeygenChainValue
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) : Prop :=
  ∃ chain, WinningOutcomeGuessesKeygenChainValue keygenCache finalCache
    secretKey outcome chain

noncomputable def GlobalWinningOutcomeChainValueHasKeygenOrigin
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) : Prop :=
  ∃ chain, WinningOutcomeChainValueHasKeygenOrigin keygenCache finalCache
    secretKey outcome chain

theorem globalWinningChainValueRevealed_probability_le_globalKeygenValueGuess
    (adversary : Adversary Concrete.scheme) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      GlobalWinningChainValueRevealed execution.2 execution.1 |
      detailedGameWithCache Concrete.scheme adversary] ≤
    Pr[fun result =>
      GlobalWinningOutcomeGuessesKeygenChainValue result.1.2 result.2.2
        result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] := by
  rw [detailedGameWithCache_eq_map_detailedGameWithKeygenCache, probEvent_map]
  apply probEvent_mono
  intro result hresult hevent
  unfold detailedGameWithKeygenCache at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, hkeygen, hcontinuation⟩ := hresult
  rw [support_map] at hcontinuation
  obtain ⟨execution, hafter, heq⟩ := hcontinuation
  subst result
  obtain ⟨chain, hwinning, hrevealed⟩ := hevent
  exact ⟨chain, hwinning,
    chainValueRevealed_afterKeygen_guesses_keygenValue adversary keyResult
      hkeygen execution hafter chain hrevealed⟩

theorem globalWinningKeygenValueGuess_probability_le_origin
    (adversary : Adversary Concrete.scheme) :
    Pr[fun result =>
      GlobalWinningOutcomeGuessesKeygenChainValue result.1.2 result.2.2
        result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
    Pr[fun result =>
      GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] := by
  apply probEvent_mono
  intro result hresult hevent
  unfold detailedGameWithKeygenCache at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, hkeygen, hcontinuation⟩ := hresult
  rw [support_map] at hcontinuation
  obtain ⟨execution, _hafter, heq⟩ := hcontinuation
  subst result
  obtain ⟨chain, hguess⟩ := hevent
  exact ⟨chain,
    winningKeygenValueGuess_has_origin keyResult hkeygen execution chain hguess⟩

end XmssSecurity.CappedChain
