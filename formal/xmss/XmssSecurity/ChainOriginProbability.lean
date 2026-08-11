import XmssSecurity.ChainEventDecomposition

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable def detailedGameWithKeygenCache (adversary : Adversary Concrete.scheme) :
    ProbComp (((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) :=
  (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅ >>= fun keyResult =>
    (fun execution => (keyResult, execution)) <$>
      (simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2

theorem detailedGameWithCache_eq_map_detailedGameWithKeygenCache
    (adversary : Adversary Concrete.scheme) :
    detailedGameWithCache Concrete.scheme adversary =
      Prod.snd <$> detailedGameWithKeygenCache adversary := by
  unfold detailedGameWithCache detailedGameCore detailedGameWithKeygenCache
  rw [simulateQ_bind, StateT.run_bind]
  simp

theorem chainValueRevealed_probability_le_keygenValueGuess
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      OutcomeChainValueRevealed execution.2 execution.1 chain |
      detailedGameWithCache Concrete.scheme adversary] ≤
      Pr[fun result =>
        OutcomeGuessesKeygenChainValue result.1.2 result.2.2 result.1.1.2
          result.2.1 chain |
        detailedGameWithKeygenCache adversary] := by
  rw [detailedGameWithCache_eq_map_detailedGameWithKeygenCache, probEvent_map]
  apply probEvent_mono
  intro result hresult hrevealed
  unfold detailedGameWithKeygenCache at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, hkeygen, hcontinuation⟩ := hresult
  rw [support_map] at hcontinuation
  obtain ⟨execution, hafter, heq⟩ := hcontinuation
  subst result
  exact chainValueRevealed_afterKeygen_guesses_keygenValue adversary keyResult hkeygen
    execution hafter chain hrevealed

theorem chainValueRevealed_probability_le_keygenOrigin
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      OutcomeChainValueRevealed execution.2 execution.1 chain |
      detailedGameWithCache Concrete.scheme adversary] ≤
      Pr[fun result =>
        OutcomeChainValueHasKeygenOrigin result.1.2 result.2.2 result.1.1.2
          result.2.1 chain |
        detailedGameWithKeygenCache adversary] := by
  rw [detailedGameWithCache_eq_map_detailedGameWithKeygenCache, probEvent_map]
  apply probEvent_mono
  intro result hresult hrevealed
  unfold detailedGameWithKeygenCache at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, hkeygen, hcontinuation⟩ := hresult
  rw [support_map] at hcontinuation
  obtain ⟨execution, hafter, heq⟩ := hcontinuation
  subst result
  exact chainValueRevealed_afterKeygen_has_origin adversary keyResult hkeygen execution
    hafter chain hrevealed

end XmssSecurity
