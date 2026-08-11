import XmssSecurity.ChainEventDecomposition
import XmssSecurity.PrefixTarget
import XmssSecurity.WinningEventReduction

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

noncomputable def WinningOutcomeGuessesKeygenChainValue
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) (chain : ChainIndex) : Prop :=
  WinningOutcomeBadEventOccurs finalCache outcome (.chain chain) ∧
    OutcomeGuessesKeygenChainValue keygenCache finalCache secretKey outcome chain

/-- Retaining the winning chain witness prevents the hidden-value event from including trivial replays of an honestly returned signature. -/
theorem winningChainValueRevealed_probability_le_winningKeygenValueGuess
    (adversary : Adversary Concrete.scheme) (chain : ChainIndex) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 (.chain chain) ∧
        OutcomeChainValueRevealed execution.2 execution.1 chain |
      detailedGameWithCache Concrete.scheme adversary] ≤
      Pr[fun result =>
        WinningOutcomeGuessesKeygenChainValue result.1.2 result.2.2 result.1.1.2
          result.2.1 chain |
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
  exact ⟨hevent.1,
    chainValueRevealed_afterKeygen_guesses_keygenValue adversary keyResult hkeygen
      execution hafter chain hevent.2⟩

/-- A winning chain event either reveals the honest key-generation value while retaining its freshness witness, or creates one adaptive fresh collision after key generation. -/
theorem winning_chain_outcomeBadEvent_probability_le_revealed_add
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) (chain : ChainIndex) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 (.chain chain) |
      detailedGameWithCache Concrete.scheme adversary] ≤
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        WinningOutcomeBadEventOccurs execution.2 execution.1 (.chain chain) ∧
          OutcomeChainValueRevealed execution.2 execution.1 chain |
        detailedGameWithCache Concrete.scheme adversary] +
        (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  let bad := fun execution : GameOutcome × QueryCache HashSpec =>
    WinningOutcomeBadEventOccurs execution.2 execution.1 (.chain chain)
  let revealed := fun execution : GameOutcome × QueryCache HashSpec =>
    OutcomeChainValueRevealed execution.2 execution.1 chain
  let remainder := fun execution : GameOutcome × QueryCache HashSpec =>
    bad execution ∧ ¬revealed execution
  have hdetailedBound :
      (detailedGameCore Concrete.scheme adversary).IsQueryBoundP
        (· matches .inr _) q :=
    (hasHashQueryBound_iff_detailedGameCore Concrete.scheme adversary q).mp hbound
  have hcollision :
      Pr[remainder | detailedGameWithCache Concrete.scheme adversary] ≤
        (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
    unfold detailedGameWithCache detailedGameCore
    apply Rom.mixed_adaptiveFreshDigestCollision_after_prefix_le
      Concrete.scheme.keygen
      (fun key => detailedGameAfterKeygen Concrete.scheme adversary key.1 key.2)
      q hdetailedBound ∅
      (fun key keyCache => keygenChainTargetInput key.2 keyCache)
      remainder
    intro keyResult hkeygen execution hafter hrest
    rcases chain_event_afterKeygen_revealed_or_collision adversary keyResult hkeygen
        execution hafter chain hrest.1.2 with hrevealed | hcollision
    · exact (hrest.2 hrevealed).elim
    · exact hcollision
  calc
    Pr[bad | detailedGameWithCache Concrete.scheme adversary] ≤
        Pr[fun execution =>
          (bad execution ∧ revealed execution) ∨ remainder execution |
          detailedGameWithCache Concrete.scheme adversary] := by
      apply probEvent_mono''
      intro execution hbad
      by_cases hreveal : revealed execution
      · exact Or.inl ⟨hbad, hreveal⟩
      · exact Or.inr ⟨hbad, hreveal⟩
    _ ≤ Pr[fun execution => bad execution ∧ revealed execution |
          detailedGameWithCache Concrete.scheme adversary] +
        Pr[remainder | detailedGameWithCache Concrete.scheme adversary] :=
      probEvent_or_le _ _ _
    _ ≤ Pr[fun execution => bad execution ∧ revealed execution |
          detailedGameWithCache Concrete.scheme adversary] +
        (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
      exact add_le_add_right hcollision _

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
