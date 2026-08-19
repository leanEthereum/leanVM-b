import XmssSecurity.Proof.CappedEncodingEventProbability
import XmssSecurity.Proof.CappedUnifiedStructuralCollision

open OracleComp OracleSpec

namespace XmssSecurity

def WinningEncodingEventOccurs
    (cache : QueryCache HashSpec) (outcome : GameOutcome) : Prop :=
  WinningGlobalBadEventOccurs cache outcome .encoding

def WinningUnifiedBadEventOccurs
    (cache : QueryCache HashSpec) (outcome : GameOutcome) : Prop :=
  WinningEncodingEventOccurs cache outcome ∨
    GlobalWinningChainValueRevealed cache outcome ∨
      WinningStructuralCollisionOccurs cache outcome

theorem winning_outcome_has_unifiedBadEvent
    (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (hconsistent : ConcreteOutcomeConsistent cache outcome)
    (hwin : outcome.won = true) :
    WinningUnifiedBadEventOccurs cache outcome := by
  obtain ⟨event, hevent⟩ :=
    winning_outcome_has_globalBadEvent cache outcome hconsistent hwin
  cases event with
  | encoding => exact Or.inl hevent
  | chain =>
      by_cases hrevealed : GlobalWinningChainValueRevealed cache outcome
      · exact Or.inr (Or.inl hrevealed)
      · exact Or.inr (Or.inr (Or.inl ⟨hevent, hrevealed⟩))
  | suffixCollision =>
      exact Or.inr (Or.inr (Or.inr (Or.inl hevent)))
  | leaf =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hevent))))
  | merkle =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hevent))))

end XmssSecurity
