import XmssSecurity.CappedSigningLogReplay

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-- The five cryptographic failure mechanisms, without coordinate indices. -/
inductive GlobalBadEvent where
  | encoding
  | chain
  | suffixCollision
  | leaf
  | merkle
deriving DecidableEq, Fintype

def GlobalOutcomeBadEventOccurs
    (cache : QueryCache HashSpec) (outcome : GameOutcome) :
    GlobalBadEvent → Prop
  | .encoding => OutcomeBadEventOccurs cache outcome .encoding
  | .chain => ∃ chain, OutcomeBadEventOccurs cache outcome (.chain chain)
  | .suffixCollision =>
      ∃ slot, OutcomeBadEventOccurs cache outcome (.suffixCollision slot)
  | .leaf => OutcomeBadEventOccurs cache outcome .leaf
  | .merkle => ∃ level, OutcomeBadEventOccurs cache outcome (.merkle level)

def WinningGlobalBadEventOccurs
    (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (event : GlobalBadEvent) : Prop :=
  outcome.won = true ∧ GlobalOutcomeBadEventOccurs cache outcome event

theorem outcomeBadEventOccurs_implies_global
    {cache : QueryCache HashSpec} {outcome : GameOutcome} {event : BadEvent}
    (hevent : OutcomeBadEventOccurs cache outcome event) :
    ∃ globalEvent, GlobalOutcomeBadEventOccurs cache outcome globalEvent := by
  cases event with
  | encoding => exact ⟨.encoding, hevent⟩
  | chain chain => exact ⟨.chain, chain, hevent⟩
  | suffixCollision slot => exact ⟨.suffixCollision, slot, hevent⟩
  | leaf => exact ⟨.leaf, hevent⟩
  | merkle level => exact ⟨.merkle, level, hevent⟩

theorem winning_outcome_has_globalBadEvent
    (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (hconsistent : ConcreteOutcomeConsistent cache outcome)
    (hwin : outcome.won = true) :
    ∃ event, WinningGlobalBadEventOccurs cache outcome event := by
  obtain ⟨event, hevent⟩ :=
    winning_outcome_has_badEvent cache outcome hconsistent hwin
  obtain ⟨globalEvent, hglobal⟩ :=
    outcomeBadEventOccurs_implies_global hevent
  exact ⟨globalEvent, hwin, hglobal⟩

theorem capped_forgeAdvantage_le_winningGlobalBadEvent_sum
    (adversary : Adversary Concrete.scheme) :
    forgeAdvantage Concrete.scheme adversary ≤
      ∑ event, Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        WinningGlobalBadEventOccurs execution.2 execution.1 event |
        detailedGameWithCache Concrete.scheme adversary] := by
  rw [forgeAdvantage_eq_detailedGameWithCache]
  calc
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true |
        detailedGameWithCache Concrete.scheme adversary] ≤
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        ∃ event : GlobalBadEvent,
          WinningGlobalBadEventOccurs execution.2 execution.1 event |
        detailedGameWithCache Concrete.scheme adversary] := by
      apply probEvent_mono
      intro execution hmem hwin
      exact winning_outcome_has_globalBadEvent execution.2 execution.1
        (capped_detailed_execution_consistent adversary execution hmem) hwin
    _ ≤ ∑ event : GlobalBadEvent,
        Pr[fun execution : GameOutcome × QueryCache HashSpec =>
          WinningGlobalBadEventOccurs execution.2 execution.1 event |
          detailedGameWithCache Concrete.scheme adversary] := by
      simpa only [Finset.mem_univ, true_and] using
        probEvent_exists_finset_le_sum (Finset.univ : Finset GlobalBadEvent)
          (detailedGameWithCache Concrete.scheme adversary)
          (fun event execution =>
            WinningGlobalBadEventOccurs execution.2 execution.1 event)

end XmssSecurity
