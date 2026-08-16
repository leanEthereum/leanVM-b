import XmssSecurity.CappedUnifiedStructuralCollision
import XmssSecurity.CappedEncodingEventProbability
import XmssSecurity.CappedGlobalMainTheorem

open OracleComp OracleSpec ENNReal

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
      by_cases hrevealed :
          GlobalWinningChainValueRevealed cache outcome
      · exact Or.inr (Or.inl hrevealed)
      · exact Or.inr (Or.inr (Or.inl ⟨hevent, hrevealed⟩))
  | suffixCollision =>
      exact Or.inr (Or.inr (Or.inr (Or.inl hevent)))
  | leaf =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hevent))))
  | merkle =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hevent))))

theorem capped_forgeAdvantage_le_winningUnifiedBadEvent
    (adversary : Adversary Concrete.cappedScheme) :
    forgeAdvantage Concrete.cappedScheme adversary ≤
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        WinningUnifiedBadEventOccurs execution.2 execution.1 |
        detailedGameWithCache Concrete.cappedScheme adversary] := by
  rw [forgeAdvantage_eq_detailedGameWithCache]
  apply probEvent_mono
  intro execution hmem hwin
  exact winning_outcome_has_unifiedBadEvent execution.2 execution.1
    (capped_detailed_execution_consistent adversary execution hmem) hwin

theorem capped_forgeAdvantage_le_unifiedBadEvents
    (adversary : Adversary Concrete.cappedScheme) :
    forgeAdvantage Concrete.cappedScheme adversary ≤
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        WinningEncodingEventOccurs execution.2 execution.1 |
        detailedGameWithCache Concrete.cappedScheme adversary] +
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        GlobalWinningChainValueRevealed execution.2 execution.1 |
        detailedGameWithCache Concrete.cappedScheme adversary] +
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        WinningStructuralCollisionOccurs execution.2 execution.1 |
        detailedGameWithCache Concrete.cappedScheme adversary] := by
  rw [forgeAdvantage_eq_detailedGameWithCache]
  calc
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true |
        detailedGameWithCache Concrete.cappedScheme adversary] ≤
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        WinningUnifiedBadEventOccurs execution.2 execution.1 |
        detailedGameWithCache Concrete.cappedScheme adversary] := by
      apply probEvent_mono
      intro execution hmem hwin
      exact winning_outcome_has_unifiedBadEvent execution.2 execution.1
        (capped_detailed_execution_consistent adversary execution hmem) hwin
    _ ≤ Pr[fun execution : GameOutcome × QueryCache HashSpec =>
          WinningEncodingEventOccurs execution.2 execution.1 |
          detailedGameWithCache Concrete.cappedScheme adversary] +
        Pr[fun execution : GameOutcome × QueryCache HashSpec =>
          GlobalWinningChainValueRevealed execution.2 execution.1 |
          detailedGameWithCache Concrete.cappedScheme adversary] +
        Pr[fun execution : GameOutcome × QueryCache HashSpec =>
          WinningStructuralCollisionOccurs execution.2 execution.1 |
          detailedGameWithCache Concrete.cappedScheme adversary] := by
      let encoding := fun execution : GameOutcome × QueryCache HashSpec =>
        WinningEncodingEventOccurs execution.2 execution.1
      let revealed := fun execution : GameOutcome × QueryCache HashSpec =>
        GlobalWinningChainValueRevealed execution.2 execution.1
      let structural := fun execution : GameOutcome × QueryCache HashSpec =>
        WinningStructuralCollisionOccurs execution.2 execution.1
      calc
        Pr[fun execution => WinningUnifiedBadEventOccurs execution.2 execution.1 |
            detailedGameWithCache Concrete.cappedScheme adversary] =
          Pr[fun execution => encoding execution ∨
              (revealed execution ∨ structural execution) |
            detailedGameWithCache Concrete.cappedScheme adversary] := by rfl
        _ ≤ Pr[encoding | detailedGameWithCache Concrete.cappedScheme adversary] +
            Pr[fun execution => revealed execution ∨ structural execution |
              detailedGameWithCache Concrete.cappedScheme adversary] :=
          probEvent_or_le _ _ _
        _ ≤ Pr[encoding | detailedGameWithCache Concrete.cappedScheme adversary] +
            (Pr[revealed | detailedGameWithCache Concrete.cappedScheme adversary] +
              Pr[structural |
                detailedGameWithCache Concrete.cappedScheme adversary]) := by
          gcongr
          exact probEvent_or_le _ _ _
        _ = _ := by
          dsimp only [encoding, revealed, structural]
          ac_rfl

theorem capped_globalWinningChainValueRevealed_probability_le_of_globalChainReduction
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hreduction : CappedChain.HasGlobalChainEagerReduction q adversary) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      GlobalWinningChainValueRevealed execution.2 execution.1 |
      detailedGameWithCache Concrete.cappedScheme adversary] ≤
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  calc
    _ ≤ Pr[fun result =>
          CappedChain.GlobalWinningOutcomeGuessesKeygenChainValue
            result.1.2 result.2.2 result.1.1.2 result.2.1 |
          CappedChain.detailedGameWithKeygenCache adversary] :=
      CappedChain.globalWinningChainValueRevealed_probability_le_globalKeygenValueGuess
        adversary
    _ ≤ Pr[fun result =>
          CappedChain.GlobalWinningOutcomeChainValueHasKeygenOrigin
            result.1.2 result.2.2 result.1.1.2 result.2.1 |
          CappedChain.detailedGameWithKeygenCache adversary] :=
      CappedChain.globalWinningKeygenValueGuess_probability_le_origin adversary
    _ ≤ (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) :=
      CappedChain.globalWinningChainOrigin_probability_le_of_eagerReduction
        q adversary hreduction

theorem four_digest_terms_le_126 (q : Nat) :
    (4 : ENNReal) *
        ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) ≤
      (q : ENNReal) / ((2 ^ 126 : Nat) : ENNReal) := by
  have hbits : digestBits = 2 + 126 := by decide
  have hzero : ((2 ^ 2 : Nat) : ENNReal) ≠ 0 := by positivity
  have htop : ((2 ^ 2 : Nat) : ENNReal) ≠ ∞ := by simp
  rw [show (4 : ENNReal) = ((2 ^ 2 : Nat) : ENNReal) by norm_num]
  rw [hbits, Nat.pow_add, Nat.cast_mul, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl hzero) (Or.inl htop)]
  calc
    ((2 ^ 2 : Nat) : ENNReal) *
        ((q : ENNReal) *
          (((2 ^ 2 : Nat) : ENNReal)⁻¹ *
            ((2 ^ 126 : Nat) : ENNReal)⁻¹)) =
      (((2 ^ 2 : Nat) : ENNReal) *
        ((2 ^ 2 : Nat) : ENNReal)⁻¹) *
        ((q : ENNReal) * ((2 ^ 126 : Nat) : ENNReal)⁻¹) := by
      ac_rfl
    _ = (q : ENNReal) * ((2 ^ 126 : Nat) : ENNReal)⁻¹ := by
      rw [ENNReal.mul_inv_cancel hzero htop, one_mul]
    _ ≤ (q : ENNReal) / ((2 ^ 126 : Nat) : ENNReal) := by
      rw [div_eq_mul_inv]

theorem capped_xmss_forgeAdvantage_le_126_of_globalChainReduction
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q)
    (hreduction : CappedChain.HasGlobalChainEagerReduction q adversary) :
    forgeAdvantage Concrete.cappedScheme adversary ≤
      (q : ENNReal) / ((2 ^ 126 : Nat) : ENNReal) := by
  calc
    forgeAdvantage Concrete.cappedScheme adversary ≤
        2 * ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) +
          (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) +
          (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
      apply (capped_forgeAdvantage_le_unifiedBadEvents adversary).trans
      gcongr
      · exact cappedWinning_encoding_event_probability_le_two_terms
          q adversary hbound
      · exact
          capped_globalWinningChainValueRevealed_probability_le_of_globalChainReduction
            q adversary hreduction
      · exact capped_winningStructuralCollision_probability_le
          q adversary hbound
    _ = 4 * ((q : ENNReal) /
        ((2 ^ digestBits : Nat) : ENNReal)) := by ring
    _ ≤ (q : ENNReal) / ((2 ^ 126 : Nat) : ENNReal) :=
      four_digest_terms_le_126 q

theorem xmss_has_126_bits_of_classical_security_of_globalChainReductions
    (hreductions : HasCappedGlobalChainReductions) :
    HasClassicalSecurityBits Concrete.cappedScheme 126 := by
  intro q _hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact capped_xmss_forgeAdvantage_le_126_of_globalChainReduction q adversary
    hbound (hreductions q adversary hbound)

end XmssSecurity
