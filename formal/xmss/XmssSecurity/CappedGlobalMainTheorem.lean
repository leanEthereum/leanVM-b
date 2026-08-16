import XmssSecurity.CappedEncodingEventProbability
import XmssSecurity.CappedLeafEventProbability
import XmssSecurity.CappedGlobalChainTracedGame

open OracleComp OracleSpec ENNReal
open scoped BigOperators

namespace XmssSecurity

def globalBadEventWeight : GlobalBadEvent → Nat
  | .encoding => 2
  | .chain => 2
  | .suffixCollision => 1
  | .leaf => 1
  | .merkle => 1

theorem globalBadEventWeight_sum :
    ∑ event : GlobalBadEvent, globalBadEventWeight event = 7 := by
  decide

theorem capped_winningGlobalBadEvent_probability_le_of_globalChainReduction
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q)
    (hchain : CappedChain.HasGlobalChainEagerReduction q adversary)
    (event : GlobalBadEvent) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningGlobalBadEventOccurs execution.2 execution.1 event |
      detailedGameWithCache Concrete.cappedScheme adversary] ≤
      (globalBadEventWeight event : ENNReal) *
        ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
  cases event with
  | encoding =>
      exact cappedWinning_encoding_event_probability_le_two_terms q adversary
        hbound
  | chain =>
      calc
        Pr[fun execution : GameOutcome × QueryCache HashSpec =>
            WinningGlobalBadEventOccurs execution.2 execution.1 .chain |
            detailedGameWithCache Concrete.cappedScheme adversary] ≤
          Pr[fun execution : GameOutcome × QueryCache HashSpec =>
              GlobalWinningChainValueRevealed execution.2 execution.1 |
              detailedGameWithCache Concrete.cappedScheme adversary] +
            (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) :=
          capped_globalWinningChain_probability_le_revealed_add q adversary
            hbound
        _ ≤ Pr[fun result =>
              CappedChain.GlobalWinningOutcomeGuessesKeygenChainValue
                result.1.2 result.2.2 result.1.1.2 result.2.1 |
              CappedChain.detailedGameWithKeygenCache adversary] +
            (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
          gcongr
          exact CappedChain.globalWinningChainValueRevealed_probability_le_globalKeygenValueGuess
            adversary
        _ ≤ Pr[fun result =>
              CappedChain.GlobalWinningOutcomeChainValueHasKeygenOrigin
                result.1.2 result.2.2 result.1.1.2 result.2.1 |
              CappedChain.detailedGameWithKeygenCache adversary] +
            (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
          gcongr
          exact CappedChain.globalWinningKeygenValueGuess_probability_le_origin
            adversary
        _ ≤ (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) +
            (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
          gcongr
          exact CappedChain.globalWinningChainOrigin_probability_le_of_eagerReduction
            q adversary hchain
        _ = (globalBadEventWeight .chain : ENNReal) *
            ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
          simp [globalBadEventWeight, two_mul]
  | suffixCollision =>
      simpa [globalBadEventWeight] using
        (probEvent_mono'' (p := fun execution : GameOutcome × QueryCache HashSpec =>
          WinningGlobalBadEventOccurs execution.2 execution.1
            .suffixCollision) (q := fun execution =>
          GlobalOutcomeBadEventOccurs execution.2 execution.1
            .suffixCollision) (by
          intro execution hevent
          exact hevent.2)).trans
            (capped_globalSuffixCollision_probability_le q adversary hbound)
  | leaf =>
      refine (capped_winningOutcomeBadEvent_probability_le_outcomeBadEvent
        adversary .leaf).trans ?_
      simpa [globalBadEventWeight] using
        capped_leaf_outcomeBadEvent_probability_le q adversary hbound
  | merkle =>
      simpa [globalBadEventWeight] using
        (probEvent_mono'' (p := fun execution : GameOutcome × QueryCache HashSpec =>
          WinningGlobalBadEventOccurs execution.2 execution.1 .merkle)
          (q := fun execution =>
            GlobalOutcomeBadEventOccurs execution.2 execution.1 .merkle) (by
          intro execution hevent
          exact hevent.2)).trans
            (capped_globalMerkle_probability_le q adversary hbound)

theorem seven_digest_terms_le_125 (q : Nat) :
    (7 : ENNReal) *
        ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) ≤
      (q : ENNReal) / ((2 ^ 125 : Nat) : ENNReal) := by
  have hbits : digestBits = 3 + 125 := by decide
  have hzero : ((2 ^ 3 : Nat) : ENNReal) ≠ 0 := by positivity
  have htop : ((2 ^ 3 : Nat) : ENNReal) ≠ ∞ := by simp
  calc
    (7 : ENNReal) *
        ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) ≤
      ((2 ^ 3 : Nat) : ENNReal) *
        ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
        gcongr
        norm_num
    _ = (q : ENNReal) / ((2 ^ 125 : Nat) : ENNReal) := by
      rw [hbits, Nat.pow_add, Nat.cast_mul, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl hzero) (Or.inl htop)]
      calc
        ((2 ^ 3 : Nat) : ENNReal) *
            ((q : ENNReal) *
              (((2 ^ 3 : Nat) : ENNReal)⁻¹ *
                ((2 ^ 125 : Nat) : ENNReal)⁻¹)) =
            (((2 ^ 3 : Nat) : ENNReal) *
              ((2 ^ 3 : Nat) : ENNReal)⁻¹) *
              ((q : ENNReal) * ((2 ^ 125 : Nat) : ENNReal)⁻¹) := by
          ac_rfl
        _ = (q : ENNReal) * ((2 ^ 125 : Nat) : ENNReal)⁻¹ := by
          rw [ENNReal.mul_inv_cancel hzero htop, one_mul]

theorem capped_xmss_forgeAdvantage_le_125_of_globalChainReduction
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q)
    (hchain : CappedChain.HasGlobalChainEagerReduction q adversary) :
    forgeAdvantage Concrete.cappedScheme adversary ≤
      (q : ENNReal) / ((2 ^ 125 : Nat) : ENNReal) := by
  refine (capped_forgeAdvantage_le_winningGlobalBadEvent_sum adversary).trans ?_
  refine (Finset.sum_le_sum fun event _ =>
    capped_winningGlobalBadEvent_probability_le_of_globalChainReduction
      q adversary hbound hchain event).trans ?_
  rw [← Finset.sum_mul]
  have hweight :
      ∑ event : GlobalBadEvent, (globalBadEventWeight event : ENNReal) = 7 := by
    exact_mod_cast globalBadEventWeight_sum
  rw [hweight]
  exact seven_digest_terms_le_125 q

/-- The single remaining hypothesis for 125-bit security is the global WOTS chain simulator. -/
def HasCappedGlobalChainReductions : Prop :=
  ∀ (q : Nat) (adversary : Adversary Concrete.cappedScheme),
    HasHashQueryBound Concrete.cappedScheme adversary q →
      CappedChain.HasGlobalChainEagerReduction q adversary

theorem xmss_has_125_bits_of_classical_security_of_globalChainReductions
    (hreductions : HasCappedGlobalChainReductions) :
    HasClassicalSecurityBits Concrete.cappedScheme 125 := by
  intro q _hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact capped_xmss_forgeAdvantage_le_125_of_globalChainReduction q adversary
    hbound (hreductions q adversary hbound)

end XmssSecurity
