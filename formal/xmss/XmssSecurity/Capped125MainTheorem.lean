import XmssSecurity.CappedGlobalChainHighBoundedPublic
import XmssSecurity.CappedUnifiedMainTheorem

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem capped_globalWinningChainValueRevealed_probability_le_two_queries
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q)
    (hreduction : CappedChain.HasGlobalHighBoundedPublicReduction q adversary) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      GlobalWinningChainValueRevealed execution.2 execution.1 |
      detailedGameWithCache Concrete.cappedScheme adversary] ≤
      2 * ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
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
    _ ≤ 2 * ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) :=
      CappedChain.globalWinningChainOrigin_probability_le_two_queries
        q adversary hbound hreduction

theorem five_digest_terms_le_125 (q : Nat) :
    (5 : ENNReal) *
        ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) ≤
      (q : ENNReal) / ((2 ^ 125 : Nat) : ENNReal) := by
  apply le_trans ?_ (seven_digest_terms_le_125 q)
  gcongr
  norm_num

theorem capped_xmss_forgeAdvantage_le_125_of_boundedPublicReduction
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q)
    (hreduction : CappedChain.HasGlobalHighBoundedPublicReduction q adversary) :
    forgeAdvantage Concrete.cappedScheme adversary ≤
      (q : ENNReal) / ((2 ^ 125 : Nat) : ENNReal) := by
  calc
    forgeAdvantage Concrete.cappedScheme adversary ≤
        2 * ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) +
          2 * ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) +
          (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
      apply (capped_forgeAdvantage_le_unifiedBadEvents adversary).trans
      gcongr
      · exact cappedWinning_encoding_event_probability_le_two_terms
          q adversary hbound
      · exact capped_globalWinningChainValueRevealed_probability_le_two_queries
          q adversary hbound hreduction
      · exact capped_winningStructuralCollision_probability_le
          q adversary hbound
    _ = 5 * ((q : ENNReal) /
        ((2 ^ digestBits : Nat) : ENNReal)) := by ring
    _ ≤ (q : ENNReal) / ((2 ^ 125 : Nat) : ENNReal) :=
      five_digest_terms_le_125 q

def HasCappedGlobalHighBoundedPublicReductions : Prop :=
  ∀ (q : Nat) (adversary : Adversary Concrete.cappedScheme),
    HasHashQueryBound Concrete.cappedScheme adversary q →
      CappedChain.HasGlobalHighBoundedPublicReduction q adversary

theorem xmss_has_125_bits_of_classical_security_of_boundedPublicReductions
    (hreductions : HasCappedGlobalHighBoundedPublicReductions) :
    HasClassicalSecurityBits Concrete.cappedScheme 125 := by
  intro q _hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact capped_xmss_forgeAdvantage_le_125_of_boundedPublicReduction q adversary
    hbound (hreductions q adversary hbound)

end XmssSecurity
