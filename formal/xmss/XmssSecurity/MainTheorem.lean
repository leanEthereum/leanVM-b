import XmssSecurity.Encoding
import XmssSecurity.ConcreteScheme
import XmssSecurity.EncodingEventProbability
import XmssSecurity.EncodingOracleSimulation
import XmssSecurity.ForgeryCases
import XmssSecurity.HiddenValue
import XmssSecurity.IndexedHiddenValue
import XmssSecurity.ChainOriginProbability
import XmssSecurity.ChainHiddenTable
import XmssSecurity.LeafEventProbability
import XmssSecurity.Merkle
import XmssSecurity.MerkleEventProbability
import XmssSecurity.PublicRootUniformity
import XmssSecurity.SecurityBudget
import XmssSecurity.SecurityGame
import XmssSecurity.SigningLogReplay
import XmssSecurity.SigningCacheTrace
import XmssSecurity.SuffixEventProbability
import XmssSecurity.Wots
import XmssSecurity.WinningEventReduction

namespace XmssSecurity

open OracleSpec

/-- The remaining probabilistic core consists of the encoding target collision and one indexed hidden-value hit. -/
theorem xmss_remaining_core_probability_le_below_digest_space (q : Nat) (hq : 1 ≤ q)
    (hqlt : q < 2 ^ digestBits)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 .encoding |
      detailedGameWithCache Concrete.scheme adversary] ≤
      2 * ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) ∧
    ∀ chain : ChainIndex,
      Pr[fun result =>
        WinningOutcomeGuessesKeygenChainValue result.1.2 result.2.2 result.1.1.2
          result.2.1 chain |
        detailedGameWithKeygenCache adversary] ≤
        (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  constructor
  · exact winning_encoding_event_probability_le_two_terms q adversary hbound
  · intro chain
    refine (winningKeygenValueGuess_probability_le_origin adversary chain).trans ?_
    sorry

/-- Below the digest-space size, encoding and chain events cost two elementary terms and every other event costs one. -/
theorem xmss_badEvent_probability_le_below_digest_space (q : Nat) (hq : 1 ≤ q)
    (hqlt : q < 2 ^ digestBits)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) (event : BadEvent) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 event |
      detailedGameWithCache Concrete.scheme adversary] ≤
      (badEventWeight event : ENNReal) *
        ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
  cases event with
  | encoding =>
      simpa [badEventWeight] using
        (xmss_remaining_core_probability_le_below_digest_space q hq hqlt adversary hbound).1
  | chain chain =>
      calc
        Pr[fun execution : GameOutcome × QueryCache HashSpec =>
            WinningOutcomeBadEventOccurs execution.2 execution.1 (.chain chain) |
            detailedGameWithCache Concrete.scheme adversary] ≤
          Pr[fun execution : GameOutcome × QueryCache HashSpec =>
              WinningOutcomeBadEventOccurs execution.2 execution.1 (.chain chain) ∧
                OutcomeChainValueRevealed execution.2 execution.1 chain |
              detailedGameWithCache Concrete.scheme adversary] +
            (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) :=
          winning_chain_outcomeBadEvent_probability_le_revealed_add
            q adversary hbound chain
        _ ≤ Pr[fun result =>
              WinningOutcomeGuessesKeygenChainValue result.1.2 result.2.2
                result.1.1.2 result.2.1 chain |
              detailedGameWithKeygenCache adversary] +
            (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
          gcongr
          exact winningChainValueRevealed_probability_le_winningKeygenValueGuess
            adversary chain
        _ ≤ (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) +
            (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
          gcongr
          exact (xmss_remaining_core_probability_le_below_digest_space
            q hq hqlt adversary hbound).2 chain
        _ = (badEventWeight (.chain chain) : ENNReal) *
            ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
          simp [badEventWeight, two_mul]
  | suffixCollision slot =>
      exact (winningOutcomeBadEvent_probability_le_outcomeBadEvent adversary
        (.suffixCollision slot)).trans (by
          simpa [badEventWeight] using
            suffixCollision_outcomeBadEvent_probability_le q adversary hbound slot)
  | leaf =>
      exact (winningOutcomeBadEvent_probability_le_outcomeBadEvent adversary .leaf).trans (by
        simpa [badEventWeight] using leaf_outcomeBadEvent_probability_le q adversary hbound)
  | merkle level =>
      exact (winningOutcomeBadEvent_probability_le_outcomeBadEvent adversary
        (.merkle level)).trans (by
          simpa [badEventWeight] using
            merkle_outcomeBadEvent_probability_le q adversary hbound level)

/-- Every concrete event satisfies its weighted bound; above `2^128` queries this follows from the trivial probability bound. -/
theorem xmss_badEvent_probability_le (q : Nat) (hq : 1 ≤ q)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) (event : BadEvent) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 event |
      detailedGameWithCache Concrete.scheme adversary] ≤
      (badEventWeight event : ENNReal) *
        ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
  by_cases hqlt : q < 2 ^ digestBits
  · exact xmss_badEvent_probability_le_below_digest_space q hq hqlt adversary hbound event
  · apply probEvent_le_one.trans
    have hbase : 1 ≤ (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
      rw [ENNReal.le_div_iff_mul_le]
      · exact_mod_cast Nat.le_of_not_gt hqlt
      · simp
      · simp
    calc
      1 ≤ (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := hbase
      _ ≤ (badEventWeight event : ENNReal) *
          ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
        cases event <;> simp [badEventWeight]
        all_goals
          rw [two_mul]
          exact le_add_right (α := ENNReal) le_rfl

/-- Every bounded adversary has forging probability at most `q / 2^120`. -/
theorem xmss_forgeAdvantage_le (q : Nat) (hq : 1 ≤ q)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    forgeAdvantage Concrete.scheme adversary ≤ (q : ENNReal) / ((2 ^ 120 : Nat) : ENNReal) := by
  refine (forgeAdvantage_le_winningOutcomeBadEvent_sum adversary).trans ?_
  apply badEvent_weighted_sum_le_120
  intro event
  exact xmss_badEvent_probability_le q hq adversary hbound event

/-- The concrete XMSS scheme has at least 120 bits of classical security in the random-oracle game. -/
theorem xmss_has_120_bits_of_classical_security :
    HasClassicalSecurityBits Concrete.scheme 120 := by
  intro q hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact xmss_forgeAdvantage_le q hq adversary hbound

end XmssSecurity
