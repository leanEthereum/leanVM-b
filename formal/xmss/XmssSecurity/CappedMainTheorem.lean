import XmssSecurity.CappedSigningLogReplay
import XmssSecurity.CappedEncodingEventProbability
import XmssSecurity.CappedSuffixEventProbability
import XmssSecurity.CappedLeafEventProbability
import XmssSecurity.CappedMerkleEventProbability
import XmssSecurity.CappedChain.ChainOriginProbability
import XmssSecurity.CappedChain.CausalEagerHighDirectReduction
import XmssSecurity.MainTheorem

namespace XmssSecurity

open OracleSpec

theorem capped_xmss_remaining_core_probability_le_below_digest_space
    (q : Nat) (_hq : 1 ≤ q) (_hqlt : q < 2 ^ digestBits)
    (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 .encoding |
      detailedGameWithCache Concrete.cappedScheme adversary] ≤
      2 * ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) ∧
    ∀ chain : ChainIndex,
      Pr[fun result =>
        CappedChain.WinningOutcomeGuessesKeygenChainValue result.1.2 result.2.2
          result.1.1.2 result.2.1 chain |
        CappedChain.detailedGameWithKeygenCache adversary] ≤
        (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  constructor
  · exact cappedWinning_encoding_event_probability_le_two_terms q adversary
      hbound
  · intro chain
    refine (CappedChain.winningKeygenValueGuess_probability_le_origin adversary
      chain).trans ?_
    apply CappedChain.winningChainOrigin_probability_le_of_eagerViewReduction
      q adversary hbound chain
    apply CappedChain.hasActionTracedEagerViewReduction_of_boundedFilteredHighDirectReduction
    exact CappedChain.hasBoundedFilteredHighDirectReduction_of_hashQueryBound
      q adversary chain hbound

/-- The remaining capped-signer proof obligation is a weighted bound for each concrete bad event below the digest-space size. -/
theorem capped_xmss_badEvent_probability_le_below_digest_space
    (q : Nat) (hq : 1 ≤ q) (hqlt : q < 2 ^ digestBits)
    (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q)
    (event : BadEvent) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 event |
      detailedGameWithCache Concrete.cappedScheme adversary] ≤
      (badEventWeight event : ENNReal) *
        ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
  cases event with
  | encoding =>
      simpa [badEventWeight] using
        (capped_xmss_remaining_core_probability_le_below_digest_space
          q hq hqlt adversary hbound).1
  | chain chain =>
      calc
        Pr[fun execution : GameOutcome × QueryCache HashSpec =>
            WinningOutcomeBadEventOccurs execution.2 execution.1 (.chain chain) |
            detailedGameWithCache Concrete.cappedScheme adversary] ≤
          Pr[fun execution : GameOutcome × QueryCache HashSpec =>
              WinningOutcomeBadEventOccurs execution.2 execution.1 (.chain chain) ∧
                OutcomeChainValueRevealed execution.2 execution.1 chain |
              detailedGameWithCache Concrete.cappedScheme adversary] +
            (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) :=
          CappedChain.winning_chain_outcomeBadEvent_probability_le_revealed_add
            q adversary hbound chain
        _ ≤ Pr[fun result =>
              CappedChain.WinningOutcomeGuessesKeygenChainValue result.1.2
                result.2.2 result.1.1.2 result.2.1 chain |
              CappedChain.detailedGameWithKeygenCache adversary] +
            (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
          gcongr
          exact
            CappedChain.winningChainValueRevealed_probability_le_winningKeygenValueGuess
              adversary chain
        _ ≤ (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) +
            (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
          gcongr
          exact (capped_xmss_remaining_core_probability_le_below_digest_space
            q hq hqlt adversary hbound).2 chain
        _ = (badEventWeight (.chain chain) : ENNReal) *
            ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
          simp [badEventWeight, two_mul]
  | suffixCollision slot =>
      exact (capped_winningOutcomeBadEvent_probability_le_outcomeBadEvent
        adversary (.suffixCollision slot)).trans (by
          simpa [badEventWeight] using
            capped_suffixCollision_outcomeBadEvent_probability_le q adversary
              hbound slot)
  | leaf =>
      exact (capped_winningOutcomeBadEvent_probability_le_outcomeBadEvent
        adversary .leaf).trans (by
          simpa [badEventWeight] using
            capped_leaf_outcomeBadEvent_probability_le q adversary hbound)
  | merkle level =>
      exact (capped_winningOutcomeBadEvent_probability_le_outcomeBadEvent
        adversary (.merkle level)).trans (by
          simpa [badEventWeight] using
            capped_merkle_outcomeBadEvent_probability_le q adversary hbound
              level)

theorem capped_xmss_badEvent_probability_le
    (q : Nat) (hq : 1 ≤ q)
    (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q)
    (event : BadEvent) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 event |
      detailedGameWithCache Concrete.cappedScheme adversary] ≤
      (badEventWeight event : ENNReal) *
        ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
  by_cases hqlt : q < 2 ^ digestBits
  · exact capped_xmss_badEvent_probability_le_below_digest_space
      q hq hqlt adversary hbound event
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

theorem capped_xmss_forgeAdvantage_le
    (q : Nat) (hq : 1 ≤ q)
    (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q) :
    forgeAdvantage Concrete.cappedScheme adversary ≤
      (q : ENNReal) / ((2 ^ 120 : Nat) : ENNReal) := by
  refine (capped_forgeAdvantage_le_winningOutcomeBadEvent_sum adversary).trans ?_
  apply badEvent_weighted_sum_le_120
  intro event
  exact capped_xmss_badEvent_probability_le q hq adversary hbound event

/-- The concrete XMSS scheme with at most `2^23` encoding attempts per signing request has at least 120 bits of classical security in the random-oracle game. -/
theorem xmss_has_120_bits_of_classical_security :
    HasClassicalSecurityBits Concrete.cappedScheme 120 := by
  intro q hq
  unfold forgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  exact capped_xmss_forgeAdvantage_le q hq adversary hbound

end XmssSecurity
