import XmssSecurity.GlobalBadEvent
import XmssSecurity.CappedSuffixEventProbability
import XmssSecurity.CappedMerkleEventProbability
import XmssSecurity.CappedChain.ChainOriginProbability

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem capped_outcomePredicate_probability_le_of_afterKeygen_freshCollision
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q)
    (event : GameOutcome × QueryCache HashSpec → Prop)
    (targetInput :
      (PublicKey × SecretKey) → QueryCache HashSpec → HashInput → HashInput)
    (horient : ∀ keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.cappedScheme.keygen).run ∅),
      ∀ execution ∈ support
        ((simulateQ xmssRomImpl
          (detailedGameAfterKeygen Concrete.cappedScheme adversary
            keyResult.1.1 keyResult.1.2)).run keyResult.2),
        event execution →
          Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
            (targetInput keyResult.1 keyResult.2)) :
    Pr[event | detailedGameWithCache Concrete.cappedScheme adversary] ≤
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  have hdetailedBound :
      (detailedGameCore Concrete.cappedScheme adversary).IsQueryBoundP
        (· matches .inr _) q :=
    (hasHashQueryBound_iff_detailedGameCore Concrete.cappedScheme adversary q).mp
      hbound
  unfold detailedGameWithCache detailedGameCore
  apply Rom.mixed_adaptiveFreshDigestCollision_after_prefix_le
    Concrete.cappedScheme.keygen
    (fun key => detailedGameAfterKeygen Concrete.cappedScheme adversary
      key.1 key.2)
    q hdetailedBound ∅ targetInput event
  exact horient

theorem globalSuffixCollision_event_afterKeygen_orientation
    (adversary : Adversary Concrete.cappedScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.cappedScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.cappedScheme adversary
          keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (hevent : GlobalOutcomeBadEventOccurs execution.2 execution.1
      .suffixCollision) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (CappedSuffix.keygenChainTargetInput keyResult.1.2 keyResult.2) := by
  obtain ⟨slot, hslot⟩ := hevent
  exact CappedSuffix.suffixCollision_event_afterKeygen_orientation adversary
    keyResult hkeygen execution hafter slot hslot

theorem capped_globalSuffixCollision_probability_le
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      GlobalOutcomeBadEventOccurs execution.2 execution.1 .suffixCollision |
      detailedGameWithCache Concrete.cappedScheme adversary] ≤
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  apply capped_outcomePredicate_probability_le_of_afterKeygen_freshCollision
    q adversary hbound _
    (fun key cache => CappedSuffix.keygenChainTargetInput key.2 cache)
  intro keyResult hkeygen execution hafter hevent
  exact globalSuffixCollision_event_afterKeygen_orientation adversary
    keyResult hkeygen execution hafter hevent

theorem globalMerkle_event_afterKeygen_orientation
    (adversary : Adversary Concrete.cappedScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.cappedScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.cappedScheme adversary
          keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (hevent : GlobalOutcomeBadEventOccurs execution.2 execution.1 .merkle) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (CappedMerkle.keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  obtain ⟨level, hlevel⟩ := hevent
  exact CappedMerkle.merkle_event_afterKeygen_orientation adversary keyResult
    hkeygen execution hafter level hlevel

theorem capped_globalMerkle_probability_le
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      GlobalOutcomeBadEventOccurs execution.2 execution.1 .merkle |
      detailedGameWithCache Concrete.cappedScheme adversary] ≤
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  apply capped_outcomePredicate_probability_le_of_afterKeygen_freshCollision
    q adversary hbound _
    (fun key cache => CappedMerkle.keygenMerkleTargetInput key.2 cache)
  intro keyResult hkeygen execution hafter hevent
  exact globalMerkle_event_afterKeygen_orientation adversary keyResult hkeygen
    execution hafter hevent

def GlobalWinningChainValueRevealed
    (cache : QueryCache HashSpec) (outcome : GameOutcome) : Prop :=
  ∃ chain, WinningOutcomeBadEventOccurs cache outcome (.chain chain) ∧
    CappedChain.OutcomeChainValueRevealed cache outcome chain

theorem capped_globalWinningChain_probability_le_revealed_add
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningGlobalBadEventOccurs execution.2 execution.1 .chain |
      detailedGameWithCache Concrete.cappedScheme adversary] ≤
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        GlobalWinningChainValueRevealed execution.2 execution.1 |
        detailedGameWithCache Concrete.cappedScheme adversary] +
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  let bad := fun execution : GameOutcome × QueryCache HashSpec =>
    WinningGlobalBadEventOccurs execution.2 execution.1 .chain
  let revealed := fun execution : GameOutcome × QueryCache HashSpec =>
    GlobalWinningChainValueRevealed execution.2 execution.1
  let remainder := fun execution : GameOutcome × QueryCache HashSpec =>
    bad execution ∧ ¬revealed execution
  have hcollision :
      Pr[remainder | detailedGameWithCache Concrete.cappedScheme adversary] ≤
        (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
    apply capped_outcomePredicate_probability_le_of_afterKeygen_freshCollision
      q adversary hbound remainder
      (fun key cache => CappedSuffix.keygenChainTargetInput key.2 cache)
    intro keyResult hkeygen execution hafter hrest
    obtain ⟨hwin, chain, hchain⟩ := hrest.1
    rcases CappedChain.chain_event_afterKeygen_revealed_or_collision adversary
        keyResult hkeygen execution hafter chain hchain with
      hrevealed | hcollision
    · exact (hrest.2 ⟨chain, ⟨hwin, hchain⟩, hrevealed⟩).elim
    · simpa only [CappedChain.keygenChainTargetInput_eq_capped] using
        hcollision
  calc
    Pr[bad | detailedGameWithCache Concrete.cappedScheme adversary] ≤
        Pr[fun execution =>
          (bad execution ∧ revealed execution) ∨ remainder execution |
          detailedGameWithCache Concrete.cappedScheme adversary] := by
      apply probEvent_mono''
      intro execution hbad
      by_cases hrevealed : revealed execution
      · exact Or.inl ⟨hbad, hrevealed⟩
      · exact Or.inr ⟨hbad, hrevealed⟩
    _ ≤ Pr[fun execution => bad execution ∧ revealed execution |
          detailedGameWithCache Concrete.cappedScheme adversary] +
        Pr[remainder | detailedGameWithCache Concrete.cappedScheme adversary] :=
      probEvent_or_le _ _ _
    _ ≤ Pr[revealed |
          detailedGameWithCache Concrete.cappedScheme adversary] +
        (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
      apply add_le_add
      · apply probEvent_mono''
        intro execution hboth
        exact hboth.2
      · exact hcollision

end XmssSecurity
