import XmssSecurity.ConcreteEventCollision
import XmssSecurity.PrefixTarget

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-- Once key generation fixes a target input for every possible fresh query, temporal orientation of a concrete bad event gives its `q / 2^128` probability bound. -/
theorem outcomeBadEvent_probability_le_of_afterKeygen_freshCollision_forScheme
    (scheme : Scheme) (q : Nat) (adversary : Adversary scheme)
    (hbound : HasHashQueryBound scheme adversary q) (event : BadEvent)
    (targetInput : (PublicKey × SecretKey) → QueryCache HashSpec → HashInput → HashInput)
    (horient : ∀ keyResult ∈ support
      ((simulateQ xmssRomImpl scheme.keygen).run ∅),
      ∀ execution ∈ support
        ((simulateQ xmssRomImpl
          (detailedGameAfterKeygen scheme adversary keyResult.1.1 keyResult.1.2)).run
            keyResult.2),
        OutcomeBadEventOccurs execution.2 execution.1 event →
          Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
            (targetInput keyResult.1 keyResult.2)) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      OutcomeBadEventOccurs execution.2 execution.1 event |
      detailedGameWithCache scheme adversary] ≤
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  have hdetailedBound :
      (detailedGameCore scheme adversary).IsQueryBoundP
        (· matches .inr _) q :=
    (hasHashQueryBound_iff_detailedGameCore scheme adversary q).mp hbound
  unfold detailedGameWithCache detailedGameCore
  apply Rom.mixed_adaptiveFreshDigestCollision_after_prefix_le
    scheme.keygen
    (fun key => detailedGameAfterKeygen scheme adversary key.1 key.2)
    q hdetailedBound ∅ targetInput
    (fun execution => OutcomeBadEventOccurs execution.2 execution.1 event)
  exact horient

theorem outcomeBadEvent_probability_le_of_afterKeygen_freshCollision
    (q : Nat) (adversary : Adversary Concrete.singleAttemptScheme)
    (hbound : HasHashQueryBound Concrete.singleAttemptScheme adversary q) (event : BadEvent)
    (targetInput : (PublicKey × SecretKey) → QueryCache HashSpec → HashInput → HashInput)
    (horient : ∀ keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅),
      ∀ execution ∈ support
        ((simulateQ xmssRomImpl
          (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary keyResult.1.1 keyResult.1.2)).run
            keyResult.2),
        OutcomeBadEventOccurs execution.2 execution.1 event →
          Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
            (targetInput keyResult.1 keyResult.2)) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      OutcomeBadEventOccurs execution.2 execution.1 event |
      detailedGameWithCache Concrete.singleAttemptScheme adversary] ≤
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) :=
  outcomeBadEvent_probability_le_of_afterKeygen_freshCollision_forScheme
    Concrete.singleAttemptScheme q adversary hbound event targetInput horient

end XmssSecurity
