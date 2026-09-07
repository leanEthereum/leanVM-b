import SphincsSecurity.Proof.CachedTargetCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_adaptive_signingCacheCovered_le_127 {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => SigningTranscript.Valid result.2.2 ∧ SigningCacheCovered key.parameter key.root result.2.1 result.2.2 |
      (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] ≤
        (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  apply le_trans ?_ (expected_adaptive_cappedCachedTargetEnvelope_full_scaled_le_127 key q hq computation hbound cache hnone hbudget)
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro result
  split_ifs with hcover
  · rw [mul_assoc]
    exact le_mul_of_one_le_right' (one_le_cappedCachedTargetEnvelope_scaled_of_covered key q result.2 hcover.1 hcover.2)
  · exact bot_le

theorem probEvent_adaptive_observedFewTimeCover_le_127 {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (cache : QueryCache HashSpec) (forgery : α → Forgery)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => SigningTranscript.Valid result.2.2 ∧
      ObservedFewTimeCover (FtsProbeSimulation.messageAnswers key.parameter result.2.1) key.root result.2.2 (forgery result.1) |
      (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] ≤
        (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  apply le_trans ?_ (probEvent_adaptive_signingCacheCovered_le_127 key q hq computation hbound cache hnone hbudget)
  apply probEvent_mono
  intro result _ hcover
  exact ⟨hcover.1, observedFewTimeCover_signingCacheCovered _ _ _ _ _ hcover.2⟩

end SphincsSecurity.Concrete
