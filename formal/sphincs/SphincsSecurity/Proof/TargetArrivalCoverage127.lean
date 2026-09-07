import SphincsSecurity.Proof.AdaptiveTargetArrival
import SphincsSecurity.Proof.CachedTargetCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_adaptive_cappedCachedTargetEnvelope_full_add_unused_scaled_le_127 {α : Type}
    (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      cappedCachedTargetEnvelope key q result.2 ∅ Finset.univ) * ((2 ^ 140 : Nat) : ENNReal)⁻¹ +
      expectedUnusedTargetIndexCharge key q ∅ Finset.univ computation (cache, []) * ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≤
        (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hvalid : TargetShapeValid ∅ Finset.univ := by constructor <;> simp
  have h := expected_adaptive_cappedCachedTargetEnvelope_add_unused_le key q hq computation (cache, []) hsigned hbudget ∅ Finset.univ hvalid
  have hinitial : cappedCachedTargetEnvelope key q (cache, []) ∅ Finset.univ = 0 := by
    rw [cappedCachedTargetEnvelope, if_pos (show SigningTranscript.Valid [] from Nat.zero_le _), cachedTargetEnvelope]
    exact cacheMessageWeight_of_no_message key.parameter _ cache hnone
  rw [hinitial, zero_add] at h
  have hrate : (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
      ((2 ^ 140 : Nat) : ENNReal)⁻¹ = ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
    norm_num [Index, totalHeight, ftsTreeHeight, ← ENNReal.mul_inv]
  have hscaled := mul_le_mul' h (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹))
  rw [add_mul, mul_right_comm _ (expectedUnusedTargetIndexCharge _ _ _ _ _ _), hrate,
    mul_right_comm _ (expectedMacroIndexCharge _ _ _ _ _ _), hrate] at hscaled
  apply le_trans ?_ (expectedMacroIndexCharge_full_scaled_le_127 key q hq computation hbound cache hnone hbudget)
  simpa only [mul_comm] using hscaled

theorem probEvent_adaptive_signingCacheCovered_add_unused_le_127 {α : Type}
    (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => SigningTranscript.Valid result.2.2 ∧ SigningCacheCovered key.parameter key.root result.2.1 result.2.2 |
      (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] +
      expectedUnusedTargetIndexCharge key q ∅ Finset.univ computation (cache, []) * ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≤
        (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  apply le_trans ?_ (expected_adaptive_cappedCachedTargetEnvelope_full_add_unused_scaled_le_127 key q hq computation hbound cache hnone hbudget)
  apply add_le_add _ le_rfl
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro result
  split_ifs with hcover
  · rw [mul_assoc]
    exact le_mul_of_one_le_right' (one_le_cappedCachedTargetEnvelope_scaled_of_covered key q result.2 hcover.1 hcover.2)
  · exact bot_le

theorem probEvent_adaptive_observedFewTimeCover_add_unused_le_127 {α : Type}
    (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (cache : QueryCache HashSpec) (forgery : α → Forgery)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => SigningTranscript.Valid result.2.2 ∧
      ObservedFewTimeCover (FtsProbeSimulation.messageAnswers key.parameter result.2.1) key.root result.2.2 (forgery result.1) |
      (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] +
      expectedUnusedTargetIndexCharge key q ∅ Finset.univ computation (cache, []) * ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≤
        (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  apply le_trans ?_ (probEvent_adaptive_signingCacheCovered_add_unused_le_127 key q hq computation hbound cache hnone hbudget)
  apply add_le_add _ le_rfl
  apply probEvent_mono
  intro result _ hcover
  exact ⟨hcover.1, observedFewTimeCover_signingCacheCovered _ _ _ _ _ hcover.2⟩

end SphincsSecurity.Concrete
