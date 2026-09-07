import SphincsSecurity.Proof.AdaptiveCachedTarget
import SphincsSecurity.Proof.AdaptiveIndexCharge127

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expected_adaptive_cappedCachedTargetEnvelope_full_scaled_le_127 {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      cappedCachedTargetEnvelope key q result.2 ∅ Finset.univ) * ((2 ^ 140 : Nat) : ENNReal)⁻¹ ≤
        (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hvalid : TargetShapeValid ∅ Finset.univ := by constructor <;> simp
  have h := expected_adaptive_cappedCachedTargetEnvelope_le key q hq computation (cache, []) hsigned hbudget ∅ Finset.univ hvalid
  have hinitial : cappedCachedTargetEnvelope key q (cache, []) ∅ Finset.univ = 0 := by
    rw [cappedCachedTargetEnvelope, if_pos (show SigningTranscript.Valid [] from Nat.zero_le _), cachedTargetEnvelope]
    exact cacheMessageWeight_of_no_message key.parameter _ cache hnone
  rw [hinitial, zero_add] at h
  apply (mul_le_mul' h le_rfl).trans
  have hrate : (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
      ((2 ^ 140 : Nat) : ENNReal)⁻¹ = ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
    norm_num [Index, totalHeight, ftsTreeHeight, ← ENNReal.mul_inv]
  rw [mul_right_comm, hrate, mul_comm]
  exact expectedMacroIndexCharge_full_scaled_le_127 key q hq computation hbound cache hnone hbudget

end SphincsSecurity.Concrete
