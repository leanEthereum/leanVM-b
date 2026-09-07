import SphincsSecurity.Proof.WorldLinearReserve
import SphincsSecurity.Proof.UniformOccupancyInitialBound

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def freshMessageQueryCharge (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if cache input = none ∧ MessageHashInput parameter input then 1 else 0

noncomputable def linearReuseQueryRate (q : Nat) : ENNReal :=
  2 * (q : ENNReal) * (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * digestReuseWeight q) * ((2 ^ 176 : Nat) : ENNReal)⁻¹

theorem freshMessageReuseCharge_le_count (remaining : Nat) (key : SecretKey) (q : Nat)
    (log : QueryLog SigningSpec) (cache : QueryCache HashSpec) (input : HashInput) :
    freshMessageReuseCharge remaining key q log cache input ≤
      freshMessageQueryCharge key.parameter cache input *
        (linearReuseQueryRate q * uniformOccupancyIncrement remaining key cache log) := by
  by_cases hmessage : cache input = none ∧ MessageHashInput key.parameter input
  · simp only [freshMessageReuseCharge, freshMessageQueryCharge, if_pos hmessage, one_mul]
    have hslots : ((cacheSlotCount q cache - 1 : Nat) : ENNReal) ≤ (q : ENNReal) := by
      apply Nat.cast_le.mpr
      unfold cacheSlotCount
      omega
    exact mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hslots) le_rfl) le_rfl) le_rfl
  · simp only [freshMessageReuseCharge, freshMessageQueryCharge, if_neg hmessage, zero_mul, le_refl]

theorem expected_freshMessageReuseCharge_le_count {α : Type} (remaining : Nat) (key : SecretKey) (q : Nat)
    (log : QueryLog SigningSpec) (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (hsigned : SigningDigestsCached key.parameter cache key.root log) :
    expectedQueryCharge (freshMessageReuseCharge remaining key q log) computation cache ≤
      expectedQueryCharge (freshMessageQueryCharge key.parameter) computation cache *
        (linearReuseQueryRate q * uniformOccupancyIncrement remaining key cache log) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [expectedQueryCharge_pure, zero_mul, le_refl]
  | query_bind input next ih =>
      have hstep : hashQueryCharge (freshMessageReuseCharge remaining key q log) cache input ≤
          hashQueryCharge (freshMessageQueryCharge key.parameter) cache input *
            (linearReuseQueryRate q * uniformOccupancyIncrement remaining key cache log) := by
        cases input with
        | inl input => simp only [hashQueryCharge, Sum.elim_inl, zero_mul, le_refl]
        | inr input => exact freshMessageReuseCharge_le_count remaining key q log cache input
      rw [expectedQueryCharge_query_bind, expectedQueryCharge_query_bind, add_mul, ← ENNReal.tsum_mul_right]
      apply add_le_add hstep
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support ((romImpl input).run cache)
      · have hcache := simulateQ_romImpl_cache_le (OracleSpec.query input) cache result
          (by simpa only [simulateQ_spec_query] using hresult)
        have hnext := ih result.1 result.2 (hsigned.mono hcache)
        rw [uniformOccupancyIncrement_cache_stable remaining key cache result.2 log hcache hsigned] at hnext
        exact (mul_le_mul' le_rfl hnext).trans_eq (mul_assoc _ _ _).symm
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul, zero_mul]

theorem expected_fixedLog_linearReserve_le_count {α : Type} (remaining : Nat) (key : SecretKey) (q : Nat)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter cache key.root log) (computation : OracleComp OracleWorld α)
    (hcap : ∀ result ∈ support ((simulateQ romImpl computation).run cache), QueryCache.enncard result.2 ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run cache] * cachedLinearReuseReserve remaining key q result.2 log) ≤
      cachedLinearReuseReserve remaining key q cache log +
        expectedQueryCharge (freshMessageQueryCharge key.parameter) computation cache *
          (linearReuseQueryRate q * uniformOccupancyIncrement remaining key cache log) :=
  (expected_fixedLog_linearReserve_le remaining key q cache log hsigned computation hcap).trans
    (add_le_add le_rfl (expected_freshMessageReuseCharge_le_count remaining key q log computation cache hsigned))

theorem expected_emptyLog_linearReserve_le_count {α : Type} (key : SecretKey) (q : Nat)
    (cache : QueryCache HashSpec) (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none)
    (computation : OracleComp OracleWorld α)
    (hcap : ∀ result ∈ support ((simulateQ romImpl computation).run cache), QueryCache.enncard result.2 ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run cache] * cachedLinearReuseReserve signatureLimit key q result.2 []) ≤
      expectedQueryCharge (freshMessageQueryCharge key.parameter) computation cache * (linearReuseQueryRate q * (2 : ENNReal) ^ 21) := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hbound := expected_fixedLog_linearReserve_le_count signatureLimit key q cache [] hsigned computation hcap
  rw [cachedLinearReuseReserve_of_no_message signatureLimit key q cache [] hnone, zero_add] at hbound
  exact hbound.trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl (uniformOccupancyIncrement_empty_signatureLimit_le key cache)))

end SphincsSecurity.Concrete
