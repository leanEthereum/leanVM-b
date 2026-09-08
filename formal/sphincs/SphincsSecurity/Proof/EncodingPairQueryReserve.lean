import SphincsSecurity.Proof.CollisionStructuralBudget
import SphincsSecurity.Proof.JointFailureCacheCap

namespace SphincsSecurity

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem validCacheEntries_card_le_cache (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    ((validCacheEntries cache).card : ENNReal) ≤ QueryCache.enncard cache := by
  rw [validCacheEntries, dif_pos hfinite]
  apply (Nat.cast_le.mpr Finset.card_image_le).trans
  apply (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans_eq
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  rw [Set.ncard_eq_toFinset_card _ hfinite]

theorem validCachePairIncrementCharge_le_cap (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (cap : Nat) (hcap : QueryCache.enncard cache ≤ cap) (input : HashInput) :
    validCachePairIncrementCharge cache input ≤ 2 * (cap : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  unfold validCachePairIncrementCharge
  split_ifs
  · exact mul_le_mul' (mul_le_mul' le_rfl ((validCacheEntries_card_le_cache cache hfinite).trans hcap)) le_rfl
  · exact zero_le

namespace Concrete

open FtsProbeSimulation (encodingHashCharge)

theorem encodingPairIncrementCharge_le_encoding_rate (key : SecretKey) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (cap : Nat) (hcap : QueryCache.enncard cache ≤ cap) (input : HashInput) :
    encodingPairIncrementCharge key cache input ≤
      encodingHashCharge key.parameter cache input * (2 * (cap : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) := by
  unfold encodingPairIncrementCharge encodingHashCharge
  split_ifs
  · simpa only [one_mul] using validCachePairIncrementCharge_le_cap cache hfinite cap hcap input
  · simp only [zero_mul, le_refl]

theorem encodingPairQueryRate_le_one (cap : Nat) (hcap : cap ≤ 2 ^ 127) :
    2 * (cap : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ ≤ 1 := by
  apply (mul_le_mul' (mul_le_mul' le_rfl (Nat.cast_le.mpr hcap)) le_rfl).trans_eq
  norm_num [Digest, digestBits, ENNReal.mul_inv_cancel]

namespace FtsProbeSimulation.JointOriginal

theorem expectedBeforeFailureOuterCharge_mono_of_cache_cap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (left right : QueryCache HashSpec → HashInput → ENNReal) (cap : ENNReal)
    (hle : ∀ cache, Finite cache → QueryCache.enncard cache ≤ cap → ∀ input, left cache input ≤ right cache input)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hit failed : Bool)
    (hcache : ∀ result ∈ support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed),
      QueryCache.enncard result.1.2.1.2 ≤ cap) :
    expectedBeforeFailureOuterCharge exception left parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedBeforeFailureOuterCharge exception right parameter root otsTable ftsTable computation frame cache hit failed := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => simp
  | query_bind input next ih =>
      have hbefore := runWithFailure_initial_cache_cap exception parameter root otsTable ftsTable (OracleSpec.query input >>= next)
        frame cache hit failed cap hcache
      rw [expectedBeforeFailureOuterCharge_query_bind, expectedBeforeFailureOuterCharge_query_bind]
      apply add_le_add
      · split_ifs
        · exact le_rfl
        · cases input with
          | inr message => exact le_rfl
          | inl world =>
              cases world with
              | inl n => exact le_rfl
              | inr hash => exact hle cache hfinite hbefore hash
      · apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed)
        · have hm := stepWithFailure_original_support exception parameter root otsTable ftsTable input frame cache hit failed result hr
          have hf := finite_cache_of_mem_support _ cache result.1.2.1.1 result.1.2.1.2
            (runExceptionMonitor_support_project exception _ cache hit hm) hfinite
          exact mul_le_mul' le_rfl (ih result.1.2.1.1 result.1.1 result.1.2.1.2 hf result.1.2.2 result.2
            (runWithFailure_tail_cache_cap exception parameter root otsTable ftsTable input next frame cache hit failed cap hcache result hr))
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

theorem expectedBeforeFailureOuterCharge_mul
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal) (rate : ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureOuterCharge exception (fun current input => charge current input * rate)
        parameter root otsTable ftsTable computation frame cache hit failed =
      expectedBeforeFailureOuterCharge exception charge parameter root otsTable ftsTable computation frame cache hit failed * rate := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedBeforeFailureOuterCharge_query_bind, expectedBeforeFailureOuterCharge_query_bind, add_mul, ← ENNReal.tsum_mul_right]
      congr 1
      · split_ifs
        · exact (zero_mul _).symm
        · cases input with
          | inr message => exact (zero_mul _).symm
          | inl world => cases world <;> simp only [outerHashQueryCharge, hashQueryCharge, Sum.elim_inl, Sum.elim_inr, zero_mul]
      · apply tsum_congr
        intro result
        rw [ih, mul_assoc]

theorem expected_outerEncodingPairs_le_reserve_rate
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit failed : Bool)
    (hcache : ∀ result ∈ support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed),
      QueryCache.enncard result.1.2.1.2 ≤ cap) :
    expectedBeforeFailureOuterCharge exception (encodingPairIncrementCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedBeforeFailureOuterCharge exception (encodingHashCharge parameter)
        parameter root otsTable ftsTable computation frame cache hit failed * (2 * (cap : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) := by
  rw [← expectedBeforeFailureOuterCharge_mul]
  exact expectedBeforeFailureOuterCharge_mono_of_cache_cap exception _ _ cap
    (fun current hc hbound input => encodingPairIncrementCharge_le_encoding_rate (secretKey parameter root otsTable ftsTable) current hc cap hbound input)
    parameter root otsTable ftsTable computation frame cache hfinite hit failed hcache

end FtsProbeSimulation.JointOriginal
end Concrete
end SphincsSecurity
