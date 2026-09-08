import SphincsSecurity.Proof.SampledEncodingPairReserve
import SphincsSecurity.Proof.SigningEncodingPairPayment

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
attribute [local irreducible] expectedBeforeFailureSigningCharge retainedComputation
set_option backward.isDefEq.respectTransparency false

theorem sampledSigningEncodingPairCharge_le_reserve_rate
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledSigningEncodingPairCharge adversary q fuel ≤
      sampledSigningNonEncodingReserve adversary q fuel * (2 * (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) := by
  unfold sampledSigningEncodingPairCharge sampledSigningNonEncodingReserve
  simp only [← ENNReal.tsum_mul_right, mul_assoc]
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hp : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    by_cases hfts : ftsSecret ∈ support sampleFtsSecrets
    · apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro table
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro initial
      by_cases hi : initial ∈ support (initializeRoot parameter table (curryFtsTableEquiv ftsSecret) q fuel)
      · apply mul_le_mul' le_rfl
        have ha := initializeRoot_original_support parameter table (curryFtsTableEquiv ftsSecret) q fuel initial hi
        have hf := finite_cache_of_mem_support _ ∅ initial.2.1 initial.2.2 ha finite_empty
        have hc : ∀ result ∈ support (runWithFailure (parentException parameter table (curryFtsTableEquiv ftsSecret))
            parameter initial.2.1 table (curryFtsTableEquiv ftsSecret) (retainedComputation adversary parameter initial.2.1 q)
              initial.1 initial.2.2 false initial.1.isNone), QueryCache.enncard result.1.2.1.2 ≤ q := by
          intro result hr
          apply runRetainedWithFailure_cache_le_queryBound _ adversary q hq parameter hp table (curryFtsTableEquiv ftsSecret) hfts fuel result
          rw [runRetainedWithFailure, mem_support_bind_iff]
          exact ⟨initial, hi, hr⟩
        have hs : encodingPairIncrementCharge (secretKey parameter default table (curryFtsTableEquiv ftsSecret)) =
            encodingPairIncrementCharge (secretKey parameter initial.2.1 table (curryFtsTableEquiv ftsSecret)) := rfl
        simpa only [mul_assoc, hs] using expected_signingEncodingPairs_le_reserved_rate
          (parentException parameter table (curryFtsTableEquiv ftsSecret)) parameter initial.2.1
          table (curryFtsTableEquiv ftsSecret) q _ initial.1 initial.2.2 hf false initial.1.isNone hc
      · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]
    · rw [probOutput_eq_zero_of_not_mem_support hfts, zero_mul, zero_mul]
  · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]

theorem sampledSigningEncodingPairCharge_le_reserve
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledSigningEncodingPairCharge adversary q fuel ≤ sampledSigningNonEncodingReserve adversary q fuel :=
  (sampledSigningEncodingPairCharge_le_reserve_rate adversary q hq fuel).trans
    (mul_le_of_le_one_right' (encodingPairQueryRate_le_one q hqMax))

noncomputable def sampledSigningNonEncodingReserveAfterPairs (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  sampledSigningNonEncodingReserve adversary q fuel - sampledSigningEncodingPairCharge adversary q fuel

theorem sampledSigningNonEncodingReserveAfterPairs_add_pairs
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledSigningNonEncodingReserveAfterPairs adversary q fuel + sampledSigningEncodingPairCharge adversary q fuel =
      sampledSigningNonEncodingReserve adversary q fuel :=
  tsub_add_cancel_of_le (sampledSigningEncodingPairCharge_le_reserve adversary q hq hqMax fuel)

theorem sampledSigningEncodingPairCharge_scaled_ne_top
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledSigningEncodingPairCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≠ ⊤ := by
  have hfinite : (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (by simp) (by norm_num)
    · apply ENNReal.inv_ne_top.mpr
      exact_mod_cast Fintype.card_ne_zero (α := Digest)
  have h := sampledBeforeFailureEncodingPairCharge_scaled_le_127 adversary q hq hqMax fuel
  rw [sampledBeforeFailureEncodingPairCharge_eq_outer_add_signing, add_mul] at h
  exact ne_top_of_le_ne_top hfinite (le_add_self.trans h)

theorem sampledSigningNonEncodingReserveAfterPairs_scaled_ge_fraction
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    (1 - 2 * (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) *
        sampledSigningNonEncodingReserve adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤
      sampledSigningNonEncodingReserveAfterPairs adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ := by
  let rate := 2 * (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹
  have h := add_le_add (le_refl ((1 - rate) * sampledSigningNonEncodingReserve adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹))
    (mul_le_mul' (sampledSigningEncodingPairCharge_le_reserve_rate adversary q hq fuel) (le_refl (Fintype.card Digest : ENNReal)⁻¹))
  have heq : (1 - rate) * sampledSigningNonEncodingReserve adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledSigningNonEncodingReserve adversary q fuel * rate * (Fintype.card Digest : ENNReal)⁻¹ =
        sampledSigningNonEncodingReserve adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ := by
    calc
      _ = ((1 - rate) + rate) * sampledSigningNonEncodingReserve adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ := by ring
      _ = _ := by rw [tsub_add_cancel_of_le (encodingPairQueryRate_le_one q hqMax), one_mul]
  rw [heq] at h
  apply ENNReal.le_of_add_le_add_right (sampledSigningEncodingPairCharge_scaled_ne_top adversary q hq hqMax fuel)
  conv_rhs => rw [← add_mul, sampledSigningNonEncodingReserveAfterPairs_add_pairs adversary q hq hqMax fuel]
  exact h

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
