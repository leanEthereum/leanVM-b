import SphincsSecurity.Proof.BeforeFailureSigningSurvival
import SphincsSecurity.Proof.SampledSigningEncodingPayment
import SphincsSecurity.Proof.SecurityJointBeforeFailureBound

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
attribute [local irreducible] expectedBeforeFailureSigningCharge expectedBeforeFailureSigningSurvivalCredit retainedComputation
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledSigningSurvivalCredit (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        ∑' initial, Pr[= initial | initializeRoot parameter table (curryFtsTableEquiv ftsSecret) q fuel] *
          expectedBeforeFailureSigningSurvivalCredit (parentException parameter table (curryFtsTableEquiv ftsSecret))
            parameter initial.2.1 table (curryFtsTableEquiv ftsSecret)
            (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone

theorem sampledSigningEncodingPairs_add_survival_le_reserved
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledSigningEncodingPairCharge adversary q fuel + sampledSigningSurvivalCredit adversary q fuel ≤
      sampledSigningNonEncodingReserve adversary q fuel := by
  unfold sampledSigningEncodingPairCharge sampledSigningSurvivalCredit sampledSigningNonEncodingReserve
  simp only [← ENNReal.tsum_add, ← mul_add]
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
        simpa only [hs] using expected_beforeFailureEncodingPairs_add_survival_le_reserved
          (parentException parameter table (curryFtsTableEquiv ftsSecret)) parameter initial.2.1
          table (curryFtsTableEquiv ftsSecret) q hqMax _ initial.1 initial.2.2 hf false initial.1.isNone hc
      · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]
    · rw [probOutput_eq_zero_of_not_mem_support hfts, zero_mul, zero_mul]
  · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]

theorem sampledSigningNonEncodingReserve_le_twice_queryBound
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledSigningNonEncodingReserve adversary q fuel ≤ 2 * (q : ENNReal) := by
  have hsign := le_add_self.trans (sampledBeforeFailureStructural_add_signingNonEncoding_le adversary q fuel)
  have hmessage : sampledBeforeFailureHashCharge nonMessageHashCharge adversary q fuel ≤ q := by
    apply le_trans ?_ (sampledBeforeFailureRestHashCharge_le_queryBound adversary q hq fuel)
    rw [sampledBeforeFailureRestHashCharge_eq_nonMessage_add_message]
    exact le_self_add
  have hselected : sampledBeforeFailureSelectedCharge NonMessageNonSecretHashInput adversary q fuel ≤ q := by
    apply (sampledBeforeFailureSelectedCharge_le_erased NonMessageNonSecretHashInput adversary q fuel).trans
    apply le_trans ?_ (sampledJointNonSecretQueryCharge_le_queryBound adversary q)
    rw [sampledJointNonSecretQueryCharge_eq_nonMessage_add_message]
    exact le_self_add
  exact hsign.trans ((add_le_add hmessage hselected).trans_eq (two_mul _).symm)

theorem sampledSigningNonEncodingReserve_ne_top
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledSigningNonEncodingReserve adversary q fuel ≠ ⊤ :=
  ne_top_of_le_ne_top (by finiteness) (sampledSigningNonEncodingReserve_le_twice_queryBound adversary q hq fuel)

theorem sampledSigningSurvivalCredit_le_afterPairs
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledSigningSurvivalCredit adversary q fuel ≤ sampledSigningNonEncodingReserveAfterPairs adversary q fuel := by
  have hp := ne_top_of_le_ne_top (sampledSigningNonEncodingReserve_ne_top adversary q hq fuel)
    (sampledSigningEncodingPairCharge_le_reserve adversary q hq hqMax fuel)
  apply ENNReal.le_of_add_le_add_right hp
  rw [sampledSigningNonEncodingReserveAfterPairs_add_pairs adversary q hq hqMax fuel, add_comm]
  exact sampledSigningEncodingPairs_add_survival_le_reserved adversary q hq hqMax fuel

noncomputable def sampledSigningNonEncodingReserveAfterSurvival (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  sampledSigningNonEncodingReserveAfterPairs adversary q fuel - sampledSigningSurvivalCredit adversary q fuel

theorem sampledSigningNonEncodingReserveAfterSurvival_add_credit
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledSigningNonEncodingReserveAfterSurvival adversary q fuel + sampledSigningSurvivalCredit adversary q fuel =
      sampledSigningNonEncodingReserveAfterPairs adversary q fuel :=
  tsub_add_cancel_of_le (sampledSigningSurvivalCredit_le_afterPairs adversary q hq hqMax fuel)

theorem sampledSigningSurvivalCredit_scaled_ne_top
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledSigningSurvivalCredit adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≠ ⊤ := by
  apply ENNReal.mul_ne_top
  · exact ne_top_of_le_ne_top (sampledSigningNonEncodingReserve_ne_top adversary q hq fuel)
      (le_add_self.trans (sampledSigningEncodingPairs_add_survival_le_reserved adversary q hq hqMax fuel))
  · exact ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
