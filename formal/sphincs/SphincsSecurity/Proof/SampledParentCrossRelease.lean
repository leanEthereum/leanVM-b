import SphincsSecurity.Proof.ParentCrossReleasePairs
import SphincsSecurity.Proof.SampledSigningEncodingPayment

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable expectedBeforeFailureCharge retainedComputation
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledBeforeFailureParentCharge (charge : SecretKey → QueryCache HashSpec → HashInput → ENNReal)
    (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        ∑' initial, Pr[= initial | initializeRoot parameter table (curryFtsTableEquiv ftsSecret) q fuel] *
          expectedBeforeFailureCharge (parentException parameter table (curryFtsTableEquiv ftsSecret))
            (charge (secretKey parameter default table (curryFtsTableEquiv ftsSecret)))
            parameter initial.2.1 table (curryFtsTableEquiv ftsSecret)
            (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone

private theorem expected_le_constant {m : Type → Type} [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    (computation : m α) (weight : α → ENNReal) (bound : ENNReal)
    (h : ∀ result ∈ support computation, weight result ≤ bound) :
    (∑' result, Pr[= result | computation] * weight result) ≤ bound := by
  calc
    _ ≤ ∑' result, Pr[= result | computation] * bound := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support computation
      · exact mul_le_mul' le_rfl (h result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem sampledBeforeFailureParentCharge_le_of_cache_cap
    (charge : SecretKey → QueryCache HashSpec → HashInput → ENNReal)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) (bound : ENNReal)
    (hlocal : ∀ (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
      (root : Digest) (frame : Option Frame) (cache : QueryCache HashSpec), Finite cache → ∀ failed : Bool,
      (∀ result ∈ support (runWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
        (retainedComputation adversary parameter root q) frame cache false failed), QueryCache.enncard result.1.2.1.2 ≤ q) →
      expectedBeforeFailureCharge (parentException parameter otsTable ftsTable) (charge (secretKey parameter default otsTable ftsTable))
        parameter root otsTable ftsTable (retainedComputation adversary parameter root q) frame cache false failed ≤ bound) :
    sampledBeforeFailureParentCharge charge adversary q fuel ≤ bound := by
  unfold sampledBeforeFailureParentCharge
  apply expected_le_constant
  intro parameter hp
  apply expected_le_constant
  intro ftsSecret hfts
  apply expected_le_constant
  intro table _
  apply expected_le_constant
  intro initial hi
  have ha := initializeRoot_original_support parameter table (curryFtsTableEquiv ftsSecret) q fuel initial hi
  have hf := finite_cache_of_mem_support _ ∅ initial.2.1 initial.2.2 ha finite_empty
  apply hlocal parameter table (curryFtsTableEquiv ftsSecret) initial.2.1 initial.1 initial.2.2 hf initial.1.isNone
  intro result hr
  apply runRetainedWithFailure_cache_le_queryBound _ adversary q hq parameter hp table (curryFtsTableEquiv ftsSecret) hfts fuel result
  rw [runRetainedWithFailure, mem_support_bind_iff]
  exact ⟨initial, hi, hr⟩

noncomputable def sampledCrossParentReleaseCharge (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  sampledBeforeFailureParentCharge crossFtsParentReleaseCharge adversary q fuel

theorem sampledDirectParentReleaseCharge_eq_parentCharge (adversary : Adversary) (q fuel : Nat) :
    sampledDirectParentReleaseCharge adversary q fuel = sampledBeforeFailureParentCharge directFtsParentReleaseCharge adversary q fuel := rfl

theorem sampledLocalizedParentReleaseCharge_eq_direct_add_cross (adversary : Adversary) (q fuel : Nat) :
    sampledLocalizedParentReleaseCharge adversary q fuel =
      sampledDirectParentReleaseCharge adversary q fuel + sampledCrossParentReleaseCharge adversary q fuel := by
  unfold sampledLocalizedParentReleaseCharge initializedLocalizedParentReleaseCharge
    sampledDirectParentReleaseCharge initializedDirectParentReleaseCharge sampledCrossParentReleaseCharge sampledBeforeFailureParentCharge
  simp only [localizedFtsParentReleaseCharge_eq_direct_add_cross, expectedBeforeFailureCharge_add, mul_add, ENNReal.tsum_add]

theorem sampledDirectParentReleaseCharge_le_queryBound
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledDirectParentReleaseCharge adversary q fuel ≤ q := by
  rw [sampledDirectParentReleaseCharge_eq_parentCharge]
  apply sampledBeforeFailureParentCharge_le_of_cache_cap _ adversary q hq fuel q
  intro parameter table ftsTable root frame cache hf failed hc
  exact expectedBeforeFailureDirectParentCharge_le_cache_cap (parentException parameter table ftsTable)
    (secretKey parameter default table ftsTable) (fun position => ¬ OtsProbeSimulation.IsOtsPosition position)
    parameter root table ftsTable _ frame cache hf false failed q hc

theorem sampledCrossParentReleaseCharge_le_quadratic
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledCrossParentReleaseCharge adversary q fuel ≤ (q : ENNReal) * q * (Fintype.card Digest : ENNReal)⁻¹ := by
  have hcard : (Fintype.card Digest : ENNReal) = ((2 ^ digestBits : Nat) : ENNReal) := by
    norm_num [Digest, Fintype.card_fin, Nat.card_eq_fintype_card]
  rw [hcard, mul_assoc]
  apply sampledBeforeFailureParentCharge_le_of_cache_cap _ adversary q hq fuel _
  intro parameter table ftsTable root frame cache hf failed hc
  exact expectedBeforeFailureCrossParentCharge_le_cache_cap (parentException parameter table ftsTable)
    (secretKey parameter default table ftsTable) parameter root table ftsTable _ frame cache hf false failed q hc

theorem sampledDirectParentReleaseCharge_ne_top
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledDirectParentReleaseCharge adversary q fuel ≠ ⊤ :=
  ne_top_of_le_ne_top (by finiteness) (sampledDirectParentReleaseCharge_le_queryBound adversary q hq fuel)

theorem sampledCrossParentReleaseCharge_le_pairs
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledCrossParentReleaseCharge adversary q fuel ≤ (q.choose 2 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  have hcard : (Fintype.card Digest : ENNReal) = ((2 ^ digestBits : Nat) : ENNReal) := by
    norm_num [Digest, Fintype.card_fin, Nat.card_eq_fintype_card]
  rw [hcard]
  apply sampledBeforeFailureParentCharge_le_of_cache_cap _ adversary q hq fuel _
  intro parameter table ftsTable root frame cache hf failed hc
  exact expectedBeforeFailureCrossParentCharge_le_pairs (parentException parameter table ftsTable)
    (secretKey parameter default table ftsTable) parameter root table ftsTable _ frame cache hf false failed q hc

theorem sampledCrossParentReleaseCharge_ne_top
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledCrossParentReleaseCharge adversary q fuel ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (by finiteness)
    (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)))
      (sampledCrossParentReleaseCharge_le_quadratic adversary q hq fuel)

noncomputable def sampledParentFundingAfterDirectRelease (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  sampledFreshParentReserveCharge adversary q fuel - sampledDirectParentReleaseCharge adversary q fuel

theorem sampledParentFundingAfterDirectRelease_add_direct (adversary : Adversary) (q fuel : Nat) :
    sampledParentFundingAfterDirectRelease adversary q fuel + sampledDirectParentReleaseCharge adversary q fuel =
      sampledFreshParentReserveCharge adversary q fuel :=
  tsub_add_cancel_of_le (le_add_self.trans (sampled_pending_discard_directRelease_le_funding adversary q fuel))

theorem sampled_pending_discard_le_fundingAfterDirectRelease
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledPendingParentCount adversary q fuel + sampledTerminalParentDiscard adversary q fuel + sampledSharedParentDiscard adversary q fuel ≤
      sampledParentFundingAfterDirectRelease adversary q fuel := by
  apply ENNReal.le_of_add_le_add_right (sampledDirectParentReleaseCharge_ne_top adversary q hq fuel)
  rw [sampledParentFundingAfterDirectRelease_add_direct]
  exact sampled_pending_discard_directRelease_le_funding adversary q fuel

theorem sampledFreshParentReserveCharge_le_queryBound
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledFreshParentReserveCharge adversary q fuel ≤ q := by
  change sampledBeforeFailureParentCharge freshFtsParentReserveCharge adversary q fuel ≤ q
  apply sampledBeforeFailureParentCharge_le_of_cache_cap _ adversary q hq fuel q
  intro parameter table ftsTable root frame cache hf failed hc
  let raw := simulateQ (expandedAdversaryImpl (secretKey parameter root table ftsTable)) (retainedComputation adversary parameter root q)
  have hrawcap := runWithFailure_original_cache_cap (parentException parameter table ftsTable)
    parameter root table ftsTable (retainedComputation adversary parameter root q) frame cache false failed q hc
  apply (expectedBeforeFailureCharge_le_preExceptionCharge (parentException parameter table ftsTable) _
    parameter root table ftsTable _ frame cache false failed).trans
  apply (expectedPreExceptionCharge_le_queryCharge (parentException parameter table ftsTable) _ raw cache false).trans
  apply (expectedQueryCharge_mono _ _ (freshParentReserveCharge_le_freshCache parameter
    (secretKey parameter default table ftsTable).otsSecret (secretKey parameter default table ftsTable).ftsSecret _) raw cache).trans
  apply (le_add_self.trans_eq (expected_simulateQ_enncard raw cache).symm).trans
  exact expected_le_constant _ _ q hrawcap

theorem sampledFreshParentReserveCharge_ne_top
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledFreshParentReserveCharge adversary q fuel ≠ ⊤ :=
  ne_top_of_le_ne_top (by finiteness) (sampledFreshParentReserveCharge_le_queryBound adversary q hq fuel)

theorem sampledTerminalParentDiscard_ne_top
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledTerminalParentDiscard adversary q fuel ≠ ⊤ :=
  ne_top_of_le_ne_top (sampledFreshParentReserveCharge_ne_top adversary q hq fuel)
    ((le_add_self.trans le_self_add).trans (le_self_add.trans (sampled_pending_discard_directRelease_le_funding adversary q fuel)))

noncomputable def sampledNetParentFunding (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  2 * sampledParentFundingAfterDirectRelease adversary q fuel - sampledTerminalParentDiscard adversary q fuel

theorem sampledNetParentFunding_add_terminal
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledNetParentFunding adversary q fuel + sampledTerminalParentDiscard adversary q fuel =
      2 * sampledParentFundingAfterDirectRelease adversary q fuel := by
  apply tsub_add_cancel_of_le
  apply ((le_add_self.trans le_self_add).trans (sampled_pending_discard_le_fundingAfterDirectRelease adversary q hq fuel)).trans
  exact le_mul_of_one_le_left' (by norm_num)

theorem sampledNetParentFunding_ge_pending_discard
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    2 * sampledPendingParentCount adversary q fuel + sampledTerminalParentDiscard adversary q fuel +
      2 * sampledSharedParentDiscard adversary q fuel ≤ sampledNetParentFunding adversary q fuel := by
  apply ENNReal.le_of_add_le_add_right (sampledTerminalParentDiscard_ne_top adversary q hq fuel)
  rw [sampledNetParentFunding_add_terminal adversary q hq fuel]
  convert mul_le_mul' (le_refl (2 : ENNReal)) (sampled_pending_discard_le_fundingAfterDirectRelease adversary q hq fuel) using 1 <;> first | rfl | ring

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
