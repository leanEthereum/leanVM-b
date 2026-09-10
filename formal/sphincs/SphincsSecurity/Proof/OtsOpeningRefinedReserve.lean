import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsOpeningQueryReserve
import SphincsSecurity.Proof.OtsProbeRootQueryReserve

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def otsOpeningRefinedQueryReserve (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : ℝ≥0∞ :=
  otsOpeningQueryReserve secretKey cache input + 1 / 3

theorem sampledQueryCharge_add
    (left right : SecretKey → QueryCache HashSpec → HashInput → ℝ≥0∞) (adversary : Adversary) :
    sampledQueryCharge (fun secretKey cache input => left secretKey cache input + right secretKey cache input) adversary =
      sampledQueryCharge left adversary + sampledQueryCharge right adversary := by
  unfold sampledQueryCharge
  simp_rw [expectedQueryCharge_add, mul_add, ENNReal.tsum_add]

theorem sampledQueryCharge_le_const
    (charge : SecretKey → QueryCache HashSpec → HashInput → ℝ≥0∞) (bound : ℝ≥0∞)
    (hcharge : ∀ secretKey cache input, charge secretKey cache input ≤ bound)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) :
    sampledQueryCharge charge adversary ≤ bound * q := by
  unfold sampledQueryCharge
  calc
    _ ≤ ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] * (bound * q) := by
      apply ENNReal.tsum_le_tsum
      intro secrets
      by_cases hsecrets : secrets ∈ support sampleSecrets
      · obtain ⟨hparameter, hots, hfts⟩ := secrets.support_components hsecrets
        exact mul_le_mul' le_rfl (expectedQueryCharge_le_queryBound _ bound (hcharge _)
          (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) q
          (isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts) ∅)
      · simp [probOutput_eq_zero_of_not_mem_support hsecrets]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one

theorem structural_add_refined_openingQueryReserve (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) :
    (TightEncoding.refinedStructuralEncodingQueryCharge secretKey cache input +
      ftsOpeningQueryReserve secretKey cache input) + otsOpeningRefinedQueryReserve secretKey cache input = 10 / 3 := by
  unfold otsOpeningRefinedQueryReserve
  rw [add_assoc, ← add_assoc (ftsOpeningQueryReserve secretKey cache input), openingQueryReserve_add,
    ← add_assoc, structural_add_residual_queryCharge]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

theorem sampled_structural_add_refined_openingQueryReserve_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) :
    (sampledQueryCharge TightEncoding.refinedStructuralEncodingQueryCharge adversary +
      sampledQueryCharge ftsOpeningQueryReserve adversary) +
      sampledQueryCharge otsOpeningRefinedQueryReserve adversary ≤ (10 / 3 : ℝ≥0∞) * q := by
  rw [← sampledQueryCharge_add, ← sampledQueryCharge_add]
  exact sampledQueryCharge_le_const _ _
    (fun secretKey cache input => (structural_add_refined_openingQueryReserve secretKey cache input).le)
    adversary q hq

theorem otsOpeningRefinedQueryReserve_ge_four_thirds_of_one_le
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (hreserve : 1 ≤ otsOpeningQueryReserve secretKey cache input) :
    4 / 3 ≤ otsOpeningRefinedQueryReserve secretKey cache input := by
  have heq : (4 / 3 : ℝ≥0∞) = 1 + 1 / 3 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num
  rw [heq]
  exact add_le_add hreserve le_rfl

theorem otsOpeningRefinedQueryReserve_ge_four_thirds_of_atOtsPosition
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) (position : Position)
    (hat : AtPosition secretKey.parameter input position) (hots : OtsProbeSimulation.IsOtsPosition position) :
    4 / 3 ≤ otsOpeningRefinedQueryReserve secretKey cache input :=
  otsOpeningRefinedQueryReserve_ge_four_thirds_of_one_le secretKey cache input
    (otsOpeningQueryReserve_ge_one_of_atOtsPosition secretKey cache input position hat hots)

theorem otsOpeningRefinedQueryReserve_ge_four_thirds_of_encodingMessageSettled
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) (position : EncodingPosition)
    (hat : AtEncodingPosition secretKey.parameter input position)
    (hsettled : EncodingMessageSettledAt cache secretKey position) :
    4 / 3 ≤ otsOpeningRefinedQueryReserve secretKey cache input := by
  apply otsOpeningRefinedQueryReserve_ge_four_thirds_of_one_le
  rw [otsOpeningQueryReserve_atEncodingPosition secretKey cache input position hat]
  simp only [hsettled, if_true]
  split_ifs <;> norm_num

end SphincsSecurity.Concrete
