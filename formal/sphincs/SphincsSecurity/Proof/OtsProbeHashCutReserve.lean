import SphincsSecurity.Proof.OtsProbeWeightedReserve

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

noncomputable def sampledHashCutUnresolvedStartRisk (adversary : Adversary) (fuel q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑ ordinal ∈ Finset.range q, Pr[LiveUnresolvedStartHit (hashCutCandidate parameter) |
        sampledCanonicalHashCut parameter ftsSecret fuel
          (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩) ordinal]

private theorem expected_affine (computation : ProbComp α) (cost : α → ENNReal) (factor error : ENNReal) :
    (∑' result, Pr[= result | computation] * (cost result * factor + error)) =
      (∑' result, Pr[= result | computation] * cost result) * factor + error := by
  simp_rw [mul_add, ← mul_assoc]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right,
    tsum_probOutput_eq_one' (by simp), one_mul]

theorem sampledHashCutUnresolvedStartRisk_le_charge
    (adversary : Adversary) (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    sampledHashCutUnresolvedStartRisk adversary fuel q ≤
      sampledCanonicalCharge unresolvedStartOuterCharge adversary fuel *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  rw [sampledCanonicalCharge_eq_accumulated]
  unfold sampledHashCutUnresolvedStartRisk
  rw [← expected_affine]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  rw [← expected_affine]
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  exact mul_le_mul' le_rfl (sum_hashCut_unresolvedStart_le_accumulatedCharge parameter ftsSecret fuel q
    (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩) hq)

theorem sampledHashCutUnresolvedStartRisk_add_components_le_refinedReserve
    (adversary : Adversary) (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    sampledHashCutUnresolvedStartRisk adversary fuel q +
      sampledCanonicalCharge unresolvedPositionOuterCharge adversary fuel * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
      sampledCanonicalCharge materializedOuterCandidateCharge adversary fuel *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) ≤
      sampledQueryCharge otsOpeningRefinedQueryReserve adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ (sampledCanonicalCharge unresolvedStartOuterCharge adversary fuel *
          ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) +
          (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) +
        sampledCanonicalCharge unresolvedPositionOuterCharge adversary fuel * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        sampledCanonicalCharge materializedOuterCandidateCharge adversary fuel *
          ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :=
      add_le_add (add_le_add (sampledHashCutUnresolvedStartRisk_le_charge adversary fuel q hq) le_rfl) le_rfl
    _ = (sampledCanonicalCharge unresolvedStartOuterCharge adversary fuel * (4 / 3) +
          sampledCanonicalCharge unresolvedPositionOuterCharge adversary fuel +
          sampledCanonicalCharge materializedOuterCandidateCharge adversary fuel * (4 / 3)) *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by ring
    _ ≤ _ := add_le_add (mul_le_mul' (sampledCanonical_components_le_refinedReserve adversary fuel) le_rfl) le_rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
