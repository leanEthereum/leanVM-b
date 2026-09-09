import SphincsSecurity.Proof.PairedHiddenMiss
import SphincsSecurity.Proof.EndpointPreimageDensity
import SphincsSecurity.Proof.EncodingProbability

namespace SphincsSecurity.Concrete.HiddenLabelProbe

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

noncomputable def law (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) : PMF ((Coordinate → Digest) × HashOutput) :=
  (uniformTable allowed ha).bind fun labels =>
    (PMF.uniformOfFintype HashOutput).map fun answer => (labels, answer)

def Match (child parent : Coordinate) (candidate : Digest)
    (result : (Coordinate → Digest) × HashOutput) : Prop :=
  result.1 child = candidate ∨ truncateHash result.2 = result.1 parent

theorem law_apply (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (labels : Coordinate → Digest) (answer : HashOutput) :
    law allowed ha (labels, answer) = uniformTable allowed ha labels * PMF.uniformOfFintype HashOutput answer := by
  exact EndpointPreimageDensity.bind_pair_apply _ _ _ _

theorem surviving_mass (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (hne : child ≠ parent)
    (candidate : Digest) (answer : HashOutput)
    (hc : ((allowed child).erase candidate).Nonempty)
    (hp : ((allowed parent).erase (truncateHash answer)).Nonempty) (labels : Coordinate → Digest) :
    (if ¬Match child parent candidate (labels, answer) then law allowed ha (labels, answer) else 0) =
      PMF.uniformOfFintype HashOutput answer *
        (((((allowed child).erase candidate).card : ENNReal) / (allowed child).card *
          (((allowed parent).erase (truncateHash answer)).card : ENNReal) / (allowed parent).card) *
          uniformTable (pairedMissAllowed allowed child candidate parent (truncateHash answer))
            (pairedMissAllowed_nonempty allowed ha child parent hne candidate (truncateHash answer) hc hp) labels) := by
  rw [law_apply]
  have hcondition : ¬Match child parent candidate (labels, answer) ↔
      labels child ≠ candidate ∧ labels parent ≠ truncateHash answer := by
    simp only [Match, not_or, ne_comm]
  simp only [hcondition]
  rw [show (if labels child ≠ candidate ∧ labels parent ≠ truncateHash answer then
      uniformTable allowed ha labels * PMF.uniformOfFintype HashOutput answer else 0) =
      PMF.uniformOfFintype HashOutput answer *
        (if labels child ≠ candidate ∧ labels parent ≠ truncateHash answer then uniformTable allowed ha labels else 0) by
    split <;> simp only [zero_mul, mul_comm]]
  rw [uniformTable_paired_miss_mass allowed ha child parent hne candidate (truncateHash answer) hc hp]

theorem prob_truncate_eq (target : Digest) :
    Pr[fun answer => truncateHash answer = target | PMF.uniformOfFintype HashOutput] =
      (Fintype.card Digest : ENNReal)⁻¹ := by
  simpa only [probEvent_eq_tsum_ite, probOutput_uniformSample, PMF.probOutput_eq_apply,
    PMF.uniformOfFintype_apply] using probEvent_uniform_truncateHash_eq target

theorem prob_truncate_ne (target : Digest) :
    Pr[fun answer => truncateHash answer ≠ target | PMF.uniformOfFintype HashOutput] =
      1 - (Fintype.card Digest : ENNReal)⁻¹ := by
  have h := probEvent_compl (PMF.uniformOfFintype HashOutput) (fun answer => truncateHash answer = target)
  rw [prob_truncate_eq, probFailure_of_liftM_PMF, tsub_zero] at h
  exact ENNReal.eq_sub_of_add_eq' (by finiteness) (by rwa [add_comm])

theorem prob_survive (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (candidate : Digest) :
    Pr[fun result => ¬Match child parent candidate result | law allowed ha] =
      Pr[fun labels => labels child ≠ candidate | uniformTable allowed ha] *
        (1 - (Fintype.card Digest : ENNReal)⁻¹) := by
  change Pr[fun result => ¬Match child parent candidate result |
    (uniformTable allowed ha) >>= fun labels =>
      (fun answer => (labels, answer)) <$> PMF.uniformOfFintype HashOutput] = _
  rw [probEvent_bind_eq_tsum]
  have hinner (labels : Coordinate → Digest) :
      Pr[(fun result => ¬Match child parent candidate result) ∘ (fun answer => (labels, answer)) |
        PMF.uniformOfFintype HashOutput] =
      if labels child ≠ candidate then 1 - (Fintype.card Digest : ENNReal)⁻¹ else 0 := by
    by_cases hc : labels child = candidate
    · simp [Function.comp_def, Match, hc]
    · simpa only [Function.comp_def, Match, hc, false_or, if_pos hc] using prob_truncate_ne (labels parent)
  simp only [probEvent_map, hinner, PMF.probOutput_eq_apply, mul_ite, mul_zero]
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  simp only [PMF.probOutput_eq_apply, ite_mul, zero_mul]

theorem prob_child_miss (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child : Coordinate) (candidate : Digest) :
    Pr[fun labels => labels child ≠ candidate | uniformTable allowed ha] =
      1 - Pr[fun labels => labels child = candidate | uniformTable allowed ha] := by
  have h := probEvent_compl (uniformTable allowed ha) (fun labels => labels child = candidate)
  rw [probFailure_of_liftM_PMF, tsub_zero] at h
  exact ENNReal.eq_sub_of_add_eq' (by simp) (by rwa [add_comm])

theorem prob_child_hit_le (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child : Coordinate) (candidate : Digest)
    (minimum : Nat) (hmin : minimum ≤ (allowed child).card) :
    Pr[fun labels => labels child = candidate | uniformTable allowed ha] ≤ (minimum : ENNReal)⁻¹ := by
  rw [probEvent_uniformTable_eq]
  split
  · exact ENNReal.inv_le_inv.mpr (by exact_mod_cast hmin)
  · exact bot_le

theorem prob_survive_ge (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (candidate : Digest)
    (minimum : Nat) (hmin : minimum ≤ (allowed child).card) :
    (1 - (minimum : ENNReal)⁻¹) ^ 2 ≤
      Pr[fun result => ¬Match child parent candidate result | law allowed ha] := by
  have hspace : minimum ≤ Fintype.card Digest := hmin.trans (Finset.card_le_univ _)
  rw [prob_survive, prob_child_miss, pow_two]
  exact mul_le_mul' (tsub_le_tsub_left (prob_child_hit_le allowed ha child candidate minimum hmin) _)
    (tsub_le_tsub_left (ENNReal.inv_le_inv.mpr (by exact_mod_cast hspace)) _)

theorem prob_match_le (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (candidate : Digest)
    (minimum : Nat) (hmin : minimum ≤ (allowed child).card) :
    Pr[Match child parent candidate | law allowed ha] ≤ 1 - (1 - (minimum : ENNReal)⁻¹) ^ 2 := by
  have h := probEvent_compl (law allowed ha) (Match child parent candidate)
  rw [probFailure_of_liftM_PMF, tsub_zero] at h
  have heq := ENNReal.eq_sub_of_add_eq' (by simp) h
  rw [heq]
  exact tsub_le_tsub_left (prob_survive_ge allowed ha child parent candidate minimum hmin) _

theorem prob_match_le_rounds (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (candidate : Digest)
    (rounds : Nat) (hmin : 2 ^ digestBits - rounds ≤ (allowed child).card) :
    Pr[Match child parent candidate | law allowed ha] ≤
      1 - (1 - ((2 ^ digestBits - rounds : Nat) : ENNReal)⁻¹) ^ 2 :=
  prob_match_le allowed ha child parent candidate _ hmin

end SphincsSecurity.Concrete.HiddenLabelProbe
