import SphincsSecurity.Proof.CachedMultiplicityPower

namespace SphincsSecurity.Concrete

open ENNReal

abbrev MixedMomentVector := Nat → Nat → ENNReal

noncomputable def mixedPowerLower (moments : MixedMomentVector) (power order : Nat) : ENNReal :=
  ∑ lower ∈ Finset.range power, (power.choose lower : ENNReal) * moments lower order

theorem mixedPowerLower_add (left right : MixedMomentVector) (power order : Nat) :
    mixedPowerLower (fun p o => left p o + right p o) power order =
      mixedPowerLower left power order + mixedPowerLower right power order := by
  simp only [mixedPowerLower, mul_add, Finset.sum_add_distrib]

theorem mixedPowerLower_mul (scalar : ENNReal) (moments : MixedMomentVector) (power order : Nat) :
    mixedPowerLower (fun p o => scalar * moments p o) power order = scalar * mixedPowerLower moments power order := by
  simp only [mixedPowerLower, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lower _
  ring

theorem mixedPowerLower_succ (moments : MixedMomentVector) (power order : Nat) :
    mixedPowerLower moments (power + 1) order =
      mixedPowerLower (fun p o => moments (p + 1) o) power order + moments power order + mixedPowerLower moments power order := by
  unfold mixedPowerLower
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.choose_zero_right, Nat.cast_one, one_mul]
  have hsum : (∑ lower ∈ Finset.range power, (power.choose (lower + 1) : ENNReal) * moments (lower + 1) order) +
      moments 0 order = (∑ lower ∈ Finset.range power, (power.choose lower : ENNReal) * moments lower order) + moments power order := by
    have h := Finset.sum_range_succ' (fun lower => (power.choose lower : ENNReal) * moments lower order) power
    rw [Finset.sum_range_succ] at h
    simpa only [Nat.choose_self, Nat.choose_zero_right, Nat.cast_one, one_mul] using h.symm
  calc
    _ = (∑ lower ∈ Finset.range power, (power.choose lower : ENNReal) * moments (lower + 1) order) +
        ((∑ lower ∈ Finset.range power, (power.choose (lower + 1) : ENNReal) * moments (lower + 1) order) + moments 0 order) := by ring
    _ = _ := by rw [hsum]; ring

noncomputable def mixedQueryEnvelope (arrival : ENNReal) (moments : MixedMomentVector) (power order : Nat) : ENNReal :=
  moments power order + arrival * mixedPowerLower moments power order

noncomputable def mixedSigningEnvelope (uniform reuse : ENNReal) (moments : MixedMomentVector) (power order : Nat) : ENNReal :=
  moments power order + uniform * (mixedPowerLower moments power order + moments power (order + 1) + mixedPowerLower moments power (order + 1)) +
    reuse * moments (power + 1) (order + 1)

theorem mixedSigning_query_commute (uniform reuse arrival : ENNReal) (moments : MixedMomentVector) (power order : Nat) :
    mixedSigningEnvelope uniform reuse (mixedQueryEnvelope arrival moments) power order =
      mixedQueryEnvelope arrival (mixedSigningEnvelope uniform reuse moments) power order +
        arrival * reuse * (moments power (order + 1) + mixedPowerLower moments power (order + 1)) := by
  unfold mixedSigningEnvelope mixedQueryEnvelope
  simp only [mixedPowerLower_add, mixedPowerLower_mul]
  rw [mixedPowerLower_succ]
  simp only [mixedPowerLower]
  ring

theorem mixedQuery_signing_le (uniform reuse arrival : ENNReal) (moments : MixedMomentVector) :
    mixedQueryEnvelope arrival (mixedSigningEnvelope uniform reuse moments) ≤
      mixedSigningEnvelope uniform reuse (mixedQueryEnvelope arrival moments) := by
  intro power order
  rw [mixedSigning_query_commute]
  exact le_self_add

theorem mixedPowerLower_mono : Monotone mixedPowerLower := by
  intro left right h power order
  exact Finset.sum_le_sum fun lower _ => mul_le_mul_right (h lower order) _

theorem mixedQueryEnvelope_mono (arrival : ENNReal) : Monotone (mixedQueryEnvelope arrival) := by
  intro left right h power order
  exact add_le_add (h power order) (mul_le_mul_right (mixedPowerLower_mono h power order) arrival)

theorem mixedSigningEnvelope_mono (uniform reuse : ENNReal) : Monotone (mixedSigningEnvelope uniform reuse) := by
  intro left right h power order
  exact add_le_add (add_le_add (h power order) (mul_le_mul_right
    (add_le_add (add_le_add (mixedPowerLower_mono h power order) (h power (order + 1)))
      (mixedPowerLower_mono h power (order + 1))) uniform)) (mul_le_mul_right (h (power + 1) (order + 1)) reuse)

end SphincsSecurity.Concrete
