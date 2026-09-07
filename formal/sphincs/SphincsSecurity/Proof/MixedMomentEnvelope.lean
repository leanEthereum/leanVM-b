import SphincsSecurity.Proof.MixedMomentOperators

namespace SphincsSecurity.Concrete

open ENNReal

theorem le_mixedQueryEnvelope (arrival : ENNReal) (moments : MixedMomentVector) : moments ≤ mixedQueryEnvelope arrival moments :=
  fun _ _ => le_self_add

theorem le_mixedSigningEnvelope (uniform reuse : ENNReal) (moments : MixedMomentVector) : moments ≤ mixedSigningEnvelope uniform reuse moments :=
  fun _ _ => le_self_add.trans le_self_add

theorem mixedQueryEnvelope_iterate_signing_le (uniform reuse arrival : ENNReal) (queries : Nat) (moments : MixedMomentVector) :
    (mixedQueryEnvelope arrival)^[queries] (mixedSigningEnvelope uniform reuse moments) ≤
      mixedSigningEnvelope uniform reuse ((mixedQueryEnvelope arrival)^[queries] moments) := by
  induction queries with
  | zero => exact le_rfl
  | succ queries ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact ((mixedQueryEnvelope_mono arrival) ih).trans (mixedQuery_signing_le uniform reuse arrival _)

noncomputable def mixedRemainingEnvelope (uniform reuse arrival : ENNReal) (queries signatures : Nat)
    (moments : MixedMomentVector) : MixedMomentVector :=
  (mixedSigningEnvelope uniform reuse)^[signatures] ((mixedQueryEnvelope arrival)^[queries] moments)

theorem mixedRemainingEnvelope_mono (uniform reuse arrival : ENNReal) (queries signatures : Nat) :
    Monotone (mixedRemainingEnvelope uniform reuse arrival queries signatures) :=
  ((mixedSigningEnvelope_mono uniform reuse).iterate signatures).comp ((mixedQueryEnvelope_mono arrival).iterate queries)

theorem mixedRemainingEnvelope_queries_mono (uniform reuse arrival : ENNReal) (signatures : Nat) (moments : MixedMomentVector) :
    Monotone (fun queries => mixedRemainingEnvelope uniform reuse arrival queries signatures moments) := by
  intro small large h
  exact (mixedSigningEnvelope_mono uniform reuse).iterate signatures
    (Function.monotone_iterate_of_id_le (le_mixedQueryEnvelope arrival) h moments)

theorem le_mixedRemainingEnvelope (uniform reuse arrival : ENNReal) (queries signatures : Nat) (moments : MixedMomentVector) :
    moments ≤ mixedRemainingEnvelope uniform reuse arrival queries signatures moments :=
  (Function.id_le_iterate_of_id_le (le_mixedQueryEnvelope arrival) queries moments).trans
    (Function.id_le_iterate_of_id_le (le_mixedSigningEnvelope uniform reuse) signatures _)

theorem mixedRemainingEnvelope_query (uniform reuse arrival : ENNReal) (queries signatures : Nat) (moments : MixedMomentVector) :
    mixedRemainingEnvelope uniform reuse arrival queries signatures (mixedQueryEnvelope arrival moments) =
      mixedRemainingEnvelope uniform reuse arrival (queries + 1) signatures moments := by
  simp only [mixedRemainingEnvelope, Function.iterate_succ_apply]

theorem mixedRemainingEnvelope_signing_le (uniform reuse arrival : ENNReal) (queries signatures : Nat) (moments : MixedMomentVector) :
    mixedRemainingEnvelope uniform reuse arrival queries signatures (mixedSigningEnvelope uniform reuse moments) ≤
      mixedRemainingEnvelope uniform reuse arrival queries (signatures + 1) moments := by
  unfold mixedRemainingEnvelope
  rw [Function.iterate_succ_apply]
  exact (mixedSigningEnvelope_mono uniform reuse).iterate signatures (mixedQueryEnvelope_iterate_signing_le uniform reuse arrival queries moments)

theorem mixedPowerLower_tsum {α : Type} (moments : α → MixedMomentVector) (power order : Nat) :
    mixedPowerLower (fun p o => ∑' result, moments result p o) power order =
      ∑' result, mixedPowerLower (moments result) power order := by
  simp only [mixedPowerLower, ← ENNReal.tsum_mul_left]
  exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm

theorem mixedQueryEnvelope_tsum {α : Type} (arrival : ENNReal) (moments : α → MixedMomentVector) (power order : Nat) :
    mixedQueryEnvelope arrival (fun p o => ∑' result, moments result p o) power order =
      ∑' result, mixedQueryEnvelope arrival (moments result) power order := by
  simp only [mixedQueryEnvelope, mixedPowerLower_tsum, ENNReal.tsum_mul_left, ENNReal.tsum_add]

theorem mixedSigningEnvelope_tsum {α : Type} (uniform reuse : ENNReal) (moments : α → MixedMomentVector) (power order : Nat) :
    mixedSigningEnvelope uniform reuse (fun p o => ∑' result, moments result p o) power order =
      ∑' result, mixedSigningEnvelope uniform reuse (moments result) power order := by
  simp only [mixedSigningEnvelope, mixedPowerLower_tsum, ENNReal.tsum_mul_left, ENNReal.tsum_add]

theorem mixedQueryEnvelope_mul (arrival scalar : ENNReal) (moments : MixedMomentVector) (power order : Nat) :
    mixedQueryEnvelope arrival (fun p o => scalar * moments p o) power order =
      scalar * mixedQueryEnvelope arrival moments power order := by
  simp only [mixedQueryEnvelope, mixedPowerLower_mul]
  ring

theorem mixedSigningEnvelope_mul (uniform reuse scalar : ENNReal) (moments : MixedMomentVector) (power order : Nat) :
    mixedSigningEnvelope uniform reuse (fun p o => scalar * moments p o) power order =
      scalar * mixedSigningEnvelope uniform reuse moments power order := by
  simp only [mixedSigningEnvelope, mixedPowerLower_mul]
  ring

theorem mixedRemainingEnvelope_tsum {α : Type} (uniform reuse arrival : ENNReal) (queries signatures : Nat)
    (moments : α → MixedMomentVector) (power order : Nat) :
    mixedRemainingEnvelope uniform reuse arrival queries signatures (fun p o => ∑' result, moments result p o) power order =
      ∑' result, mixedRemainingEnvelope uniform reuse arrival queries signatures (moments result) power order := by
  have hquery (count : Nat) : (mixedQueryEnvelope arrival)^[count] (fun p o => ∑' result, moments result p o) =
      fun p o => ∑' result, (mixedQueryEnvelope arrival)^[count] (moments result) p o := by
    induction count with
    | zero => rfl
    | succ count ih =>
        simp only [Function.iterate_succ_apply', ih]
        funext p o
        exact mixedQueryEnvelope_tsum arrival _ p o
  unfold mixedRemainingEnvelope
  rw [hquery]
  induction signatures generalizing power order with
  | zero => rfl
  | succ signatures ih =>
      simp only [Function.iterate_succ_apply']
      have hsign : (mixedSigningEnvelope uniform reuse)^[signatures]
          (fun p o => ∑' result, (mixedQueryEnvelope arrival)^[queries] (moments result) p o) =
          fun p o => ∑' result, (mixedSigningEnvelope uniform reuse)^[signatures] ((mixedQueryEnvelope arrival)^[queries] (moments result)) p o := by
        funext p o
        exact ih p o
      rw [hsign]
      exact mixedSigningEnvelope_tsum uniform reuse _ power order

theorem mixedRemainingEnvelope_mul (uniform reuse arrival scalar : ENNReal) (queries signatures : Nat)
    (moments : MixedMomentVector) (power order : Nat) :
    mixedRemainingEnvelope uniform reuse arrival queries signatures (fun p o => scalar * moments p o) power order =
      scalar * mixedRemainingEnvelope uniform reuse arrival queries signatures moments power order := by
  have hquery (count : Nat) : (mixedQueryEnvelope arrival)^[count] (fun p o => scalar * moments p o) =
      fun p o => scalar * (mixedQueryEnvelope arrival)^[count] moments p o := by
    induction count with
    | zero => rfl
    | succ count ih =>
        simp only [Function.iterate_succ_apply', ih]
        funext p o
        exact mixedQueryEnvelope_mul arrival scalar _ p o
  unfold mixedRemainingEnvelope
  rw [hquery]
  induction signatures generalizing power order with
  | zero => rfl
  | succ signatures ih =>
      simp only [Function.iterate_succ_apply']
      have hsign : (mixedSigningEnvelope uniform reuse)^[signatures]
          (fun p o => scalar * (mixedQueryEnvelope arrival)^[queries] moments p o) =
          fun p o => scalar * (mixedSigningEnvelope uniform reuse)^[signatures] ((mixedQueryEnvelope arrival)^[queries] moments) p o := by
        funext p o
        exact ih p o
      rw [hsign]
      exact mixedSigningEnvelope_mul uniform reuse scalar _ power order

theorem mixedRemainingEnvelope_expected {α : Type} (uniform reuse arrival : ENNReal) (queries signatures : Nat)
    (weight : α → ENNReal) (moments : α → MixedMomentVector) (power order : Nat) :
    (∑' result, weight result * mixedRemainingEnvelope uniform reuse arrival queries signatures (moments result) power order) =
      mixedRemainingEnvelope uniform reuse arrival queries signatures (fun p o => ∑' result, weight result * moments result p o) power order := by
  rw [mixedRemainingEnvelope_tsum]
  apply tsum_congr
  intro result
  exact (mixedRemainingEnvelope_mul uniform reuse arrival (weight result) queries signatures (moments result) power order).symm

end SphincsSecurity.Concrete
