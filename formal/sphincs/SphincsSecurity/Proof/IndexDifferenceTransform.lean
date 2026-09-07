import SphincsSecurity.Proof.TargetIndexEnvelope
import SphincsSecurity.Proof.MixedMomentEnvelope

namespace SphincsSecurity.Concrete

open ENNReal

noncomputable def indexDifferenceTransform (moments : TargetIndexVector) : MixedMomentVector :=
  fun power order => targetIndexTreeLower^[order] moments power 14

theorem targetIndexTreeLower_add (left right : TargetIndexVector) :
    targetIndexTreeLower (fun p r => left p r + right p r) = fun p r => targetIndexTreeLower left p r + targetIndexTreeLower right p r := by
  funext power degree
  simp only [targetIndexTreeLower, mul_add, Finset.sum_add_distrib]

theorem targetIndexTreeLower_mul (scalar : ENNReal) (moments : TargetIndexVector) :
    targetIndexTreeLower (fun p r => scalar * moments p r) = fun p r => scalar * targetIndexTreeLower moments p r := by
  funext power degree
  simp only [targetIndexTreeLower, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lower _
  ring

theorem targetIndexTreeLower_cache_commute (moments : TargetIndexVector) :
    targetIndexTreeLower (targetIndexCacheLower moments) = targetIndexCacheLower (targetIndexTreeLower moments) := by
  funext power degree
  simp only [targetIndexTreeLower, targetIndexCacheLower, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro lowerPower _
  apply Finset.sum_congr rfl
  intro lowerDegree _
  ring

theorem targetIndexTreeLower_iterate_add (order : Nat) (left right : TargetIndexVector) :
    targetIndexTreeLower^[order] (fun p r => left p r + right p r) =
      fun p r => targetIndexTreeLower^[order] left p r + targetIndexTreeLower^[order] right p r := by
  induction order with
  | zero => rfl
  | succ order ih => simp only [Function.iterate_succ_apply', ih, targetIndexTreeLower_add]

theorem targetIndexTreeLower_iterate_mul (order : Nat) (scalar : ENNReal) (moments : TargetIndexVector) :
    targetIndexTreeLower^[order] (fun p r => scalar * moments p r) = fun p r => scalar * targetIndexTreeLower^[order] moments p r := by
  induction order with
  | zero => rfl
  | succ order ih => simp only [Function.iterate_succ_apply', ih, targetIndexTreeLower_mul]

theorem targetIndexTreeLower_iterate_cache (order : Nat) (moments : TargetIndexVector) :
    targetIndexTreeLower^[order] (targetIndexCacheLower moments) = targetIndexCacheLower (targetIndexTreeLower^[order] moments) := by
  induction order with
  | zero => rfl
  | succ order ih => simp only [Function.iterate_succ_apply', ih, targetIndexTreeLower_cache_commute]

theorem targetIndexTreeLower_iterate_shift (order : Nat) (moments : TargetIndexVector) :
    targetIndexTreeLower^[order] (fun p r => moments (p + 1) r) = fun p r => targetIndexTreeLower^[order] moments (p + 1) r := by
  induction order with
  | zero => rfl
  | succ order ih => simp only [Function.iterate_succ_apply', ih]; rfl

theorem indexDifferenceTransform_add (left right : TargetIndexVector) :
    indexDifferenceTransform (fun p r => left p r + right p r) = fun p o => indexDifferenceTransform left p o + indexDifferenceTransform right p o := by
  funext power order
  simp only [indexDifferenceTransform, targetIndexTreeLower_iterate_add]

theorem indexDifferenceTransform_mul (scalar : ENNReal) (moments : TargetIndexVector) :
    indexDifferenceTransform (fun p r => scalar * moments p r) = fun p o => scalar * indexDifferenceTransform moments p o := by
  funext power order
  simp only [indexDifferenceTransform, targetIndexTreeLower_iterate_mul]

theorem indexDifferenceTransform_cache (moments : TargetIndexVector) :
    indexDifferenceTransform (targetIndexCacheLower moments) = mixedPowerLower (indexDifferenceTransform moments) := by
  funext power order
  simp only [indexDifferenceTransform, targetIndexTreeLower_iterate_cache, targetIndexCacheLower, mixedPowerLower]

theorem indexDifferenceTransform_tree (moments : TargetIndexVector) :
    indexDifferenceTransform (targetIndexTreeLower moments) = fun p o => indexDifferenceTransform moments p (o + 1) := by
  funext power order
  simp only [indexDifferenceTransform, Function.iterate_succ_apply]

theorem indexDifferenceTransform_reuse (moments : TargetIndexVector) :
    indexDifferenceTransform (targetIndexReuseStep moments) = fun p o => indexDifferenceTransform moments (p + 1) (o + 1) := by
  have heq : targetIndexReuseStep moments = fun p r => targetIndexTreeLower moments (p + 1) r := rfl
  funext power order
  simp only [heq, indexDifferenceTransform, targetIndexTreeLower_iterate_shift, Function.iterate_succ_apply]

end SphincsSecurity.Concrete
