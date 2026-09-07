import SphincsSecurity.Proof.IndexDifferenceTransform

namespace SphincsSecurity.Concrete

open ENNReal

theorem indexDifferenceTransform_query (arrival : ENNReal) (moments : TargetIndexVector) :
    indexDifferenceTransform (targetIndexQuery arrival moments) = mixedQueryEnvelope arrival (indexDifferenceTransform moments) := by
  unfold targetIndexQuery
  rw [indexDifferenceTransform_add, indexDifferenceTransform_mul, indexDifferenceTransform_cache]
  rfl

theorem indexDifferenceTransform_signing (uniform reuse : ENNReal) (moments : TargetIndexVector) :
    indexDifferenceTransform (targetIndexSigning uniform reuse moments) = mixedSigningEnvelope uniform reuse (indexDifferenceTransform moments) := by
  unfold targetIndexSigning
  simp only [indexDifferenceTransform_add, indexDifferenceTransform_mul, indexDifferenceTransform_cache,
    indexDifferenceTransform_tree, indexDifferenceTransform_reuse]
  rfl

theorem indexDifferenceTransform_query_iterate (arrival : ENNReal) (queries : Nat) (moments : TargetIndexVector) :
    indexDifferenceTransform ((targetIndexQuery arrival)^[queries] moments) = (mixedQueryEnvelope arrival)^[queries] (indexDifferenceTransform moments) := by
  induction queries with
  | zero => rfl
  | succ queries ih => simp only [Function.iterate_succ_apply', indexDifferenceTransform_query, ih]

theorem indexDifferenceTransform_signing_iterate (uniform reuse : ENNReal) (signings : Nat) (moments : TargetIndexVector) :
    indexDifferenceTransform ((targetIndexSigning uniform reuse)^[signings] moments) =
      (mixedSigningEnvelope uniform reuse)^[signings] (indexDifferenceTransform moments) := by
  induction signings with
  | zero => rfl
  | succ signings ih => simp only [Function.iterate_succ_apply', indexDifferenceTransform_signing, ih]

theorem indexDifferenceTransform_envelope (uniform reuse arrival : ENNReal) (queries signings : Nat) (moments : TargetIndexVector) :
    indexDifferenceTransform (targetIndexEnvelope uniform reuse arrival queries signings moments) =
      mixedRemainingEnvelope uniform reuse arrival queries signings (indexDifferenceTransform moments) := by
  unfold targetIndexEnvelope mixedRemainingEnvelope
  rw [indexDifferenceTransform_signing_iterate, indexDifferenceTransform_query_iterate]

theorem targetIndexEnvelope_fourteen_eq_mixed (uniform reuse arrival : ENNReal) (queries signings : Nat) (moments : TargetIndexVector) (power : Nat) :
    targetIndexEnvelope uniform reuse arrival queries signings moments power 14 =
      mixedRemainingEnvelope uniform reuse arrival queries signings (indexDifferenceTransform moments) power 0 := by
  rw [← indexDifferenceTransform_envelope]
  rfl

end SphincsSecurity.Concrete
