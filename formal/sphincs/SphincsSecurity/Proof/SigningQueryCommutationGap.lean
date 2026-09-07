import SphincsSecurity.Proof.TargetShapeExpectation

namespace SphincsSecurity.Concrete

open ENNReal

noncomputable def targetTreeArrival (f : TargetShapeVector) : TargetShapeVector :=
  fun groups remaining => targetTreeLower f groups remaining + targetCacheLower (targetTreeLower f) groups remaining

theorem targetShapeQuery_add (arrival : ENNReal) (f g : TargetShapeVector) :
    targetShapeQuery arrival (fun G R => f G R + g G R) =
      fun G R => targetShapeQuery arrival f G R + targetShapeQuery arrival g G R := by
  funext G R
  simp only [targetShapeQuery, targetCacheLower_add]
  ring

theorem targetTreeArrival_query (arrival : ENNReal) (f : TargetShapeVector) :
    targetTreeArrival (targetShapeQuery arrival f) = targetShapeQuery arrival (targetTreeArrival f) := by
  have ht : targetTreeLower (targetShapeQuery arrival f) = fun G R =>
      targetTreeLower f G R + arrival * targetCacheLower (targetTreeLower f) G R := by
    funext G R
    change targetTreeLower (fun G R => f G R + arrival * targetCacheLower f G R) G R = _
    rw [targetTreeLower_add, targetTreeLower_mul, ← targetCacheLower_tree_commute]
  funext G R
  change targetTreeLower (targetShapeQuery arrival f) G R + targetCacheLower (targetTreeLower (targetShapeQuery arrival f)) G R =
    (targetTreeLower f G R + targetCacheLower (targetTreeLower f) G R) +
      arrival * targetCacheLower (fun G R => targetTreeLower f G R + targetCacheLower (targetTreeLower f) G R) G R
  rw [ht]
  simp only [targetCacheLower_add, targetCacheLower_mul]
  ring

theorem targetTreeArrival_query_iterate (arrival : ENNReal) (queries : Nat) (f : TargetShapeVector) :
    targetTreeArrival ((targetShapeQuery arrival)^[queries] f) =
      (targetShapeQuery arrival)^[queries] (targetTreeArrival f) := by
  induction queries with
  | zero => rfl
  | succ queries ih => rw [Function.iterate_succ_apply', targetTreeArrival_query, ih, Function.iterate_succ_apply']

theorem targetShapeQuery_congr_valid (arrival : ENNReal) {f g : TargetShapeVector}
    (h : ∀ G R, TargetShapeValid G R → f G R = g G R)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    targetShapeQuery arrival f groups remaining = targetShapeQuery arrival g groups remaining :=
  le_antisymm (targetShapeQuery_mono arrival (fun G R hv => (h G R hv).le) groups remaining hvalid)
    (targetShapeQuery_mono arrival (fun G R hv => (h G R hv).ge) groups remaining hvalid)

theorem targetShapeSigning_query_iterate_gap (uniform reuse arrival : ENNReal) (queries : Nat) (f : TargetShapeVector)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    targetShapeSigning uniform reuse ((targetShapeQuery arrival)^[queries + 1] f) groups remaining =
      (targetShapeQuery arrival)^[queries + 1] (targetShapeSigning uniform reuse f) groups remaining +
        ((queries + 1 : Nat) : ENNReal) * arrival * reuse *
          (targetShapeQuery arrival)^[queries] (targetTreeArrival f) groups remaining := by
  induction queries generalizing groups remaining with
  | zero => simpa only [Nat.zero_add, Function.iterate_one, Function.iterate_zero, id_eq, Nat.cast_one, one_mul, targetTreeArrival] using
      targetShapeSigning_query_commute uniform reuse arrival f groups remaining hvalid
  | succ queries ih =>
      rw [Function.iterate_succ_apply' (targetShapeQuery arrival) (queries + 1), targetShapeSigning_query_commute _ _ _ _ _ _ hvalid]
      have hq := targetShapeQuery_congr_valid arrival (fun G R hv => ih G R hv) groups remaining hvalid
      rw [hq, targetShapeQuery_add]
      dsimp only
      rw [targetShapeQuery_mul]
      change _ + arrival * reuse * targetTreeArrival ((targetShapeQuery arrival)^[queries + 1] f) groups remaining = _
      rw [targetTreeArrival_query_iterate]
      simp only [Function.iterate_succ_apply', Nat.cast_add, Nat.cast_one]
      ring

theorem targetShapeSigning_add (uniform reuse : ENNReal) (f g : TargetShapeVector) :
    targetShapeSigning uniform reuse (fun G R => f G R + g G R) =
      fun G R => targetShapeSigning uniform reuse f G R + targetShapeSigning uniform reuse g G R := by
  have ht : targetTreeLower (fun G R => f G R + g G R) = fun G R => targetTreeLower f G R + targetTreeLower g G R := by
    funext G R
    exact targetTreeLower_add f g G R
  funext G R
  simp only [targetShapeSigning, ht, targetCacheLower_add, targetReuseStep_add]
  ring

theorem targetShapeSigning_iterate_add_mul (uniform reuse scalar : ENNReal) (signings : Nat) (f g : TargetShapeVector) :
    (targetShapeSigning uniform reuse)^[signings] (fun G R => f G R + scalar * g G R) =
      fun G R => (targetShapeSigning uniform reuse)^[signings] f G R + scalar * (targetShapeSigning uniform reuse)^[signings] g G R := by
  induction signings with
  | zero => rfl
  | succ signings ih =>
      rw [Function.iterate_succ_apply', ih, targetShapeSigning_add]
      funext G R
      rw [targetShapeSigning_mul]
      simp only [Function.iterate_succ_apply']

noncomputable def signingQueryCommutationGap (uniform reuse arrival : ENNReal) : Nat → Nat → TargetShapeVector → TargetShapeVector
  | 0, _, _ => fun _ _ => 0
  | queries + 1, signings, f => fun G R => ((queries + 1 : Nat) : ENNReal) * arrival * reuse *
      targetShapeEnvelope uniform reuse arrival queries signings (targetTreeArrival f) G R

theorem targetShapeEnvelope_signing_gap (uniform reuse arrival : ENNReal) (queries signings : Nat) (f : TargetShapeVector)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    targetShapeEnvelope uniform reuse arrival queries signings (targetShapeSigning uniform reuse f) groups remaining +
      signingQueryCommutationGap uniform reuse arrival queries signings f groups remaining =
      targetShapeEnvelope uniform reuse arrival queries (signings + 1) f groups remaining := by
  cases queries with
  | zero => simp only [signingQueryCommutationGap, add_zero, targetShapeEnvelope, Function.iterate_zero, id_eq, Function.iterate_succ_apply]
  | succ queries =>
      have h (G R) (hv : TargetShapeValid G R) := targetShapeSigning_query_iterate_gap uniform reuse arrival queries f G R hv
      have heq := le_antisymm
        (targetShapeSigning_iterate_mono uniform reuse signings (fun G R hv => (h G R hv).le) groups remaining hvalid)
        (targetShapeSigning_iterate_mono uniform reuse signings (fun G R hv => (h G R hv).ge) groups remaining hvalid)
      rw [targetShapeSigning_iterate_add_mul] at heq
      simpa only [targetShapeEnvelope, signingQueryCommutationGap, Function.iterate_succ_apply] using heq.symm

end SphincsSecurity.Concrete
