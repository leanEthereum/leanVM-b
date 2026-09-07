import SphincsSecurity.Proof.TargetShapeBlocks
import SphincsSecurity.Proof.ConcreteTargetShapeQuery
import SphincsSecurity.Proof.CacheIndexMultiplicity
import SphincsSecurity.Proof.CachedTargetIncrement

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem excludedCacheIndexCount_fresh (parameter : PublicParameter) (cache : QueryCache HashSpec) (targetInput : HashInput)
    (hfresh : cache targetInput = none) (index : Index) :
    excludedCacheIndexCount parameter cache targetInput index = cachedIndexMultiplicity parameter cache index := by
  unfold excludedCacheIndexCount cachedIndexMultiplicity cacheMessageWeight
  apply tsum_congr
  intro input
  by_cases heq : input = targetInput
  · subst input
    simp only [cacheMessageEntryWeight, hfresh]
  · unfold cacheMessageEntryWeight
    cases cache input <;> simp only [heq, if_false]

noncomputable def targetIndexMoments (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (power degree : Nat) : ENNReal :=
  ∑ index : Index, cachedIndexMultiplicity key.parameter cache index ^ power *
    ((signingSlotsAtIndex (observedOptionalSigningViews (FtsProbeSimulation.messageAnswers key.parameter cache) key.root log) index).card : ENNReal) ^ degree

theorem expected_fresh_targetShapeMoments (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (hfresh : cache (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter cache key.root log)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * targetShapeMoments key cache log payload target groups remaining) =
      (Fintype.card Index : ENNReal)⁻¹ * targetIndexMoments key cache log groups.card remaining.card := by
  rw [expected_targetShapeMoments key cache log payload groups remaining hvalid]
  simp only [excludedCacheIndexCount_fresh key.parameter cache _ hfresh,
    eligibleSigningViews_fresh_eq_observed key.parameter key.root cache log payload hfresh hsigned, targetIndexMoments]

theorem expected_cacheQuery_freshTargetShape (key : SecretKey) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (hfresh : before (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        targetShapeMoments key (before.cacheQuery (tweakableHashInput key.parameter .message payload) output) log payload
          (hashOutputFewTimeView output) groups remaining else 0)) =
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
        targetIndexMoments key before log groups.card remaining.card := by
  simp only [targetShapeMoments_cacheQuery_unchanged key before log payload _ groups remaining _ _ hfresh hsigned (Or.inr rfl)]
  rw [expected_uniformHashOutput_admissible_weight (fun target => targetShapeMoments key before log payload target groups remaining),
    expected_fresh_targetShapeMoments key before log payload hfresh hsigned groups remaining hvalid]
  exact (mul_assoc _ _ _).symm

end SphincsSecurity.Concrete
