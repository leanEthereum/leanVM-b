import SphincsSecurity.Proof.WeightedSigningMoments

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cachedIndexMultiplicity (parameter : PublicParameter) (cache : QueryCache HashSpec) (index : Index) : ENNReal :=
  cacheMessageWeight parameter (fun _ source => if source.1 = index then 1 else 0) cache

theorem cacheMessageWeight_eq_index_sum (parameter : PublicParameter) (cache : QueryCache HashSpec) (weight : Index → ENNReal) :
    cacheMessageWeight parameter (fun _ source => weight source.1) cache =
      ∑ index : Index, cachedIndexMultiplicity parameter cache index * weight index := by
  have hsplit : (fun (_ : HashInput) (source : FewTimeView) => weight source.1) =
      (fun _ source => ∑ index : Index, (if source.1 = index then (1 : ENNReal) else 0) * weight index) := by
    funext input source
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hsplit, cacheMessageWeight_sum]
  apply Finset.sum_congr rfl
  intro index _
  exact cacheMessageWeight_mul_right parameter _ cache (weight index)

theorem cachedIndexMultiplicity_cacheQuery (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : HashInput) (output : HashOutput) (hfresh : cache input = none) (index : Index) :
    cachedIndexMultiplicity parameter (cache.cacheQuery input output) index = cachedIndexMultiplicity parameter cache index +
      (if MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output) ∧ (hashOutputFewTimeView output).1 = index then 1 else 0) := by
  rw [cachedIndexMultiplicity, cacheMessageWeight_cacheQuery parameter _ cache input output hfresh]
  simp only [← ite_and, and_assoc]
  rfl

theorem cachedIndexMultiplicity_mono (parameter : PublicParameter) (before after : QueryCache HashSpec)
    (hcache : before ≤ after) (index : Index) :
    cachedIndexMultiplicity parameter before index ≤ cachedIndexMultiplicity parameter after index := by
  rw [cachedIndexMultiplicity, cachedIndexMultiplicity, cacheMessageWeight_of_le parameter _ before after hcache]
  exact le_self_add

theorem weightedCachedBinomialMoments_eq_index_sum (weights : Index → ENNReal) (key : SecretKey)
    (state : CoverLogState) (degree : Nat) :
    weightedCachedBinomialMoments weights key state degree =
      ∑ index : Index, cachedIndexMultiplicity key.parameter state.1 index *
        (weights index * ((signingSlotsAtIndex
          (observedOptionalSigningViews (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card.choose degree : ENNReal)) :=
  cacheMessageWeight_eq_index_sum key.parameter state.1 (fun index => weights index *
    ((signingSlotsAtIndex (observedOptionalSigningViews (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2)
      index).card.choose degree : ENNReal))

end SphincsSecurity.Concrete
