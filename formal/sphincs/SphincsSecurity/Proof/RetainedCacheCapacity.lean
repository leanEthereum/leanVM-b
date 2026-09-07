import SphincsSecurity.Proof.AdaptiveCacheCapacity
import SphincsSecurity.Proof.RetainedFutureCacheCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedRetainedCapacityReuseCharge (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (table : Coordinate → Digest) (q : Nat) : ENNReal :=
  ∑' rootResult, Pr[= rootResult | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅] *
    expectedCapacityReuseCharge
      ⟨parameter, rootResult.1, otsSecret, fun index tree leafIdx => table (index, tree, leafIdx)⟩ q
      (unloggedRetainedRestComputation adversary ⟨rootResult.1, parameter⟩) (rootResult.2, [])

theorem probEvent_actualRetained_validObservedCover_le_capacity (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (table : Coordinate → Digest) (q : Nat) (hq : q ≤ 2 ^ 127)
    (hbudget : (gameAfterSecrets adversary parameter otsSecret
      (fun index tree leafIdx => table (index, tree, leafIdx))).IsQueryBoundP (· matches Sum.inr _) q) :
    Pr[fun result => SigningTranscript.Valid result.1.2.1.2 ∧
      ObservedFewTimeCover (messageAnswers parameter result.2)
      result.1.1 result.1.2.1.2 result.1.2.1.1 |
        actualRetainedGameAfterSecrets adversary parameter otsSecret table] ≤
      (q : ENNReal) * (7 * (2 : ENNReal) ^ 40 * ((2 ^ 176 : Nat) : ENNReal)⁻¹) +
        expectedRetainedCapacityReuseCharge adversary parameter otsSecret table q := by
  rw [actualRetainedGameAfterSecrets, probEvent_bind_eq_tsum, expectedRetainedCapacityReuseCharge]
  calc
    _ ≤ ∑' rootResult, Pr[= rootResult | (simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅] *
        ((q : ENNReal) * (7 * (2 : ENNReal) ^ 40 * ((2 ^ 176 : Nat) : ENNReal)⁻¹) +
          expectedCapacityReuseCharge
            ⟨parameter, rootResult.1, otsSecret, fun index tree leafIdx => table (index, tree, leafIdx)⟩ q
            (unloggedRetainedRestComputation adversary ⟨rootResult.1, parameter⟩) (rootResult.2, [])) := by
      apply ENNReal.tsum_le_tsum
      intro rootResult
      by_cases hroot : rootResult ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅)
      · apply mul_le_mul' le_rfl
        simp only [bind_pure_comp, probEvent_map]
        rw [retainedGameRestComputation_interleaved, probEvent_map]
        apply probEvent_adaptive_validObservedCover_le_capacity _ q hq _ _ Prod.fst
        · intro input hmessage
          obtain ⟨payload, rfl⟩ := hmessage
          exact treeRoot_cache_message_none parameter topLayer rootTree (otsSecret topLayer rootTree)
            rootResult.1 rootResult.2 hroot payload
        · exact retainedRoot_rest_cache_bound adversary parameter otsSecret table q hbudget rootResult hroot
      · rw [probOutput_eq_zero_of_not_mem_support hroot, zero_mul, zero_mul]
    _ ≤ _ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl

theorem probEvent_actualRetained_validObservedCover_le_capacity_of_hashQueryBound (adversary : Adversary)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (table : Coordinate → Digest)
    (hfts : (fun index tree leafIdx => table (index, tree, leafIdx)) ∈ support sampleFtsSecrets)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hbudget : HasHashQueryBound scheme adversary q) :
    Pr[fun result => SigningTranscript.Valid result.1.2.1.2 ∧
      ObservedFewTimeCover (messageAnswers parameter result.2)
      result.1.1 result.1.2.1.2 result.1.2.1.1 |
        actualRetainedGameAfterSecrets adversary parameter otsSecret table] ≤
      (q : ENNReal) * (7 * (2 : ENNReal) ^ 40 * ((2 ^ 176 : Nat) : ENNReal)⁻¹) +
        expectedRetainedCapacityReuseCharge adversary parameter otsSecret table q :=
  probEvent_actualRetained_validObservedCover_le_capacity adversary parameter otsSecret table q hq
    (isQueryBoundP_gameAfterSecrets adversary q hbudget hparameter hots hfts)

end SphincsSecurity.Concrete.FtsProbeSimulation
