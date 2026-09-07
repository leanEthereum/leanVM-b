import SphincsSecurity.Proof.AdaptiveBinomialOccupancy
import SphincsSecurity.Proof.InterleavedCoverGame

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedRetainedBinomialCharge (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (table : Coordinate → Digest) (q : Nat) : ENNReal :=
  ∑' rootResult, Pr[= rootResult | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅] *
    ∑ degree ∈ Finset.range 14, (coverageFactorialCoefficient (degree + 1) * (degree + 1).factorial : Nat) *
      expectedBinomialOccupancyCharge
        ⟨parameter, rootResult.1, otsSecret, fun index tree leafIdx => table (index, tree, leafIdx)⟩ q degree
        (unloggedRetainedRestComputation adversary ⟨rootResult.1, parameter⟩) (rootResult.2, [])

theorem expected_actualRetained_validOccupancy_le_charge (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (table : Coordinate → Digest) (q : Nat) (hq : q ≤ 2 ^ 127)
    (hbudget : (gameAfterSecrets adversary parameter otsSecret
      (fun index tree leafIdx => table (index, tree, leafIdx))).IsQueryBoundP (· matches Sum.inr _) q) :
    (∑' result, Pr[= result | actualRetainedGameAfterSecrets adversary parameter otsSecret table] *
      (if SigningTranscript.Valid result.1.2.1.2 then
        (coverageOccupancyMoment (observedOptionalSigningViews (messageAnswers parameter result.2)
          result.1.1 result.1.2.1.2) : ENNReal) else 0)) ≤
      expectedRetainedBinomialCharge adversary parameter otsSecret table q := by
  rw [actualRetainedGameAfterSecrets, tsum_probOutput_bind_mul, expectedRetainedBinomialCharge]
  apply ENNReal.tsum_le_tsum
  intro rootResult
  by_cases hroot : rootResult ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅)
  · apply mul_le_mul' le_rfl
    simp only [bind_pure_comp, tsum_probOutput_map_mul]
    rw [retainedGameRestComputation_interleaved, tsum_probOutput_map_mul]
    apply expected_adaptive_validOccupancy_from_empty_le _ q hq
    intro result hresult
    apply actualRetainedGameAfterSecrets_cache_bound adversary parameter otsSecret table q hbudget
      ((rootResult.1, (interleavedRetainedProjection result).1), result.2.1)
    rw [actualRetainedGameAfterSecrets, mem_support_bind_iff]
    refine ⟨rootResult, hroot, ?_⟩
    rw [mem_support_bind_iff]
    refine ⟨interleavedRetainedProjection result, ?_, ?_⟩
    · rw [retainedGameRestComputation_interleaved, support_map]
      exact ⟨result, hresult, rfl⟩
    · simp only [support_pure, Set.mem_singleton_iff]
      rfl
  · rw [probOutput_eq_zero_of_not_mem_support hroot, zero_mul, zero_mul]

theorem expected_actualRetained_validOccupancy_le_charge_of_hashQueryBound (adversary : Adversary)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (table : Coordinate → Digest)
    (hfts : (fun index tree leafIdx => table (index, tree, leafIdx)) ∈ support sampleFtsSecrets)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hbudget : HasHashQueryBound scheme adversary q) :
    (∑' result, Pr[= result | actualRetainedGameAfterSecrets adversary parameter otsSecret table] *
      (if SigningTranscript.Valid result.1.2.1.2 then
        (coverageOccupancyMoment (observedOptionalSigningViews (messageAnswers parameter result.2)
          result.1.1 result.1.2.1.2) : ENNReal) else 0)) ≤
      expectedRetainedBinomialCharge adversary parameter otsSecret table q :=
  expected_actualRetained_validOccupancy_le_charge adversary parameter otsSecret table q hq
    (isQueryBoundP_gameAfterSecrets adversary q hbudget hparameter hots hfts)

end SphincsSecurity.Concrete.FtsProbeSimulation
