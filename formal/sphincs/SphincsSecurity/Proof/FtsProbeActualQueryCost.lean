import SphincsSecurity.Proof.FtsProbeCostComparison

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

theorem expected_actualRetained_cache_le_queryCharge (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (table : Coordinate → Digest) :
    (∑' result, Pr[= result | actualRetainedGameAfterSecrets adversary parameter otsSecret table] *
      (probeCachedInputs parameter result.2).ncard) ≤
      expectedQueryCharge (ftsHashQueryCharge parameter)
        (gameAfterSecrets adversary parameter otsSecret (fun index tree leafIdx => table (index, tree, leafIdx))) ∅ := by
  have hprojection := congrArg
    (fun run : ProbComp RetainedGameLogResult =>
      ∑' result, Pr[= result | run] * (probeCachedInputs parameter result.2.1).ncard)
    (gameAfterSecretsWithViewTrace_actualRetained_projection adversary parameter otsSecret table)
  simp only [tsum_probOutput_map_mul] at hprojection
  have hbound := expected_probeCachedInputs_le_queryCharge parameter
    (gameAfterSecrets adversary parameter otsSecret (fun index tree leafIdx => table (index, tree, leafIdx)))
  rw [← gameAfterSecretsWithViewTrace_verdictCache_projection, tsum_probOutput_map_mul] at hbound
  exact hprojection.symm.le.trans hbound

theorem sampledActualFtsCacheCount_le_queryCharge (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :
    sampledActualFtsCacheCount adversary parameter otsSecret ≤
      ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
        expectedQueryCharge (ftsHashQueryCharge parameter)
          (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ := by
  unfold sampledActualFtsCacheCount
  rw [AdaptiveRevealProbe.expectedCost_congr _ _ _
    (evalDist_sampledConcreteActualRetainedFts_eq adversary parameter otsSecret).symm]
  rw [sampledConcreteActualRetainedFts, tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  exact mul_le_mul' le_rfl
    (expected_actualRetained_cache_le_queryCharge adversary parameter otsSecret (curryFtsTableEquiv ftsSecret))

end SphincsSecurity.Concrete.FtsProbeSimulation
