import XmssSecurity.Proof.CacheReplayEval
import XmssSecurity.Proof.HashInputLemmas

open OracleComp OracleSpec

namespace XmssSecurity

theorem Concrete.CacheReplay.encodingHash_eq_of_run_support_of_cache_le
    (parameter : PublicParameter)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (epoch : Epoch) (message : Message) (randomness : Randomness)
    (digest : Digest)
    (hresult : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter epoch message randomness)).run
          initialCache))
    (hle : resultCache ≤ largerCache) :
    Concrete.CacheView.encodingHash largerCache parameter epoch
      (message, randomness) = digest := by
  have hmapped : (digest, resultCache) ∈ support
      ((fun result : HashOutput × QueryCache HashSpec =>
        (truncateHash result.1, result.2)) <$> (randomOracle
          (Concrete.CacheView.encodingInput parameter epoch
            (message, randomness))).run initialCache) := by
    simpa [Concrete.encodingHash, Concrete.tweakableHash,
      Concrete.oracleHash, Concrete.CacheView.encodingInput,
      map_eq_bind_pure_comp] using hresult
  rw [support_map] at hmapped
  obtain ⟨result, hquery, heq⟩ := hmapped
  have hcached := Concrete.CacheReplay.randomOracle_query_caches
    (Concrete.CacheView.encodingInput parameter epoch (message, randomness))
    initialCache result.1 result.2 hquery
  rw [show result.2 = resultCache from congrArg Prod.snd heq] at hcached
  have hcachedLarger := hle hcached
  rw [Concrete.CacheView.encodingHash,
    Concrete.CacheView.digestAt_eq_of_cache_eq_some hcachedLarger]
  exact congrArg Prod.fst heq

end XmssSecurity
