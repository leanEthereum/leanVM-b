import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.EncodingSigningFailure
import SphincsSecurity.Proof.OtsProbeResolvedSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem cachedOtsEncodingFailure_of_mem_signAfterDigest_none
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (cache finalCache : QueryCache HashSpec)
    (hresult : (none, finalCache) ∈ support
      ((concreteSignAfterDigestFromTable parameter root table ftsSecret randomness index leaves).run cache)) :
    CachedOtsEncodingFailure finalCache := by
  rw [concreteSignAfterDigestFromTable_eq_signAfterDigest] at hresult
  obtain ⟨_hle, f, hagrees, hfailed, hcached⟩ := exists_answerFn_replay_of_mem_support _ _ _ _ hresult
  exact cachedOtsEncodingFailure_of_signAfterDigest_none f finalCache _ randomness index leaves hagrees hcached hfailed

end SphincsSecurity.Concrete.OtsProbeSimulation
