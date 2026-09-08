import SphincsSecurity.Proof.SigningFreshEncodingBudget
import SphincsSecurity.Proof.PreExceptionCacheCap
import SphincsSecurity.Proof.EncodingPairQueryReserve
import SphincsSecurity.Proof.BeforeFailureSigningCacheCap

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation
attribute [local instance] Classical.propDecidable
attribute [local irreducible] encodingPairIncrementCharge freshEncodingHashCharge freshCacheCharge
set_option backward.isDefEq.respectTransparency false

theorem encodingPairIncrementCharge_le_freshEncoding_rate
    (key : SecretKey) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (cap : Nat) (hcap : QueryCache.enncard cache ≤ cap) (input : HashInput) :
    encodingPairIncrementCharge key cache input ≤ freshEncodingHashCharge key.parameter cache input *
      (2 * (cap : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) := by
  unfold encodingPairIncrementCharge freshEncodingHashCharge
  split_ifs with hencoding
  · by_cases hfresh : cache input = none
    · rw [freshCacheCharge, if_pos hfresh, one_mul]
      exact validCachePairIncrementCharge_le_cap cache hfinite cap hcap input
    · rw [freshCacheCharge, if_neg hfresh, validCachePairIncrementCharge, if_neg hfresh, zero_mul]
  · simp

theorem encodingPairIncrementCharge_le_freshEncoding
    (key : SecretKey) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (cap : Nat) (hcap : QueryCache.enncard cache ≤ cap) (hcapMax : cap ≤ 2 ^ 127) (input : HashInput) :
    encodingPairIncrementCharge key cache input ≤ freshEncodingHashCharge key.parameter cache input :=
  (encodingPairIncrementCharge_le_freshEncoding_rate key cache hfinite cap hcap input).trans
    (mul_le_of_le_one_right' (encodingPairQueryRate_le_one cap hcapMax))

theorem expectedPreException_signingEncodingPairs_le_reserved
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (cap : Nat) (hcapMax : cap ≤ 2 ^ 127)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool)
    (hcap : ∀ result ∈ support ((simulateQ romImpl (sign key message)).run cache), QueryCache.enncard result.2 ≤ cap) :
    expectedPreExceptionCharge exception (encodingPairIncrementCharge key) (sign key message) cache hit ≤
      expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter) (sign key message) cache hit :=
  (expectedPreExceptionCharge_mono_of_cache_cap exception _ _ cap
    (fun current hf hc input => encodingPairIncrementCharge_le_freshEncoding key current hf cap hc hcapMax input)
    (sign key message) cache hfinite hit hcap).trans
      (expectedPreException_freshEncoding_sign_le_reserved exception key message cache hit)

theorem expectedPreException_signingEncodingPairs_le_reserved_rate
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (cap : Nat)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool)
    (hcap : ∀ result ∈ support ((simulateQ romImpl (sign key message)).run cache), QueryCache.enncard result.2 ≤ cap) :
    expectedPreExceptionCharge exception (encodingPairIncrementCharge key) (sign key message) cache hit ≤
      expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter) (sign key message) cache hit *
        (2 * (cap : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) := by
  apply (expectedPreExceptionCharge_mono_of_cache_cap exception _
    (fun current input => freshEncodingHashCharge key.parameter current input *
      (2 * (cap : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹)) cap
    (fun current hf hc input => encodingPairIncrementCharge_le_freshEncoding_rate key current hf cap hc input)
    (sign key message) cache hfinite hit hcap).trans
  rw [expectedPreExceptionCharge_mul]
  exact mul_le_mul' (expectedPreException_freshEncoding_sign_le_reserved exception key message cache hit) le_rfl

namespace FtsProbeSimulation.JointOriginal

theorem expected_signingEncodingPairs_le_reserved_rate
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit failed : Bool)
    (hcap : ∀ result ∈ support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed),
      QueryCache.enncard result.1.2.1.2 ≤ cap) :
    expectedBeforeFailureSigningCharge exception (encodingPairIncrementCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedBeforeFailureSigningCharge exception (nonMessageNonEncodingHashCharge parameter)
        parameter root otsTable ftsTable computation frame cache hit failed *
          (2 * (cap : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) := by
  rw [← expectedBeforeFailureSigningCharge_mul]
  apply expectedBeforeFailureSigningCharge_le_of_cache_cap exception _ _ cap parameter root otsTable ftsTable
    _ computation frame cache hfinite hit failed hcap
  intro message current hf currentHit hc
  rw [expectedPreExceptionCharge_mul]
  exact expectedPreException_signingEncodingPairs_le_reserved_rate exception (secretKey parameter root otsTable ftsTable)
    message cap current hf currentHit hc

end FtsProbeSimulation.JointOriginal
end SphincsSecurity.Concrete
