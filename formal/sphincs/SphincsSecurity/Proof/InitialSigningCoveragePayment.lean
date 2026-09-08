import SphincsSecurity.Proof.SigningCoverageSurvivalPayment
import SphincsSecurity.Proof.InitialTargetShape
import SphincsSecurity.Proof.JointProbeOriginalInitialization
import SphincsSecurity.Proof.RootCache

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

namespace FtsProbeSimulation

theorem newTargetCoverageExcess_initial_eq_zero (key : SecretKey) (cache : QueryCache HashSpec)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none)
    (reference : HashInput) (q : Nat) (hq : q ≤ 2 ^ 127) :
    newTargetCoverageExcess key cache [] reference (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) q signatureLimit = 0 := by
  unfold newTargetCoverageExcess
  apply ENNReal.tsum_eq_zero.mpr
  intro source
  rw [tsub_eq_zero_of_le (initialTargetShape_scaled_le_signingAllowance key cache hnone reference source q hq), mul_zero]

theorem expected_encodingPairs_add_initialNewTargetCoverage_le_reserved
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (q : Nat) (hq : q ≤ 2 ^ 127)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool)
    (hcap : ∀ result ∈ support ((simulateQ romImpl (sign key message)).run cache), QueryCache.enncard result.2 ≤ q)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none) :
    expectedPreExceptionCharge exception (encodingPairIncrementCharge key) (sign key message) cache hit *
        (Fintype.card Digest : ENNReal)⁻¹ +
      signingNewTargetCoverage exception key message cache hit [] (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) q signatureLimit ≤
      expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter) (sign key message) cache hit *
        (Fintype.card Digest : ENNReal)⁻¹ := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have h := expected_encodingPairs_add_newTargetCoverage_le_reserved_add_excess exception key message q hq cache hfinite hit hcap
    [] hsigned [] (hnone _ ⟨[], rfl⟩) (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) q signatureLimit
  simpa only [newTargetCoverageExcess_initial_eq_zero key cache hnone [] q hq, add_zero] using h

namespace JointOriginal

theorem newTargetCoverageExcess_initializeRoot_eq_zero
    (parameter : PublicParameter) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (fuel : Nat) (reference : HashInput)
    (initial : Option Frame × (Digest × QueryCache HashSpec))
    (hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)) :
    newTargetCoverageExcess (secretKey parameter initial.2.1 otsTable ftsTable) initial.2.2 [] reference
      (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) q signatureLimit = 0 := by
  apply newTargetCoverageExcess_initial_eq_zero _ _ ?_ reference q hq
  have hroot := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
  rw [originalRoot, simulateQ_romImpl_liftM] at hroot
  intro input hmessage
  obtain ⟨payload, rfl⟩ := hmessage
  exact treeRoot_cache_message_none parameter topLayer rootTree
    ((secretKey parameter initial.2.1 otsTable ftsTable).otsSecret topLayer rootTree) initial.2.1 initial.2.2 hroot payload

theorem expected_initializeRoot_newTargetCoverageExcess_eq_zero
    (parameter : PublicParameter) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (fuel : Nat) (reference : HashInput) :
    (∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
      newTargetCoverageExcess (secretKey parameter initial.2.1 otsTable ftsTable) initial.2.2 [] reference
        (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) q signatureLimit) = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro initial
  by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
  · rw [newTargetCoverageExcess_initializeRoot_eq_zero parameter otsTable ftsTable q hq fuel reference initial hi, mul_zero]
  · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul]

end JointOriginal
end FtsProbeSimulation
end SphincsSecurity.Concrete
