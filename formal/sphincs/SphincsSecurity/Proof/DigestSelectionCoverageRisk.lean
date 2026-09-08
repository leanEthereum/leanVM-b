import SphincsSecurity.Proof.SigningCollisionCoverage
import SphincsSecurity.Proof.EncodingSigningFailure
import SphincsSecurity.Proof.EncodingExhaustionTotalPotential
import SphincsSecurity.Proof.InterleavedMass

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expected_encodingExhaustionTotalPotential_run (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run cache] * encodingExhaustionTotalPotential result.2) =
      encodingExhaustionTotalPotential cache := by
  simp only [encodingExhaustionTotalPotential, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro family _
  exact expected_encodingExhaustionPotential_run _ computation cache

theorem signAfterDigest_none_encodingExhaustion (key : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : DigestTree → FtsLeaf) (before after : QueryCache HashSpec)
    (hr : (none, after) ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (signAfterDigest key randomness index leaves)).run before)) :
    1 ≤ encodingExhaustionTotalPotential after := by
  obtain ⟨_, f, hagrees, hfailed, hcached⟩ := exists_answerFn_replay_of_mem_support _ _ _ _ hr
  exact one_le_encodingExhaustionTotalPotential_of_exhausted
    (anyEncodingInputsExhausted_of_cachedOtsEncodingFailure after
      (cachedOtsEncodingFailure_of_signAfterDigest_none f after key randomness index leaves hagrees hcached hfailed))

theorem signAfterDigest_boundedCoverage_le_completion (key : SecretKey) (cap budget : Nat)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) (before after : QueryCache HashSpec)
    (signature : Option Signature) (hr : (signature, after) ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (signAfterDigest key randomness index leaves)).run before)) (message : Message) (log : QueryLog SigningSpec) :
    boundedRemainingCoveragePotential key cap budget (before, log ++ [⟨message, some (coverageSignature randomness)⟩]) ≤
      boundedRemainingCoveragePotential key cap budget (after, log ++ [⟨message, signature⟩]) +
        encodingExhaustionTotalPotential after := by
  cases signature with
  | none =>
      exact (boundedRemainingCoveragePotential_le_one _ _ _ _).trans
        ((signAfterDigest_none_encodingExhaustion key randomness index leaves before after hr).trans le_add_self)
  | some signature =>
      have heq := signAfterDigest_remainingCoveragePotential_eq key cap budget randomness index leaves before after signature hr
        message log (coverageSignature randomness) rfl ∅ Finset.univ (by constructor <;> simp)
      unfold boundedRemainingCoveragePotential
      rw [heq]
      exact le_self_add

theorem signAfterDigest_boundedCoverage_le_expected (key : SecretKey) (cap budget : Nat)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) (cache : QueryCache HashSpec)
    (message : Message) (log : QueryLog SigningSpec) :
    boundedRemainingCoveragePotential key cap budget (cache, log ++ [⟨message, some (coverageSignature randomness)⟩]) ≤
      (∑' result, Pr[= result | (simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAfterDigest key randomness index leaves)).run cache] *
          boundedRemainingCoveragePotential key cap budget (result.2, log ++ [⟨message, result.1⟩])) +
        encodingExhaustionTotalPotential cache := by
  let computation := signAfterDigest key randomness index leaves
  have hmass := simulateQ_run_mass_of_query_mass romImpl romImpl_query_mass (liftM computation : OracleComp OracleWorld _) cache
  rw [simulateQ_romImpl_liftM] at hmass
  have hexhaust := expected_encodingExhaustionTotalPotential_run (liftM computation : OracleComp OracleWorld _) cache
  rw [simulateQ_romImpl_liftM] at hexhaust
  calc
    _ = ∑' result, Pr[= result | (simulateQ (randomOracle : QueryImpl HashSpec _) computation).run cache] *
        boundedRemainingCoveragePotential key cap budget (cache, log ++ [⟨message, some (coverageSignature randomness)⟩]) := by
      rw [ENNReal.tsum_mul_right, hmass, one_mul]
    _ ≤ ∑' result, Pr[= result | (simulateQ (randomOracle : QueryImpl HashSpec _) computation).run cache] *
        (boundedRemainingCoveragePotential key cap budget (result.2, log ++ [⟨message, result.1⟩]) +
          encodingExhaustionTotalPotential result.2) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run cache)
      · exact mul_le_mul' le_rfl (signAfterDigest_boundedCoverage_le_completion key cap budget randomness index leaves cache result.2 result.1 hr message log)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add]
      rw [hexhaust]

theorem digestSelectionCoverageRisk_le_signing_add_exhaustion (key : SecretKey) (cap budget : Nat)
    (message : Message) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) :
    digestSelectionCoverageRisk key cap budget message cache log ≤
      (∑' result, Pr[= result | (simulateQ romImpl (sign key message)).run cache] *
        boundedRemainingCoveragePotential key cap budget (result.2, log ++ [⟨message, result.1⟩])) +
          encodingExhaustionTotalPotential cache := by
  rw [← expected_encodingExhaustionTotalPotential_run (signDigestLoop digestAttemptLimit key message) cache]
  rw [sign_eq_digestLoop_afterDigest, simulateQ_bind, StateT.run_bind, tsum_probOutput_bind_mul, digestSelectionCoverageRisk,
    ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [← mul_add]
  apply mul_le_mul' le_rfl
  rcases result with ⟨selected, after⟩
  cases selected with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, digestSelectionCoverageState, Option.map_none]
      exact le_self_add
  | some data =>
      rcases data with ⟨randomness, index, leaves⟩
      rw [simulateQ_romImpl_liftM]
      exact signAfterDigest_boundedCoverage_le_expected key cap budget randomness index leaves after message log

theorem digestSelectionCoverageRisk_le_one (key : SecretKey) (cap budget : Nat)
    (message : Message) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) :
    digestSelectionCoverageRisk key cap budget message cache log ≤ 1 := by
  apply le_trans (ENNReal.tsum_le_tsum (fun result => mul_le_mul' le_rfl (boundedRemainingCoveragePotential_le_one key cap budget _)))
  simpa only [mul_one] using (tsum_probOutput_le_one (mx := (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache))

end SphincsSecurity.Concrete
