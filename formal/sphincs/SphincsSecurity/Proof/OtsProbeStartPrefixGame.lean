import SphincsSecurity.Proof.OtsProbeStartPrefixCharge
import SphincsSecurity.Proof.FirstParentOtsGame

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem prefixUnresolvedStartCharge_le_one
    (candidate : DeferredContext → α → Option Probe) (entry : Option (HistoryResolvedPrefix α)) :
    prefixUnresolvedStartCharge candidate entry ≤ 1 := by
  cases entry with
  | none => exact zero_le_one
  | some entry =>
      simp only [prefixUnresolvedStartCharge]
      cases hcandidate : candidate entry.context entry.value with
      | none => simp [unresolvedStartCandidateCharge]
      | some probe =>
          rcases probe with ⟨coordinate, digest⟩
          cases coordinate with
          | position position => simp [unresolvedStartCandidateCharge]
          | chainStart lay tree leafIdx chainIdx =>
              simp only [unresolvedStartCandidateCharge]
              split_ifs
              · exact_mod_cast (Nat.le_add_right _ _).trans
                  (candidateCharge_sum_le_one (materializedDeferredState entry.context) (some ⟨.chainStart lay tree leafIdx chainIdx, digest⟩))
              · exact zero_le_one

theorem nativeStartPrefixCharge_le_one
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel ordinal : Nat) :
    nativeStartPrefixCharge targets computation fuel ordinal ≤ 1 := by
  unfold nativeStartPrefixCharge
  calc
    _ ≤ ∑' entry, Pr[= entry | runResolvedHistoryPrefix (nativeProbeCutAt computation ordinal) (ensuredInitialContext targets) fuel []] * 1 :=
      ENNReal.tsum_le_tsum fun entry => mul_le_mul' le_rfl (prefixUnresolvedStartCharge_le_one nativeCutCandidate entry)
    _ ≤ _ := by simp only [mul_one]; exact tsum_probOutput_le_one

noncomputable def sampledNativeStartPrefixCharge
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑ ordinal ∈ Finset.range q,
        nativeStartPrefixCharge targets (nativeChronologicalRetainedComputation adversary parameter ftsSecret) fuel ordinal

theorem sampledNativeStartPrefixCharge_le (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) :
    sampledNativeStartPrefixCharge targets adversary fuel q ≤ q := by
  unfold sampledNativeStartPrefixCharge
  calc
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] * (q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro parameter
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      apply mul_le_mul' le_rfl
      calc
        _ ≤ ∑ _ordinal ∈ Finset.range q, (1 : ENNReal) :=
          Finset.sum_le_sum fun ordinal _ => nativeStartPrefixCharge_le_one targets _ fuel ordinal
        _ = _ := by simp
    _ ≤ _ := by
      simp_rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one (mul_le_mul' tsum_probOutput_le_one le_rfl)).trans_eq (by simp)

theorem sampledInitializedNativeDirectRisk_le_startPrefix_add_privateRisk
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : q ≤ Fintype.card Digest) :
    sampledInitializedNativeDirectRisk targets adversary fuel q ≤
      sampledNativeStartPrefixCharge targets adversary fuel q * (Fintype.card Digest : ENNReal)⁻¹ +
        sampledInitializedPrivateHitRisk targets adversary fuel q := by
  unfold sampledInitializedNativeDirectRisk initializedNativeDirectRisk sampledNativeStartPrefixCharge sampledInitializedPrivateHitRisk
  simp only [mul_add, ENNReal.tsum_add]
  apply add_le_add _ le_rfl
  simp_rw [← ENNReal.tsum_mul_right, mul_assoc]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  rw [mul_assoc]
  exact mul_le_mul' le_rfl (sum_sampledEnsuredNativeProbeCut_unresolvedStart_le_prefixCharge targets _ fuel q hq)

theorem sampledNativeTerminalRisk_le_min_startPrefix_add_privateRisk
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest) :
    sampledNativeTerminalRisk adversary (q + 1) ≤
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        (sampledNativeStartPrefixCharge Finset.univ adversary (q + 1) q * (Fintype.card Digest : ENNReal)⁻¹ +
          sampledInitializedPrivateHitRisk Finset.univ adversary (q + 1) q) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (sampledNativeTerminalRisk_le_missing_add_erasure_of_querySpace adversary q hq hqSpace).trans
  apply add_le_add _ le_rfl
  apply (sampledNativeMissingAllowances_le_directRisk Finset.univ adversary q hq (q + 1)).trans
  exact le_min (sampledInitializedNativeDirectRisk_le_actualOtsCount_rate Finset.univ adversary (q + 1) q (by omega))
    (sampledInitializedNativeDirectRisk_le_startPrefix_add_privateRisk Finset.univ adversary (q + 1) q (by omega))

theorem probEvent_sampledFirstParentOrOtsWitness_le_min_startPrefix_add_privateRisk
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest) :
    Pr[SampledFirstParentOrOtsWitness | sampledFirstParentRetainedGame adversary] ≤
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        (sampledNativeStartPrefixCharge Finset.univ adversary (q + 1) q * (Fintype.card Digest : ENNReal)⁻¹ +
          sampledInitializedPrivateHitRisk Finset.univ adversary (q + 1) q) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_sampledFirstParentOrOtsWitness_le_nativeTerminalFailure adversary (q + 1)).trans
  rw [probEvent_sampledNativeTerminalFailure_eq_risk]
  exact sampledNativeTerminalRisk_le_min_startPrefix_add_privateRisk adversary q hq hqSpace

end SphincsSecurity.Concrete.OtsProbeSimulation
