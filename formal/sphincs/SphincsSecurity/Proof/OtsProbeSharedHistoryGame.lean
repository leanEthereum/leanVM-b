import SphincsSecurity.Proof.OtsProbeHistoryCutCounting

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledNativeHistoryStartCharge
    (targets : Finset Position) (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑ ordinal ∈ Finset.range q,
        erasedHistoryStartCutCharge (capProbeQueries (nativeChronologicalRetainedComputation adversary parameter ftsSecret) q)
          (ensuredInitialContext targets) ordinal

noncomputable def sampledNativeHistoryPrivateCharge
    (targets : Finset Position) (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        erasedHistoryPrivateCutCharge target (capProbeQueries (nativeChronologicalRetainedComputation adversary parameter ftsSecret) q)
          (ensuredInitialContext targets) ordinal

theorem sampledNativeStartPrefixCharge_le_sharedHistory
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : q ≤ Fintype.card Digest) :
    sampledNativeStartPrefixCharge targets adversary fuel q ≤ sampledNativeHistoryStartCharge targets adversary q := by
  unfold sampledNativeStartPrefixCharge sampledNativeHistoryStartCharge
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  apply mul_le_mul' le_rfl
  apply Finset.sum_le_sum
  intro ordinal hordinal
  have hord : ordinal < q := Finset.mem_range.mp hordinal
  exact (nativeStartPrefixCharge_le_erasedHistoryStartCutCharge targets _ fuel ordinal (hord.trans_le hq)).trans_eq
    (erasedHistoryStartCutCharge_cap _ (ensuredInitialContext targets) q ordinal hord)

theorem sampled_privateResolvedRawCandidate_le_history_charge
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel q : Nat)
    (hbound : ∀ table, LiveResolvedQueryBound LazyRevealProbe.IsProbe computation q (ensuredInitialContext targets) fuel table) :
    (∑' table, Pr[= table | sampleOtsHashTable] *
      ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
          runPrivateResolvedView target table (ensuredInitialContext targets) fuel (privatePositionProbeCutAt target computation ordinal)]) ≤
      (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        erasedHistoryPrivateCutCharge target (capProbeQueries computation q) (ensuredInitialContext targets) ordinal) *
        (Fintype.card Digest : ENNReal)⁻¹ := by
  calc
    _ ≤ ∑' table, Pr[= table | sampleOtsHashTable] *
        ((∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
          commonPrivateCutCharge target (capProbeQueries computation q) (ensuredInitialContext targets) table ordinal) *
          (Fintype.card Digest : ENNReal)⁻¹) := by
      apply ENNReal.tsum_le_tsum
      intro table
      exact mul_le_mul' le_rfl (sum_privateResolvedRawCandidate_le_capped_common_cuts targets computation fuel table q (hbound table))
    _ = (∑' table, Pr[= table | sampleOtsHashTable] *
        ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
          commonPrivateCutCharge target (capProbeQueries computation q) (ensuredInitialContext targets) table ordinal) *
          (Fintype.card Digest : ENNReal)⁻¹ := by simp_rw [← mul_assoc, ENNReal.tsum_mul_right]
    _ = _ := by rw [sampled_sum_commonPrivateCutCharge_eq_erasedHistory]

theorem sampledInitializedPrivateHitRisk_le_sharedHistory
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : HasHashQueryBound scheme adversary q) :
    sampledInitializedPrivateHitRisk targets adversary fuel q ≤
      sampledNativeHistoryPrivateCharge targets adversary q * (Fintype.card Digest : ENNReal)⁻¹ := by
  unfold sampledInitializedPrivateHitRisk sampledNativeHistoryPrivateCharge
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hparameter : parameter ∈ support sampleParameter
  · rw [mul_assoc, ← ENNReal.tsum_mul_right]
    apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    by_cases hfts : ftsSecret ∈ support sampleFtsSecrets
    · rw [mul_assoc]
      apply mul_le_mul' le_rfl
      exact sampled_privateResolvedRawCandidate_le_history_charge targets _ fuel q
        (fun table => liveResolvedProbeBound_nativeRetained_of_gameBudget targets adversary q hq parameter hparameter table ftsSecret hfts fuel)
    · simp [probOutput_eq_zero_of_not_mem_support hfts]
  · simp [probOutput_eq_zero_of_not_mem_support hparameter]

theorem sampledInitializedNativeDirectRisk_le_sharedHistory
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat)
    (hq : HasHashQueryBound scheme adversary q) (hqSpace : q ≤ Fintype.card Digest) :
    sampledInitializedNativeDirectRisk targets adversary fuel q ≤
      (sampledNativeHistoryStartCharge targets adversary q + sampledNativeHistoryPrivateCharge targets adversary q) *
        (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [add_mul]
  exact (sampledInitializedNativeDirectRisk_le_startPrefix_add_privateRisk targets adversary fuel q hqSpace).trans
    (add_le_add (mul_le_mul' (sampledNativeStartPrefixCharge_le_sharedHistory targets adversary fuel q hqSpace) le_rfl)
      (sampledInitializedPrivateHitRisk_le_sharedHistory targets adversary fuel q hq))

theorem sampledNativeHistoryCharge_le_query_budget
    (targets : Finset Position) (adversary : Adversary) (q : Nat) :
    sampledNativeHistoryStartCharge targets adversary q + sampledNativeHistoryPrivateCharge targets adversary q ≤ q := by
  unfold sampledNativeHistoryStartCharge sampledNativeHistoryPrivateCharge
  rw [← ENNReal.tsum_add]
  calc
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] * (q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro parameter
      rw [← mul_add, ← ENNReal.tsum_add]
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      rw [← mul_add]
      apply mul_le_mul' le_rfl
      exact sharedHistoryCutCharge_le_probeBound targets _ (ensuredInitialContext targets) q q (capProbeQueries_probeBound _ q)
    _ ≤ _ := by
      simp_rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one (mul_le_mul' tsum_probOutput_le_one le_rfl)).trans_eq (by simp)

theorem sampledInitializedNativeDirectRisk_le_query_budget
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat)
    (hq : HasHashQueryBound scheme adversary q) (hqSpace : q ≤ Fintype.card Digest) :
    sampledInitializedNativeDirectRisk targets adversary fuel q ≤ (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ :=
  (sampledInitializedNativeDirectRisk_le_sharedHistory targets adversary fuel q hq hqSpace).trans
    (mul_le_mul' (sampledNativeHistoryCharge_le_query_budget targets adversary q) le_rfl)

theorem sampledNativeTerminalRisk_le_min_sharedHistory
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest) :
    sampledNativeTerminalRisk adversary (q + 1) ≤
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((sampledNativeHistoryStartCharge Finset.univ adversary q +
          sampledNativeHistoryPrivateCharge Finset.univ adversary q) * (Fintype.card Digest : ENNReal)⁻¹) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (sampledNativeTerminalRisk_le_missing_add_erasure_of_querySpace adversary q hq hqSpace).trans
  apply add_le_add _ le_rfl
  apply (sampledNativeMissingAllowances_le_directRisk Finset.univ adversary q hq (q + 1)).trans
  exact le_min (sampledInitializedNativeDirectRisk_le_actualOtsCount_rate Finset.univ adversary (q + 1) q (by omega))
    (sampledInitializedNativeDirectRisk_le_sharedHistory Finset.univ adversary (q + 1) q hq (by omega))

theorem probEvent_sampledFirstParentOrOtsWitness_le_min_sharedHistory
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest) :
    Pr[SampledFirstParentOrOtsWitness | sampledFirstParentRetainedGame adversary] ≤
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((sampledNativeHistoryStartCharge Finset.univ adversary q +
          sampledNativeHistoryPrivateCharge Finset.univ adversary q) * (Fintype.card Digest : ENNReal)⁻¹) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_sampledFirstParentOrOtsWitness_le_nativeTerminalFailure adversary (q + 1)).trans
  rw [probEvent_sampledNativeTerminalFailure_eq_risk]
  exact sampledNativeTerminalRisk_le_min_sharedHistory adversary q hq hqSpace

theorem probEvent_sampledFirstParentOrOtsWitness_le_query_budget
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest) :
    Pr[SampledFirstParentOrOtsWitness | sampledFirstParentRetainedGame adversary] ≤
      (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_sampledFirstParentOrOtsWitness_le_min_sharedHistory adversary q hq hqSpace).trans
  exact add_le_add ((min_le_right _ _).trans
    (mul_le_mul' (sampledNativeHistoryCharge_le_query_budget Finset.univ adversary q) le_rfl)) le_rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
