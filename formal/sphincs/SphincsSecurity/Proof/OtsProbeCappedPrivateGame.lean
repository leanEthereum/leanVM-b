import SphincsSecurity.Proof.OtsProbeLiveProbeCap

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

theorem sum_privateResolvedRawCandidate_le_capped_common
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (q : Nat)
    (hbound : LiveResolvedQueryBound LazyRevealProbe.IsProbe computation q (ensuredInitialContext targets) fuel table) :
    (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table (ensuredInitialContext targets) fuel
          (privatePositionProbeCutAt target computation ordinal)]) ≤
    erasedStructuralQueryCharge (capProbeQueries computation q) (ensuredInitialContext targets) table *
      (Fintype.card Digest : ENNReal)⁻¹ := by
  have hvalid := ensuredInitialContext_valid targets
  have hcomplete := ensuredInitialContext_completable targets table
  have hstarts := startTableAgrees_of_deferredCompletable hcomplete
  calc
    _ ≤ ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        commonPrivateCutCharge target (capProbeQueries computation q) (ensuredInitialContext targets) table ordinal *
          (Fintype.card Digest : ENNReal)⁻¹ := by
      apply Finset.sum_le_sum
      intro target htarget
      apply Finset.sum_le_sum
      intro ordinal _
      rw [probEvent_congr' (fun _ _ => Iff.rfl)
        (evalDist_privateResolvedRawCandidate_cap target computation (ensuredInitialContext targets) fuel table q ordinal
          hvalid.valuesConsistent hstarts hbound)]
      apply (probEvent_privateResolvedRawCandidate_le_erased_charge target _ (ensuredInitialContext targets) fuel table ordinal
        hvalid hcomplete (ensuredInitialContext_mem_ensured targets target htarget) rfl rfl
        (by simp [ensuredInitialContext, LazyRevealProbe.State.empty])
        (by simp [ensuredInitialContext, LazyRevealProbe.State.empty, LazyRevealProbe.State.pendingAt])).trans
      apply mul_le_mul' _ le_rfl
      apply privateErasedCandidateCharge_le_common target _ (ensuredInitialContext targets) fuel table ordinal
        hvalid hstarts _ (ensuredInitialContext_mem_ensured targets target htarget) rfl rfl
      intro coordinate hmem
      simp [ensuredInitialContext, LazyRevealProbe.State.empty] at hmem
    _ = (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        commonPrivateCutCharge target (capProbeQueries computation q) (ensuredInitialContext targets) table ordinal) *
          (Fintype.card Digest : ENNReal)⁻¹ := by simp_rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul'
      (sum_commonPrivateCutCharge_le_erasedStructuralCharge targets _ (ensuredInitialContext targets) table q) le_rfl

noncomputable def sampledNativeCappedStructuralCharge
    (targets : Finset Position) (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | sampleOtsHashTable] *
        erasedStructuralQueryCharge (capProbeQueries (nativeChronologicalRetainedComputation adversary parameter ftsSecret) q)
          (ensuredInitialContext targets) table

theorem sampledNativeCappedStructuralCharge_le
    (targets : Finset Position) (adversary : Adversary) (q : Nat) :
    sampledNativeCappedStructuralCharge targets adversary q ≤ q := by
  unfold sampledNativeCappedStructuralCharge
  calc
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ∑' table, Pr[= table | sampleOtsHashTable] * (q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro parameter
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro table
      exact mul_le_mul' le_rfl
        (erasedStructuralQueryCharge_le_probeBound _ _ table q (capProbeQueries_probeBound _ q))
    _ ≤ _ := by
      simp_rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one
        (mul_le_mul' tsum_probOutput_le_one (mul_le_mul' tsum_probOutput_le_one le_rfl))).trans_eq (by simp)

theorem sampledInitializedPrivateHitRisk_le_capped_charge
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : HasHashQueryBound scheme adversary q) :
    sampledInitializedPrivateHitRisk targets adversary fuel q ≤
      sampledNativeCappedStructuralCharge targets adversary q * (Fintype.card Digest : ENNReal)⁻¹ := by
  unfold sampledInitializedPrivateHitRisk sampledNativeCappedStructuralCharge
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hparameter : parameter ∈ support sampleParameter
  · rw [mul_assoc, ← ENNReal.tsum_mul_right]
    apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    by_cases hfts : ftsSecret ∈ support sampleFtsSecrets
    · rw [mul_assoc, ← ENNReal.tsum_mul_right]
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro table
      rw [mul_assoc]
      apply mul_le_mul' le_rfl
      exact sum_privateResolvedRawCandidate_le_capped_common targets _ fuel table q
        (liveResolvedProbeBound_nativeRetained_of_gameBudget targets adversary q hq parameter hparameter table ftsSecret hfts fuel)
    · simp [probOutput_eq_zero_of_not_mem_support hfts]
  · simp [probOutput_eq_zero_of_not_mem_support hparameter]

theorem sampledInitializedPrivateHitRisk_le_query_budget
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : HasHashQueryBound scheme adversary q) :
    sampledInitializedPrivateHitRisk targets adversary fuel q ≤
      (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ :=
  (sampledInitializedPrivateHitRisk_le_capped_charge targets adversary fuel q hq).trans
    (mul_le_mul' (sampledNativeCappedStructuralCharge_le targets adversary q) le_rfl)

theorem sampledInitializedNativeDirectRisk_le_capped_prefix_charge
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat)
    (hq : HasHashQueryBound scheme adversary q) (hqSpace : q ≤ Fintype.card Digest) :
    sampledInitializedNativeDirectRisk targets adversary fuel q ≤
      (sampledNativeStartPrefixCharge targets adversary fuel q + sampledNativeCappedStructuralCharge targets adversary q) *
        (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [add_mul]
  exact (sampledInitializedNativeDirectRisk_le_startPrefix_add_privateRisk targets adversary fuel q hqSpace).trans
    (add_le_add le_rfl (sampledInitializedPrivateHitRisk_le_capped_charge targets adversary fuel q hq))

theorem sampledNativeTerminalRisk_le_min_capped_prefix_charge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest) :
    sampledNativeTerminalRisk adversary (q + 1) ≤
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((sampledNativeStartPrefixCharge Finset.univ adversary (q + 1) q +
          sampledNativeCappedStructuralCharge Finset.univ adversary q) * (Fintype.card Digest : ENNReal)⁻¹) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (sampledNativeTerminalRisk_le_missing_add_erasure_of_querySpace adversary q hq hqSpace).trans
  apply add_le_add _ le_rfl
  apply (sampledNativeMissingAllowances_le_directRisk Finset.univ adversary q hq (q + 1)).trans
  exact le_min (sampledInitializedNativeDirectRisk_le_actualOtsCount_rate Finset.univ adversary (q + 1) q (by omega))
    (sampledInitializedNativeDirectRisk_le_capped_prefix_charge Finset.univ adversary (q + 1) q hq (by omega))

theorem probEvent_sampledFirstParentOrOtsWitness_le_min_capped_prefix_charge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest) :
    Pr[SampledFirstParentOrOtsWitness | sampledFirstParentRetainedGame adversary] ≤
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((sampledNativeStartPrefixCharge Finset.univ adversary (q + 1) q +
          sampledNativeCappedStructuralCharge Finset.univ adversary q) * (Fintype.card Digest : ENNReal)⁻¹) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_sampledFirstParentOrOtsWitness_le_nativeTerminalFailure adversary (q + 1)).trans
  rw [probEvent_sampledNativeTerminalFailure_eq_risk]
  exact sampledNativeTerminalRisk_le_min_capped_prefix_charge adversary q hq hqSpace

end SphincsSecurity.Concrete.OtsProbeSimulation
