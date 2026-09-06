import SphincsSecurity.Proof.OtsProbePrivateValueErasedRisk
import SphincsSecurity.Proof.OtsProbeStartPrefixGame

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledNativePrivateErasedCharge
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | sampleOtsHashTable] *
        ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
          privateErasedCandidateCharge target (privateRawCutCandidate target)
            (privatePositionProbeCutAt target (nativeChronologicalRetainedComputation adversary parameter ftsSecret) ordinal)
            (ensuredInitialContext targets) fuel table

theorem sampledInitializedPrivateHitRisk_le_erased_charge
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) :
    sampledInitializedPrivateHitRisk targets adversary fuel q ≤
      sampledNativePrivateErasedCharge targets adversary fuel q * (Fintype.card Digest : ENNReal)⁻¹ := by
  unfold sampledInitializedPrivateHitRisk sampledNativePrivateErasedCharge
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro parameter
  rw [mul_assoc, ← ENNReal.tsum_mul_right]
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  rw [mul_assoc, ← ENNReal.tsum_mul_right]
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro table
  rw [mul_assoc, Finset.sum_mul]
  apply mul_le_mul' le_rfl
  apply Finset.sum_le_sum
  intro target htarget
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ordinal _
  apply probEvent_privateResolvedRawCandidate_le_erased_charge target _ (ensuredInitialContext targets) fuel table ordinal
    (ensuredInitialContext_valid targets) (ensuredInitialContext_completable targets table)
    (ensuredInitialContext_mem_ensured targets target htarget) rfl rfl
  · simp [ensuredInitialContext, LazyRevealProbe.State.empty]
  · simp [ensuredInitialContext, LazyRevealProbe.State.empty, LazyRevealProbe.State.pendingAt]

theorem sampledInitializedNativeDirectRisk_le_erased_prefix_charge
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : q ≤ Fintype.card Digest) :
    sampledInitializedNativeDirectRisk targets adversary fuel q ≤
      (sampledNativeStartPrefixCharge targets adversary fuel q + sampledNativePrivateErasedCharge targets adversary fuel q) *
        (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [add_mul]
  exact (sampledInitializedNativeDirectRisk_le_startPrefix_add_privateRisk targets adversary fuel q hq).trans
    (add_le_add le_rfl (sampledInitializedPrivateHitRisk_le_erased_charge targets adversary fuel q))

theorem sampledNativeTerminalRisk_le_min_erased_prefix_charge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest) :
    sampledNativeTerminalRisk adversary (q + 1) ≤
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((sampledNativeStartPrefixCharge Finset.univ adversary (q + 1) q +
          sampledNativePrivateErasedCharge Finset.univ adversary (q + 1) q) * (Fintype.card Digest : ENNReal)⁻¹) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (sampledNativeTerminalRisk_le_missing_add_erasure_of_querySpace adversary q hq hqSpace).trans
  apply add_le_add _ le_rfl
  apply (sampledNativeMissingAllowances_le_directRisk Finset.univ adversary q hq (q + 1)).trans
  exact le_min (sampledInitializedNativeDirectRisk_le_actualOtsCount_rate Finset.univ adversary (q + 1) q (by omega))
    (sampledInitializedNativeDirectRisk_le_erased_prefix_charge Finset.univ adversary (q + 1) q (by omega))

theorem probEvent_sampledFirstParentOrOtsWitness_le_min_erased_prefix_charge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest) :
    Pr[SampledFirstParentOrOtsWitness | sampledFirstParentRetainedGame adversary] ≤
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((sampledNativeStartPrefixCharge Finset.univ adversary (q + 1) q +
          sampledNativePrivateErasedCharge Finset.univ adversary (q + 1) q) * (Fintype.card Digest : ENNReal)⁻¹) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_sampledFirstParentOrOtsWitness_le_nativeTerminalFailure adversary (q + 1)).trans
  rw [probEvent_sampledNativeTerminalFailure_eq_risk]
  exact sampledNativeTerminalRisk_le_min_erased_prefix_charge adversary q hq hqSpace

end SphincsSecurity.Concrete.OtsProbeSimulation
