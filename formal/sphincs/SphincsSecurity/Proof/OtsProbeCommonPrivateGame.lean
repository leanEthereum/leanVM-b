import SphincsSecurity.Proof.OtsProbeCommonPrivateCharge
import SphincsSecurity.Proof.OtsProbePrivateErasedGame

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledNativeCommonStructuralCharge
    (targets : Finset Position) (adversary : Adversary) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | sampleOtsHashTable] *
        erasedStructuralQueryCharge (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
          (ensuredInitialContext targets) table

theorem sampledNativePrivateErasedCharge_le_common
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) :
    sampledNativePrivateErasedCharge targets adversary fuel q ≤ sampledNativeCommonStructuralCharge targets adversary := by
  unfold sampledNativePrivateErasedCharge sampledNativeCommonStructuralCharge
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro table
  apply mul_le_mul' le_rfl
  apply le_trans _ (sum_commonPrivateCutCharge_le_erasedStructuralCharge targets _ (ensuredInitialContext targets) table q)
  apply Finset.sum_le_sum
  intro target htarget
  apply Finset.sum_le_sum
  intro ordinal _
  apply privateErasedCandidateCharge_le_common target _ (ensuredInitialContext targets) fuel table ordinal
    (ensuredInitialContext_valid targets) (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table))
    _ (ensuredInitialContext_mem_ensured targets target htarget) rfl rfl
  intro coordinate hmem
  simp [ensuredInitialContext, LazyRevealProbe.State.empty] at hmem

theorem sampledInitializedPrivateHitRisk_le_common_charge
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) :
    sampledInitializedPrivateHitRisk targets adversary fuel q ≤
      sampledNativeCommonStructuralCharge targets adversary * (Fintype.card Digest : ENNReal)⁻¹ :=
  (sampledInitializedPrivateHitRisk_le_erased_charge targets adversary fuel q).trans
    (mul_le_mul' (sampledNativePrivateErasedCharge_le_common targets adversary fuel q) le_rfl)

theorem sampledInitializedNativeDirectRisk_le_common_prefix_charge
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : q ≤ Fintype.card Digest) :
    sampledInitializedNativeDirectRisk targets adversary fuel q ≤
      (sampledNativeStartPrefixCharge targets adversary fuel q + sampledNativeCommonStructuralCharge targets adversary) *
        (Fintype.card Digest : ENNReal)⁻¹ := by
  exact (sampledInitializedNativeDirectRisk_le_erased_prefix_charge targets adversary fuel q hq).trans
    (mul_le_mul' (add_le_add le_rfl (sampledNativePrivateErasedCharge_le_common targets adversary fuel q)) le_rfl)

theorem sampledNativeTerminalRisk_le_min_common_prefix_charge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest) :
    sampledNativeTerminalRisk adversary (q + 1) ≤
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((sampledNativeStartPrefixCharge Finset.univ adversary (q + 1) q +
          sampledNativeCommonStructuralCharge Finset.univ adversary) * (Fintype.card Digest : ENNReal)⁻¹) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (sampledNativeTerminalRisk_le_missing_add_erasure_of_querySpace adversary q hq hqSpace).trans
  apply add_le_add _ le_rfl
  apply (sampledNativeMissingAllowances_le_directRisk Finset.univ adversary q hq (q + 1)).trans
  exact le_min (sampledInitializedNativeDirectRisk_le_actualOtsCount_rate Finset.univ adversary (q + 1) q (by omega))
    (sampledInitializedNativeDirectRisk_le_common_prefix_charge Finset.univ adversary (q + 1) q (by omega))

theorem probEvent_sampledFirstParentOrOtsWitness_le_min_common_prefix_charge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest) :
    Pr[SampledFirstParentOrOtsWitness | sampledFirstParentRetainedGame adversary] ≤
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((sampledNativeStartPrefixCharge Finset.univ adversary (q + 1) q +
          sampledNativeCommonStructuralCharge Finset.univ adversary) * (Fintype.card Digest : ENNReal)⁻¹) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_sampledFirstParentOrOtsWitness_le_nativeTerminalFailure adversary (q + 1)).trans
  rw [probEvent_sampledNativeTerminalFailure_eq_risk]
  exact sampledNativeTerminalRisk_le_min_common_prefix_charge adversary q hq hqSpace

end SphincsSecurity.Concrete.OtsProbeSimulation
