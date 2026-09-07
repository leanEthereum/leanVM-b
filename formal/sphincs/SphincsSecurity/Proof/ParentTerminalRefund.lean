import SphincsSecurity.Proof.InitializedParentReserveConservation

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable parentReserve
set_option backward.isDefEq.respectTransparency false

private theorem factor_parent_credit (weight pending discarded rate : ENNReal) :
    2 * (weight * pending) * rate + (weight * discarded) * rate = weight * (2 * pending * rate + discarded * rate) := by ring

theorem twice_terminalPendingParentCount_add_discard_scaled_le
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool)
    (hfinite : Finite result.1.2.1.2) (hcap : QueryCache.enncard result.1.2.1.2 ≤ (Fintype.card Digest : ENNReal)) :
    2 * (terminalPendingParentCount parameter otsTable ftsTable result : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ +
      terminalParentDiscard parameter otsTable ftsTable result * (Fintype.card Digest : ENNReal)⁻¹ ≤
      collisionTerminalReserve parameter otsTable ftsTable result := by
  by_cases hs : SurvivingStructuralFailure parameter otsTable ftsTable result
  · have hz : terminalPendingParentCount parameter otsTable ftsTable result = 0 := by
      simp only [terminalPendingParentCount, hs, not_true_eq_false, and_false, if_false]
    rw [hz, Nat.cast_zero, mul_zero, zero_mul, zero_add, terminalParentDiscard, if_pos hs,
      collisionTerminalReserve, if_pos hs]
    cases hh : result.1.2.2 <;> cases hf : result.2 <;>
      simp only [jointSurvivingCachePotential, survivingFtsParentReserve, Bool.false_eq_true, if_false,
        if_true, Bool.false_or, Bool.true_or, zero_mul] <;> exact le_rfl
  · rw [terminalParentDiscard, if_neg hs, zero_mul, add_zero]
    exact twice_terminalPendingParentCount_scaled_le parameter otsTable ftsTable result hfinite hcap

noncomputable def initializedTerminalParentDiscard
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : ENNReal :=
  ∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable)
    adversary parameter otsTable ftsTable q fuel] * terminalParentDiscard parameter otsTable ftsTable result

theorem twice_initializedPendingParentCount_add_discard_scaled_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    2 * initializedPendingParentCount adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      initializedTerminalParentDiscard adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤
      initializedCollisionTerminalReserve adversary parameter otsTable ftsTable q fuel := by
  rw [initializedPendingParentCount, initializedTerminalParentDiscard, initializedCollisionTerminalReserve,
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [factor_parent_credit]
  by_cases hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel)
  · apply mul_le_mul' le_rfl
    apply twice_terminalPendingParentCount_add_discard_scaled_le parameter otsTable ftsTable result
      (runRetainedWithFailure_cache_finite _ adversary parameter otsTable ftsTable q fuel result hr)
    apply (runRetainedWithFailure_cache_le_queryBound _ adversary q hq parameter hp otsTable ftsTable hfts fuel result hr).trans
    apply Nat.cast_le.mpr
    rw [show Fintype.card Digest = 2 ^ 128 from card_bitVec digestBits]
    omega
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

noncomputable def sampledTerminalParentDiscard (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedTerminalParentDiscard adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

theorem twice_sampledPendingParentCount_add_discard_scaled_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    2 * sampledPendingParentCount adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledTerminalParentDiscard adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤ sampledCollisionTerminalReserve adversary q fuel := by
  unfold sampledPendingParentCount sampledTerminalParentDiscard sampledCollisionTerminalReserve
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro parameter
  rw [factor_parent_credit]
  by_cases hp : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    rw [factor_parent_credit]
    apply mul_le_mul' le_rfl
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro table
    rw [factor_parent_credit]
    exact mul_le_mul' le_rfl (twice_initializedPendingParentCount_add_discard_scaled_le adversary q hq hqMax parameter hp table
      (curryFtsTableEquiv ftsSecret) (mem_support_sampleFtsSecrets ftsSecret) fuel)
  · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
