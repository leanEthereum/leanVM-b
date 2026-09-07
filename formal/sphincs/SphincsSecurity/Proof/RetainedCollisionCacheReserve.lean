import SphincsSecurity.Proof.SecurityCollisionTerminalReserve
import SphincsSecurity.Proof.InterleavedCoverGame

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable parentReserve
set_option backward.isDefEq.respectTransparency false

private theorem actualRetainedGameAfterTable_eq_ftsAfterSecrets
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) :
    OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter (fun index tree leaf => ftsTable (index, tree, leaf))
      (OtsProbeSimulation.extendStartTable otsTable) =
      actualRetainedGameAfterSecrets adversary parameter
        (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)) ftsTable := by
  unfold OtsProbeSimulation.actualRetainedGameAfterTable actualRetainedGameAfterSecrets
  apply bind_congr
  rintro ⟨root, cache⟩
  dsimp only
  rw [show OtsProbeSimulation.retainedGameRestComputation adversary ⟨root, parameter⟩ =
    retainedGameRestComputation adversary ⟨root, parameter⟩ from rfl]

theorem runRetainedWithFailure_cache_le_queryBound
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat)
    (result) (hr : result ∈ support (runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel)) :
    QueryCache.enncard result.1.2.1.2 ≤ q := by
  have hproject : result.1.2.1 ∈ support ((fun pair => pair.2.1) <$> runRetained exception adversary parameter otsTable ftsTable q fuel) := by
    rw [support_map]
    exact ⟨result.1, runRetainedWithFailure_support_project exception adversary parameter otsTable ftsTable q fuel result hr, rfl⟩
  rw [runRetained_originalActual exception adversary q hq parameter hp otsTable ftsTable hfts fuel, support_map] at hproject
  obtain ⟨actual, ha, heq⟩ := hproject
  have ha' : actual ∈ support (OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter
      (fun index tree leaf => ftsTable (index, tree, leaf)) (OtsProbeSimulation.extendStartTable otsTable)) :=
    (mem_support_iff_evalDist_apply_ne_zero _ _).2 ((SPMF.mem_support_iff _ _).1 ha)
  rw [actualRetainedGameAfterTable_eq_ftsAfterSecrets] at ha'
  have hc : actual.2 = result.1.2.1.2 := congrArg Prod.snd heq
  rw [← hc]
  let otsSecret := OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)
  apply actualRetainedGameAfterSecrets_cache_bound adversary parameter otsSecret ftsTable q
    (isQueryBoundP_gameAfterSecrets adversary q hq hp (OtsProbeSimulation.mem_support_sampleOtsSecrets_all otsSecret) hfts) actual
  exact ha'

noncomputable def terminalPendingParentCount
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool) : Nat :=
  if result.1.2.2 = false ∧ result.2 = false ∧ ¬ SurvivingStructuralFailure parameter otsTable ftsTable result then
    parentReserve parameter (secretKey parameter default otsTable ftsTable).otsSecret
      (secretKey parameter default otsTable ftsTable).ftsSecret
      (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) result.1.2.1.2
  else 0

theorem twice_terminalPendingParentCount_scaled_le
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool)
    (hfinite : Finite result.1.2.1.2) (hcap : QueryCache.enncard result.1.2.1.2 ≤ (Fintype.card Digest : ENNReal)) :
    2 * (terminalPendingParentCount parameter otsTable ftsTable result : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ ≤
      collisionTerminalReserve parameter otsTable ftsTable result := by
  unfold terminalPendingParentCount
  split_ifs with h
  · exact twice_parentReserve_scaled_le_collisionTerminalReserve parameter otsTable ftsTable result hfinite h.1 h.2.1 h.2.2 hcap
  · simp only [Nat.cast_zero, mul_zero, zero_mul, zero_le]

noncomputable def initializedPendingParentCount
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : ENNReal :=
  ∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable)
    adversary parameter otsTable ftsTable q fuel] * (terminalPendingParentCount parameter otsTable ftsTable result : ENNReal)

theorem twice_initializedPendingParentCount_scaled_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    2 * initializedPendingParentCount adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤
      initializedCollisionTerminalReserve adversary parameter otsTable ftsTable q fuel := by
  rw [initializedPendingParentCount, initializedCollisionTerminalReserve, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [mul_left_comm 2, mul_assoc]
  by_cases hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel)
  · apply mul_le_mul' le_rfl
    apply twice_terminalPendingParentCount_scaled_le parameter otsTable ftsTable result
      (runRetainedWithFailure_cache_finite _ adversary parameter otsTable ftsTable q fuel result hr)
    apply (runRetainedWithFailure_cache_le_queryBound _ adversary q hq parameter hp otsTable ftsTable hfts fuel result hr).trans
    apply Nat.cast_le.mpr
    rw [show Fintype.card Digest = 2 ^ 128 from card_bitVec digestBits]
    omega
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

noncomputable def sampledPendingParentCount (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedPendingParentCount adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

theorem twice_sampledPendingParentCount_scaled_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    2 * sampledPendingParentCount adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤ sampledCollisionTerminalReserve adversary q fuel := by
  unfold sampledPendingParentCount sampledCollisionTerminalReserve
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro parameter
  rw [mul_left_comm 2, mul_assoc]
  by_cases hp : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    rw [mul_left_comm 2, mul_assoc]
    apply mul_le_mul' le_rfl
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro table
    rw [mul_left_comm 2, mul_assoc]
    exact mul_le_mul' le_rfl (twice_initializedPendingParentCount_scaled_le adversary q hq hqMax parameter hp table
      (curryFtsTableEquiv ftsSecret) (mem_support_sampleFtsSecrets ftsSecret) fuel)
  · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
