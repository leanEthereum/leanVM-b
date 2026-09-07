import SphincsSecurity.Proof.JointParentReleaseBound
import SphincsSecurity.Proof.SampledParentReserveConservation

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def initializedLocalizedParentLoss
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : ENNReal :=
  (∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] *
    terminalParentDiscard parameter otsTable ftsTable result) +
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    (expectedSharedFailureDiscard (parentException parameter otsTable ftsTable)
        (survivingFtsParentReserve (secretKey parameter default otsTable ftsTable)) parameter initial.2.1 otsTable ftsTable
        (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone +
      expectedBeforeFailureCharge (parentException parameter otsTable ftsTable)
        (localizedFtsParentReleaseCharge (secretKey parameter default otsTable ftsTable)) parameter initial.2.1 otsTable ftsTable
        (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone)

theorem initializedParentReserveLoss_le_localized
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    initializedParentReserveLoss adversary parameter otsTable ftsTable q fuel ≤
      initializedLocalizedParentLoss adversary parameter otsTable ftsTable q fuel := by
  rw [initializedParentReserveLoss, initializedLocalizedParentLoss]
  apply add_le_add le_rfl
  apply ENNReal.tsum_le_tsum
  intro initial
  by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
  · have hr := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
    have hf := finite_cache_of_mem_support _ ∅ initial.2.1 initial.2.2 hr finite_empty
    apply mul_le_mul' le_rfl
    rw [add_assoc]
    apply add_le_add le_rfl
    exact expectedBeforeFailureFtsParentRelease_add_discard_le_localized (parentException parameter otsTable ftsTable)
      (secretKey parameter default otsTable ftsTable) (fun _ _ _ h => h.2) parameter initial.2.1 otsTable ftsTable
      (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 hf false initial.1.isNone
  · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]

noncomputable def sampledLocalizedParentLoss (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedLocalizedParentLoss adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

theorem sampledParentReserveLoss_le_localized (adversary : Adversary) (q fuel : Nat) :
    sampledParentReserveLoss adversary q fuel ≤ sampledLocalizedParentLoss adversary q fuel := by
  unfold sampledParentReserveLoss sampledLocalizedParentLoss
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro table
  exact mul_le_mul' le_rfl (initializedParentReserveLoss_le_localized adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
