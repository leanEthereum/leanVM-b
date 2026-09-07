import SphincsSecurity.Proof.JointParentReserveConservation
import SphincsSecurity.Proof.RetainedCollisionCacheReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition parentReserve
set_option backward.isDefEq.respectTransparency false

theorem survivingFtsParentReserve_treeRoot_eq_zero
    (key : SecretKey) (lay : Layer) (tree : TreeIndex) (result : Digest × QueryCache HashSpec)
    (hr : result ∈ support ((simulateQ romImpl
      (liftM (treeRoot key.parameter lay tree (key.otsSecret lay tree) : OracleComp HashSpec Digest) : OracleComp OracleWorld Digest)).run ∅)) :
    survivingFtsParentReserve key result.2 false = 0 := by
  have h := structuralRecordPotential_treeRoot_eq_zero key lay tree result hr
  rw [structuralRecordPotential] at h
  have hp := (add_eq_zero.mp h).2
  change (parentReserve key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) result.2 : ENNReal) *
    (Fintype.card Digest : ENNReal)⁻¹ = 0 at hp
  have hz := (mul_eq_zero.mp hp).resolve_right (ENNReal.inv_ne_zero.mpr (by finiteness))
  exact hz

noncomputable def terminalParentDiscard
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool) : ENNReal :=
  if SurvivingStructuralFailure parameter otsTable ftsTable result then
    jointSurvivingCachePotential (survivingFtsParentReserve (secretKey parameter default otsTable ftsTable))
      result.1.2.1.2 result.1.2.2 result.2
  else 0

theorem terminalPendingParentCount_add_discard
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool) :
    (terminalPendingParentCount parameter otsTable ftsTable result : ENNReal) + terminalParentDiscard parameter otsTable ftsTable result =
      jointSurvivingCachePotential (survivingFtsParentReserve (secretKey parameter default otsTable ftsTable))
        result.1.2.1.2 result.1.2.2 result.2 := by
  by_cases hs : SurvivingStructuralFailure parameter otsTable ftsTable result
  · simp only [terminalPendingParentCount, terminalParentDiscard, hs, not_true_eq_false, and_false, if_true, if_false, Nat.cast_zero, zero_add]
  · cases hh : result.1.2.2 <;> cases hf : result.2 <;>
      simp only [terminalPendingParentCount, terminalParentDiscard, hs, hh, hf, Bool.false_eq_true, Bool.true_eq_false,
        not_false_eq_true, and_true, and_false, if_true, if_false, Nat.cast_zero, jointSurvivingCachePotential,
        survivingFtsParentReserve, add_zero]
    rfl

noncomputable def initializedParentReserveLoss
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : ENNReal :=
  (∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] *
    terminalParentDiscard parameter otsTable ftsTable result) +
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    (expectedSharedFailureDiscard (parentException parameter otsTable ftsTable)
        (survivingFtsParentReserve (secretKey parameter default otsTable ftsTable)) parameter initial.2.1 otsTable ftsTable
        (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone +
      expectedBeforeFailureCharge (parentException parameter otsTable ftsTable)
        (releasedFtsParentQueryCharge (secretKey parameter default otsTable ftsTable)) parameter initial.2.1 otsTable ftsTable
        (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone +
      expectedBeforeFailureCharge (parentException parameter otsTable ftsTable)
        (discardedFtsParentQueryCharge (parentException parameter otsTable ftsTable) (secretKey parameter default otsTable ftsTable))
        parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone)

noncomputable def initializedFreshParentReserveCharge
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : ENNReal :=
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    expectedBeforeFailureCharge (parentException parameter otsTable ftsTable)
      (freshFtsParentReserveCharge (secretKey parameter default otsTable ftsTable)) parameter initial.2.1 otsTable ftsTable
      (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone

theorem initializedPendingParentCount_add_loss_eq_funding
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    initializedPendingParentCount adversary parameter otsTable ftsTable q fuel + initializedParentReserveLoss adversary parameter otsTable ftsTable q fuel =
      initializedFreshParentReserveCharge adversary parameter otsTable ftsTable q fuel := by
  rw [initializedPendingParentCount, initializedParentReserveLoss, ← add_assoc, ← ENNReal.tsum_add]
  simp_rw [← mul_add, terminalPendingParentCount_add_discard]
  rw [runRetainedWithFailure, tsum_probOutput_bind_mul, initializedFreshParentReserveCharge, ← ENNReal.tsum_add]
  apply tsum_congr
  intro initial
  rw [← mul_add]
  by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
  · apply congrArg (fun value : ENNReal => Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] * value)
    let key := secretKey parameter initial.2.1 otsTable ftsTable
    have hr := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
    have hf := finite_cache_of_mem_support _ ∅ initial.2.1 initial.2.2 hr finite_empty
    have hz := survivingFtsParentReserve_treeRoot_eq_zero key topLayer rootTree initial.2 hr
    have h := expected_jointParentReserve_add_losses_eq_funding (parentException parameter otsTable ftsTable) parameter initial.2.1 otsTable ftsTable
      (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 hf false initial.1.isNone
    have hzero : jointSurvivingCachePotential (survivingFtsParentReserve key) initial.2.2 false initial.1.isNone = 0 := by
      simp only [jointSurvivingCachePotential, hz, ite_self]
    rw [hzero, zero_add] at h
    rw [show survivingFtsParentReserve (secretKey parameter initial.2.1 otsTable ftsTable) =
      survivingFtsParentReserve (secretKey parameter default otsTable ftsTable) from rfl,
      show releasedFtsParentQueryCharge (secretKey parameter initial.2.1 otsTable ftsTable) =
        releasedFtsParentQueryCharge (secretKey parameter default otsTable ftsTable) from rfl,
      show discardedFtsParentQueryCharge (parentException parameter otsTable ftsTable) (secretKey parameter initial.2.1 otsTable ftsTable) =
        discardedFtsParentQueryCharge (parentException parameter otsTable ftsTable) (secretKey parameter default otsTable ftsTable) from rfl,
      show freshFtsParentReserveCharge (secretKey parameter initial.2.1 otsTable ftsTable) =
        freshFtsParentReserveCharge (secretKey parameter default otsTable ftsTable) from rfl] at h
    simpa only [add_assoc] using h
  · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
