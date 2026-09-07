import SphincsSecurity.Proof.InitializedParentReserveConservation

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledParentReserveLoss (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedParentReserveLoss adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

noncomputable def sampledFreshParentReserveCharge (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedFreshParentReserveCharge adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

theorem sampledPendingParentCount_add_loss_eq_funding
    (adversary : Adversary) (q fuel : Nat) :
    sampledPendingParentCount adversary q fuel + sampledParentReserveLoss adversary q fuel =
      sampledFreshParentReserveCharge adversary q fuel := by
  unfold sampledPendingParentCount sampledParentReserveLoss sampledFreshParentReserveCharge
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro parameter
  rw [← mul_add, ← ENNReal.tsum_add]
  apply congrArg
  apply tsum_congr
  intro ftsSecret
  rw [← mul_add, ← ENNReal.tsum_add]
  apply congrArg
  apply tsum_congr
  intro table
  rw [← mul_add, initializedPendingParentCount_add_loss_eq_funding]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
