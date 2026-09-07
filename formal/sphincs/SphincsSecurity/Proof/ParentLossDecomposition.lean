import SphincsSecurity.Proof.SecuritySharedParentRefund
import SphincsSecurity.Proof.ParentTerminalRefund
import SphincsSecurity.Proof.InitializedParentReleaseBound

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def initializedLocalizedParentReleaseCharge
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : ENNReal :=
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    expectedBeforeFailureCharge (parentException parameter otsTable ftsTable)
      (localizedFtsParentReleaseCharge (secretKey parameter default otsTable ftsTable)) parameter initial.2.1 otsTable ftsTable
      (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone

theorem initializedLocalizedParentLoss_eq_discard_add_shared_add_release
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    initializedLocalizedParentLoss adversary parameter otsTable ftsTable q fuel =
      initializedTerminalParentDiscard adversary parameter otsTable ftsTable q fuel +
        initializedSharedParentDiscard adversary parameter otsTable ftsTable q fuel +
        initializedLocalizedParentReleaseCharge adversary parameter otsTable ftsTable q fuel := by
  unfold initializedLocalizedParentLoss initializedTerminalParentDiscard initializedSharedParentDiscard initializedLocalizedParentReleaseCharge
  simp only [mul_add, ENNReal.tsum_add, add_assoc]

noncomputable def sampledLocalizedParentReleaseCharge (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedLocalizedParentReleaseCharge adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

theorem sampledLocalizedParentLoss_eq_discard_add_shared_add_release (adversary : Adversary) (q fuel : Nat) :
    sampledLocalizedParentLoss adversary q fuel = sampledTerminalParentDiscard adversary q fuel +
      sampledSharedParentDiscard adversary q fuel + sampledLocalizedParentReleaseCharge adversary q fuel := by
  unfold sampledLocalizedParentLoss sampledTerminalParentDiscard sampledSharedParentDiscard sampledLocalizedParentReleaseCharge
  simp only [initializedLocalizedParentLoss_eq_discard_add_shared_add_release, mul_add, ENNReal.tsum_add]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
