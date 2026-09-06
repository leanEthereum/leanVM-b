import SphincsSecurity.Proof.JointProbeMaterializedBlocks
import SphincsSecurity.Proof.JointProbeTerminalBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FtsProbeSimulation.jointSourceRetained maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem sampledNativeFtsMaterializedProbeRisk_eq_jointCharge
    (adversary : Adversary) (q fuel : Nat) :
    sampledNativeFtsMaterializedProbeRisk adversary q fuel =
      ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ∑' otsTable, Pr[= otsTable | sampleOtsHashTable] *
            FtsProbeSimulation.expectedJointMaterializedCharge (FtsProbeSimulation.curryFtsTableEquiv ftsSecret)
              ((FtsProbeSimulation.jointSourceRetained adversary parameter q).run
                (emptySplitHashCache, FtsProbeSimulation.emptySplitHashCache))
              AdaptiveRevealProbe.State.empty q (ensuredInitialContext Finset.univ) fuel otsTable := by
  unfold sampledNativeFtsMaterializedProbeRisk initializedSourceMaterializedRisk FtsProbeSimulation.nativeFtsRetainedSource
  apply tsum_congr
  intro parameter
  apply congrArg (fun weight : ENNReal => Pr[= parameter | sampleParameter] * weight)
  apply tsum_congr
  intro ftsSecret
  apply congrArg (fun weight : ENNReal => Pr[= ftsSecret | sampleFtsSecrets] * weight)
  apply tsum_congr
  intro otsTable
  apply congrArg (fun weight : ENNReal => Pr[= otsTable | sampleOtsHashTable] * weight)
  exact (FtsProbeSimulation.expectedJointMaterializedCharge_eq_finalized _ _ _ _ _ _ _
    (ensuredInitialContext_valid Finset.univ).valuesConsistent
    (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable Finset.univ otsTable))).symm

end SphincsSecurity.Concrete
