import XmssSecurity.Proof.CausalKeygenCoupling

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable def programmedWarmedTrajectoryMaterial
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp ((List Digest × FlatSecret) ×
      (List FullChainTrajectory × QueryCache HashSpec)) := do
  let secretView ← extractFixedChainSeeds chain allEpochs
  let trajectoryResult ← programmedFixedSeedChainTrajectoriesFromCache parameter
    (unflattenSecret secretView.2) chain (chainLength - 1) ∅ allEpochs
  pure (secretView, trajectoryResult)

end XmssSecurity
