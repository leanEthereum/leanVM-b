import XmssSecurity.Proof.CappedGlobalTreeCoupling
import XmssSecurity.Proof.CappedChain.ChainTracedGame
import XmssSecurity.Proof.PrecomputedKeygenCache

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

noncomputable def trajectoryProgrammedGlobalChainKeygen :
    ProbComp ProgrammedGlobalChainKeygenView :=
  eraseAllChainTrajectories <$> programmedAllChainTrajectoryKeygen

theorem evalDist_coupledGlobalChainKeygen_eq_trajectoryProgrammed :
    evalDist coupledGlobalChainKeygen =
      evalDist trajectoryProgrammedGlobalChainKeygen :=
  evalDist_coupledGlobalChainKeygen_eq_programmedTrajectories

theorem evalDist_actualGlobalChainKeygen_eq_trajectoryProgrammed :
    evalDist actualGlobalChainKeygen =
      evalDist trajectoryProgrammedGlobalChainKeygen :=
  evalDist_actualGlobalChainKeygen_eq_programmedAllChainTrajectories

theorem trajectoryProgrammedGlobalChainKeygen_support_table
    (result : ProgrammedGlobalChainKeygenView)
    (hresult : result ∈ support trajectoryProgrammedGlobalChainKeygen) :
    globalKeygenChainValueTable result.cache result.secretKey = result.table := by
  apply actualGlobalChainKeygen_support_table result
  exact (mem_support_iff_of_evalDist_eq
    evalDist_actualGlobalChainKeygen_eq_trajectoryProgrammed result).mpr hresult

abbrev GlobalChainActionTracedResult :=
  ((ProgrammedGlobalChainKeygenView × (GameOutcome × QueryCache HashSpec)) ×
    AttackerActionTrace)

def eraseGlobalChainKeygenView
    (result : GlobalChainActionTracedResult) :
    ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) :=
  ((((result.1.1.publicKey, Concrete.materializePrecomputation
      result.1.1.cache result.1.1.secretKey), result.1.1.cache),
    result.1.2), result.2)

end XmssSecurity.CappedChain
