import XmssSecurity.Statement.Parameters
import VCVio.OracleComp.Constructions.BitVec
import VCVio.OracleComp.ProbCompLift
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics

open OracleComp OracleSpec

namespace XmssSecurity

abbrev HashSpec := HashInput →ₒ HashOutput
abbrev OracleWorld := unifSpec + HashSpec

namespace Rom

noncomputable def runtime : ProbCompRuntime (OracleComp OracleWorld) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := (randomOracle : QueryImpl HashSpec (StateT HashSpec.QueryCache ProbComp))) ∅
  toProbCompLift := ProbCompLift.ofMonadLift _

end Rom

structure SignRequest where
  epoch : Epoch
  message : Message
deriving DecidableEq

structure Forgery where
  epoch : Epoch
  message : Message
  signature : Signature
deriving DecidableEq

def Forgery.request (forgery : Forgery) : SignRequest :=
  ⟨forgery.epoch, forgery.message⟩

end XmssSecurity
