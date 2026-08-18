import XmssSecurity.FirstLaneMonitor

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

inductive Query (Index : Type) where
  | uniform (n : Nat)
  | encodingQuery (epoch : Epoch)
  | encodingSignAttempt (epoch : Epoch)
  | probe (index : Index) (target : Digest)
  | reveal (index : Index)
deriving DecidableEq

@[reducible]
def World (Index : Type) : OracleSpec (Query Index) :=
  OracleSpec.ofFn fun
  | .uniform n => Fin (n + 1)
  | .encodingQuery _ => HashOutput
  | .encodingSignAttempt _ => HashOutput
  | .probe _ _ => Unit
  | .reveal _ => Digest

def uniformQuery (n : Nat) : OracleComp (World Index) (Fin (n + 1)) :=
  liftM ((World Index).query (.uniform n))

def encodingQuery (epoch : Epoch) :
    OracleComp (World Index) HashOutput :=
  liftM ((World Index).query (.encodingQuery epoch))

def encodingSignAttemptQuery (epoch : Epoch) :
    OracleComp (World Index) HashOutput :=
  liftM ((World Index).query (.encodingSignAttempt epoch))

def probeQuery (index : Index) (target : Digest) :
    OracleComp (World Index) Unit :=
  liftM ((World Index).query (.probe index target))

def revealQuery (index : Index) : OracleComp (World Index) Digest :=
  liftM ((World Index).query (.reveal index))

def uniformForwardImpl : QueryImpl unifSpec (OracleComp (World Index)) :=
  fun n => uniformQuery n

def liftProbComp (computation : ProbComp α) : OracleComp (World Index) α :=
  simulateQ uniformForwardImpl computation

def IsSpecialQuery : (World Index).Domain → Prop
  | .uniform _ => False
  | _ => True

def IsHazardQuery : (World Index).Domain → Prop
  | .encodingQuery _ => True
  | .probe _ _ => True
  | _ => False

noncomputable instance (input : Query Index) :
    Fintype ((World Index).Range input) := by
  cases input <;> infer_instance

noncomputable instance (input : Query Index) :
    Inhabited ((World Index).Range input) := by
  cases input <;> infer_instance

noncomputable instance : DecidablePred (IsSpecialQuery (Index := Index)) :=
  Classical.decPred _

noncomputable instance : DecidablePred (IsHazardQuery (Index := Index)) :=
  Classical.decPred _

noncomputable instance : IsUniformSpec (World Index) :=
  IsUniformSpec.ofFintypeInhabited _

noncomputable def controller
    (computation : OracleComp (World Index) α) :
    ProbComp
      (FirstLaneMonitor.ControllerAction
        (OracleComp (World Index) α) Index) :=
  OracleComp.construct
    (C := fun _ => ProbComp
      (FirstLaneMonitor.ControllerAction
        (OracleComp (World Index) α) Index))
    (fun _ => pure .stop)
    (fun input next recursivelyContinue =>
      match input with
      | .uniform n => do
          let output ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
          recursivelyContinue output
      | .encodingQuery epoch => pure (.encodingQuery epoch next)
      | .encodingSignAttempt epoch => pure (.encodingSignAttempt epoch next)
      | .probe index target => pure (.probe index target (fun _ => next ()))
      | .reveal index => pure (.reveal index next))
    computation

noncomputable def monitorExperiment
    (steps fuel : Nat) (computation : OracleComp (World Index) α) :
    ProbComp Bool :=
  FirstLaneMonitor.run controller EncodingMonitor.State.empty
    AdaptiveRevealMonitor.State.empty steps fuel computation

theorem monitorExperiment_true_probability_le
    (steps fuel : Nat) (computation : OracleComp (World Index) α) :
    Pr[(· = true) | monitorExperiment steps fuel computation] ≤
      (fuel : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  exact FirstLaneMonitor.run_empty_true_probability_le controller steps fuel
    computation

end XmssSecurity.FirstLaneOracleSimulation
