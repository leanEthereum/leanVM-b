import XmssSecurity.Proof.SignCacheHitProbability
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option maxRecDepth 100000

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

noncomputable def Concrete.signBoundedAttemptsContinuation
    (attempts : Nat) (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (result : Option Signature × QueryCache HashSpec) :
    ProbComp (Option Signature × QueryCache HashSpec) :=
  match result.1 with
  | some signature => pure (some signature, result.2)
  | none => (simulateQ romImpl
      (Concrete.signBoundedAttempts attempts secretKey epoch message)).run result.2

attribute [irreducible] Concrete.signBoundedAttemptsContinuation

theorem Concrete.signBoundedAttempts_run_succ_eq
    (attempts : Nat) (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl
      (Concrete.signBoundedAttempts (attempts + 1) secretKey epoch message)).run cache =
      (($ᵗ Randomness) >>= fun randomness =>
        (simulateQ randomOracle
          (Concrete.signAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))).run cache >>=
          Concrete.signBoundedAttemptsContinuation attempts secretKey epoch
            message) := by
  rw [Concrete.signBoundedAttempts, simulateQ_bind, StateT.run_bind]
  have hsampleRun :
      (simulateQ romImpl
        (liftM Concrete.signingRandomness)).run cache =
        (fun randomness => (randomness, cache)) <$> Concrete.signingRandomness := by
    change (simulateQ (unifFwdImpl HashSpec +
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp)))
      (liftM Concrete.signingRandomness)).run cache = _
    exact roSim.run_liftM
      (hashSpec := HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      Concrete.signingRandomness cache
  rw [hsampleRun, Concrete.signingRandomness_eq]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr
  intro randomness
  rw [simulateQ_bind, StateT.run_bind]
  have hroute :
      simulateQ romImpl
          (liftM (Concrete.signAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))) =
        simulateQ randomOracle
          (Concrete.signAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature)) := by
    change simulateQ (unifFwdImpl HashSpec + randomOracle)
        (liftM (Concrete.signAttempt secretKey epoch message randomness :
          OracleComp HashSpec (Option Signature))) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.signAttempt secretKey epoch message randomness :
        OracleComp HashSpec (Option Signature))
  rw [hroute]
  apply bind_congr
  intro result
  rcases result with ⟨result, resultCache⟩
  cases result <;> simp [Concrete.signBoundedAttemptsContinuation]

theorem Concrete.signBoundedAttempts_run_succ_eq_sign_bind
    (attempts : Nat) (_publicKey : PublicKey) (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) (cache : QueryCache HashSpec) :
    (simulateQ romImpl
      (Concrete.signBoundedAttempts (attempts + 1) secretKey epoch message)).run cache =
      (simulateQ romImpl
        (Concrete.sign secretKey epoch message)).run cache >>=
          Concrete.signBoundedAttemptsContinuation attempts secretKey epoch
            message := by
  rw [Concrete.signBoundedAttempts_run_succ_eq, Concrete.sign_run_eq,
    bind_assoc]

end XmssSecurity
