import SphincsSecurity.Proof.RetryQueryBudget
import SphincsSecurity.Proof.SigningQueryCost

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local irreducible] ConsumesHashQueries

noncomputable def randomizedSignAttempt (key : SecretKey) (message : Message) :
    OracleComp OracleWorld (Option (Randomness × Index × (DigestTree → FtsLeaf))) := do
  let randomness ← liftM sampleRandomness
  let result ← liftM (signAttempt key message randomness : OracleComp HashSpec _)
  return result.map (fun selected => (randomness, selected))

theorem signDigestLoop_eq_retryOption (key : SecretKey) (message : Message) (attempts : Nat) :
    signDigestLoop attempts key message = retryOption (randomizedSignAttempt key message) attempts := by
  induction attempts with
  | zero => rfl
  | succ n ih =>
      simp only [signDigestLoop, retryOption, randomizedSignAttempt, bind_assoc, pure_bind]
      congr 1
      funext randomness
      congr 1
      funext result
      cases result with
      | none => exact ih
      | some value => rfl

theorem consumesHashQueries_randomizedSignAttempt (key : SecretKey) (message : Message) :
    ConsumesHashQueries (randomizedSignAttempt key message) 1 := by
  unfold randomizedSignAttempt
  apply consumesHashQueries_bind _ _ 0 1 (consumesHashQueries_zero _)
  intro randomness
  exact consumesHashQueries_bind _ _ 1 0 (consumesHashQueries_signAttempt _ _ _)
    (fun _ => consumesHashQueries_zero _)

theorem none_mem_support_signAttempt (key : SecretKey) (message : Message) (randomness : Randomness) :
    none ∈ support (signAttempt key message randomness : OracleComp HashSpec _) := by
  unfold signAttempt messageDigest
  rw [bind_assoc, mem_support_bind_iff]
  refine ⟨(93536104789177786765035829293842113257979682750464 : HashOutput), ?_, ?_⟩
  · exact mem_support_query _ _
  · have h : ¬ Admissible (truncateMessageDigest
        (93536104789177786765035829293842113257979682750464 : HashOutput)) := by decide
    simp only [pure_bind, if_neg h, mem_support_pure_iff]

theorem none_mem_support_randomizedSignAttempt (key : SecretKey) (message : Message) :
    none ∈ support (randomizedSignAttempt key message) := by
  unfold randomizedSignAttempt
  rw [mem_support_bind_iff]
  refine ⟨0, ?_, ?_⟩
  · change (0 : Randomness) ∈ support (OracleComp.liftComp sampleRandomness OracleWorld)
    rw [mem_support_liftComp_iff, sampleRandomness_eq]
    simp
  · rw [mem_support_bind_iff]
    refine ⟨none, ?_, by simp⟩
    change none ∈ support (OracleComp.liftComp
      (signAttempt key message 0 : OracleComp HashSpec _) OracleWorld)
    rw [mem_support_liftComp_iff]
    exact none_mem_support_signAttempt _ _ _

theorem consumesHashQueries_signDigestLoop (key : SecretKey) (message : Message) (attempts : Nat) :
    ConsumesHashQueries (signDigestLoop attempts key message) attempts := by
  rw [signDigestLoop_eq_retryOption]
  simpa only [Nat.mul_one] using consumesHashQueries_retryOption
    (randomizedSignAttempt key message) 1 (consumesHashQueries_randomizedSignAttempt _ _)
    (none_mem_support_randomizedSignAttempt _ _) attempts

theorem consumesHashQueries_sign_retryLimit (key : SecretKey) (message : Message) :
    ConsumesHashQueries (sign key message) digestAttemptLimit := by
  rw [sign_eq]
  exact consumesHashQueries_bind _ _ digestAttemptLimit 0
    (consumesHashQueries_signDigestLoop _ _ _) (fun _ => consumesHashQueries_zero _)

end SphincsSecurity.Concrete
