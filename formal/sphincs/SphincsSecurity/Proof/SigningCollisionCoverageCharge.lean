import SphincsSecurity.Proof.SigningCollisionCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem collisionSigningStructuralCharge_message_eq_zero (key : SecretKey) (cache : QueryCache HashSpec)
    (input : HashInput) (hmessage : FtsProbeSimulation.MessageHashInput key.parameter input) :
    collisionSigningStructuralCharge key cache input = 0 := by
  simp [collisionSigningStructuralCharge, collisionParentStoppedEncodingQueryCharge,
    collisionParentStoppedEncodingBaseCharge, encodingPairIncrementCharge, ftsParentQueryCharge,
    parentReserveCharge, hmessage.not_atPosition, hmessage.not_atEncoding]

private theorem expectedQueryCharge_collision_messageDigest_eq_zero
    (key : SecretKey) (message : Message) (randomness : Randomness) (cache : QueryCache HashSpec) :
    expectedQueryCharge (collisionSigningStructuralCharge key)
      (liftM (messageDigest key.parameter key.root message randomness : OracleComp HashSpec MessageDigest) :
        OracleComp OracleWorld _) cache = 0 := by
  change expectedQueryCharge (collisionSigningStructuralCharge key)
    ((liftM (OracleWorld.query (.inr (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness)))) : OracleComp OracleWorld HashOutput) >>=
      fun answer => pure (truncateMessageDigest answer)) cache = 0
  rw [expectedQueryCharge_query_bind]
  simp only [expectedQueryCharge_pure, mul_zero, tsum_zero, add_zero, hashQueryCharge, Sum.elim_inr,
    collisionSigningStructuralCharge_message_eq_zero key cache _ ⟨_, rfl⟩]

private theorem expectedQueryCharge_collision_signAttempt_eq_zero
    (key : SecretKey) (message : Message) (randomness : Randomness) (cache : QueryCache HashSpec) :
    expectedQueryCharge (collisionSigningStructuralCharge key)
      (liftM (signAttempt key message randomness : OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))) :
        OracleComp OracleWorld _) cache = 0 := by
  rw [signAttempt, liftM_bind, expectedQueryCharge_bind, expectedQueryCharge_collision_messageDigest_eq_zero, zero_add]
  apply ENNReal.tsum_eq_zero.mpr
  intro result
  split_ifs <;> simp

theorem expectedQueryCharge_collision_signDigestLoop_eq_zero
    (key : SecretKey) (message : Message) (attempts : Nat) (cache : QueryCache HashSpec) :
    expectedQueryCharge (collisionSigningStructuralCharge key) (signDigestLoop attempts key message) cache = 0 := by
  induction attempts generalizing cache with
  | zero => simp [signDigestLoop]
  | succ attempts ih =>
      rw [signDigestLoop, expectedQueryCharge_bind, expectedQueryCharge_lift_unif_eq_zero, zero_add]
      apply ENNReal.tsum_eq_zero.mpr
      intro sampled
      rw [expectedQueryCharge_bind, expectedQueryCharge_collision_signAttempt_eq_zero, zero_add]
      apply mul_eq_zero_of_right
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      cases result.1 <;> simp [ih]

theorem expectedPreExceptionCharge_collision_signDigestLoop_eq_zero
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (attempts : Nat) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (collisionSigningStructuralCharge key) (signDigestLoop attempts key message) cache hit = 0 :=
  le_antisymm ((expectedPreExceptionCharge_le_queryCharge exception _ _ cache hit).trans_eq
    (expectedQueryCharge_collision_signDigestLoop_eq_zero key message attempts cache)) zero_le

noncomputable def digestSelectionRawCollisionCharge (key : SecretKey)
    (result : Option (Randomness × Index × (DigestTree → FtsLeaf)) × QueryCache HashSpec) : ENNReal :=
  match result.1 with
  | none => 0
  | some (randomness, index, leaves) =>
      expectedPreExceptionCharge (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret) (collisionSigningStructuralCharge key)
        (liftM (signAfterDigest key randomness index leaves)) result.2 false * (Fintype.card Digest : ENNReal)⁻¹

theorem expected_digestSelectionRawCollisionCharge_eq_preCharge (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] *
      digestSelectionRawCollisionCharge key result) =
      expectedPreExceptionCharge (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret) (collisionSigningStructuralCharge key)
        (sign key message) cache false * (Fintype.card Digest : ENNReal)⁻¹ := by
  let exception := CleanParentSettlement key.parameter key.otsSecret key.ftsSecret
  have hmonitor : runExceptionMonitor exception (signDigestLoop digestAttemptLimit key message) cache false =
      (fun result => (result, false)) <$> (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache := by
    have hflag := runFirstException_flag_projection exception (signDigestLoop digestAttemptLimit key message) cache none
    simp only [Option.isSome_none] at hflag
    rw [← hflag,
      preservesExceptionRecord_signDigestLoop key exception (fun _ _ _ h => h.2) message digestAttemptLimit cache none, Functor.map_map]
    rfl
  rw [sign_eq_digestLoop_afterDigest, expectedPreExceptionCharge_bind,
    expectedPreExceptionCharge_collision_signDigestLoop_eq_zero, zero_add, hmonitor, tsum_probOutput_map_mul,
    ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro result
  cases hs : result.1 <;> simp only [digestSelectionRawCollisionCharge, hs, expectedPreExceptionCharge_pure, zero_mul, mul_zero, mul_assoc]

theorem digestSelectionCollisionCharge_add_overlap (key : SecretKey) (cap budget : Nat)
    (message : Message) (log : QueryLog SigningSpec) (result) :
    digestSelectionCollisionCharge key cap budget message log result +
      boundedRemainingCoveragePotential key cap budget (digestSelectionCoverageState message log result) * digestSelectionRawCollisionCharge key result =
      digestSelectionRawCollisionCharge key result := by
  cases hs : result.1 with
  | none => simp [digestSelectionCollisionCharge, digestSelectionRawCollisionCharge, hs]
  | some data =>
      simp only [digestSelectionCollisionCharge, digestSelectionRawCollisionCharge, hs]
      rw [← add_mul, tsub_add_cancel_of_le (boundedRemainingCoveragePotential_le_one _ _ _ _), one_mul]

noncomputable def digestSelectionCollisionOverlap (key : SecretKey) (cap budget : Nat)
    (message : Message) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) : ENNReal :=
  ∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] *
    (boundedRemainingCoveragePotential key cap budget (digestSelectionCoverageState message log result) * digestSelectionRawCollisionCharge key result)

theorem digestSelectionCollisionRisk_add_overlap (key : SecretKey) (cap budget : Nat)
    (message : Message) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) :
    digestSelectionCollisionRisk key cap budget message cache log + digestSelectionCollisionOverlap key cap budget message cache log =
      expectedPreExceptionCharge (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret) (collisionSigningStructuralCharge key)
        (sign key message) cache false * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [digestSelectionCollisionRisk, digestSelectionCollisionOverlap, ← ENNReal.tsum_add,
    ← expected_digestSelectionRawCollisionCharge_eq_preCharge]
  apply tsum_congr
  intro result
  rw [← mul_add, digestSelectionCollisionCharge_add_overlap]

end SphincsSecurity.Concrete
