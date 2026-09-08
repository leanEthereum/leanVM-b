import SphincsSecurity.Proof.FreshCacheCharge
import SphincsSecurity.Proof.SigningEncodingReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def freshEncodingHashCharge (parameter : PublicParameter) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if ∃ position : EncodingPosition, AtEncodingPosition parameter input position then freshCacheCharge cache input else 0

theorem freshEncodingHashCharge_atEncoding (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : HashInput) (position : EncodingPosition) (hat : AtEncodingPosition parameter input position) :
    freshEncodingHashCharge parameter cache input = freshCacheCharge cache input := by
  rw [freshEncodingHashCharge, if_pos (show ∃ position, AtEncodingPosition parameter input position from ⟨position, hat⟩)]

theorem expected_freshEncoding_eq_zero_of_avoidsEncoding (parameter : PublicParameter)
    (computation : OracleComp HashSpec α) (havoid : ∀ f, AvoidsEncodingQueries parameter f computation)
    (cache : QueryCache HashSpec) :
    expectedQueryCharge (freshEncodingHashCharge parameter) (liftM computation) cache = 0 := by
  apply expectedQueryCharge_lift_eq_zero_of_supported_cuts
  intro ordinal middleCache input next hcut
  have hprefix := replay_of_mem_support _ _ _ _ hcut (fromCache middleCache) (agreesWithFn_fromCache middleCache)
  have hget := queriedInputs_getElem_of_eval_hashQueryCutAt (fromCache middleCache) computation ordinal input next hprefix.2.1
  have hnot : ¬ ∃ position : EncodingPosition, AtEncodingPosition parameter input position := by
    rintro ⟨position, payload, heq⟩
    apply havoid (fromCache middleCache) position payload
    rw [← heq]
    exact List.mem_of_getElem? hget
  rw [freshEncodingHashCharge, if_neg hnot]

theorem expectedPreException_freshEncoding_eq_zero_of_avoidsEncoding
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (parameter : PublicParameter)
    (computation : OracleComp HashSpec α) (havoid : ∀ f, AvoidsEncodingQueries parameter f computation)
    (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (freshEncodingHashCharge parameter) (liftM computation) cache hit = 0 :=
  expectedPreExceptionCharge_eq_zero_of_queryCharge_eq_zero _ _ _ _ _
    (expected_freshEncoding_eq_zero_of_avoidsEncoding parameter computation havoid cache)

theorem freshEncodingHashCharge_message_eq_zero (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : HashInput) (hmessage : MessageHashInput parameter input) :
    freshEncodingHashCharge parameter cache input = 0 := by
  rw [freshEncodingHashCharge, if_neg]
  rintro ⟨position, hat⟩
  exact hmessage.not_atEncoding position hat

private theorem expectedQueryCharge_messageDigest (charge : QueryCache HashSpec → HashInput → ENNReal)
    (key : SecretKey) (message : Message) (randomness : Randomness) (cache : QueryCache HashSpec) :
    expectedQueryCharge charge
      (liftM (messageDigest key.parameter key.root message randomness : OracleComp HashSpec MessageDigest)) cache =
        charge cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) := by
  change expectedQueryCharge charge
    ((liftM (OracleWorld.query (.inr (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness)))) : OracleComp OracleWorld HashOutput) >>=
      fun answer => pure (truncateMessageDigest answer)) cache = _
  rw [expectedQueryCharge_query_bind]
  simp only [expectedQueryCharge_pure, mul_zero, tsum_zero, add_zero, hashQueryCharge, Sum.elim_inr]

private theorem expected_freshEncoding_messageDigest_eq_zero
    (key : SecretKey) (message : Message) (randomness : Randomness) (cache : QueryCache HashSpec) :
    expectedQueryCharge (freshEncodingHashCharge key.parameter)
      (liftM (messageDigest key.parameter key.root message randomness : OracleComp HashSpec MessageDigest)) cache = 0 := by
  exact (expectedQueryCharge_messageDigest _ _ _ _ _).trans
    (freshEncodingHashCharge_message_eq_zero key.parameter cache _ ⟨_, rfl⟩)

private theorem expected_freshEncoding_signAttempt_eq_zero
    (key : SecretKey) (message : Message) (randomness : Randomness) (cache : QueryCache HashSpec) :
    expectedQueryCharge (freshEncodingHashCharge key.parameter)
      (liftM (signAttempt key message randomness : OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf))))) cache = 0 := by
  rw [signAttempt, liftM_bind, expectedQueryCharge_bind, expected_freshEncoding_messageDigest_eq_zero, zero_add]
  apply ENNReal.tsum_eq_zero.mpr
  intro result
  split_ifs <;> simp

theorem expected_freshEncoding_signDigestLoop_eq_zero
    (key : SecretKey) (message : Message) (attempts : Nat) (cache : QueryCache HashSpec) :
    expectedQueryCharge (freshEncodingHashCharge key.parameter) (signDigestLoop attempts key message) cache = 0 := by
  induction attempts generalizing cache with
  | zero => simp [signDigestLoop]
  | succ attempts ih =>
      rw [signDigestLoop, expectedQueryCharge_bind, expectedQueryCharge_lift_unif_eq_zero, zero_add]
      apply ENNReal.tsum_eq_zero.mpr
      intro sampled
      rw [expectedQueryCharge_bind, expected_freshEncoding_signAttempt_eq_zero, zero_add]
      apply mul_eq_zero_of_right
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      cases result.1 <;> simp [ih]

end SphincsSecurity.Concrete.FtsProbeSimulation
