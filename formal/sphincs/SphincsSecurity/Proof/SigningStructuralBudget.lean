import SphincsSecurity.Proof.SigningHonestStructuralCharge
import SphincsSecurity.Proof.RomQueryChargeComparison

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem signingStructuralCharge_le_one_of_encoding_settled
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (position : EncodingPosition) (hat : AtEncodingPosition secretKey.parameter input position)
    (hsettled : EncodingMessageSettledAt cache secretKey position) :
    signingStructuralCharge secretKey cache input ≤ 1 := by
  classical
  have hparent : ftsParentQueryCharge secretKey cache input = 0 := by
    have h := ots_ftsLeaf_parent_queryCharge_eq_zero_of_atEncoding secretKey cache input hat
    exact (add_eq_zero.mp h).2
  rw [signingStructuralCharge, hparent, add_zero]
  have hexists : ∃ candidate, AtEncodingPosition secretKey.parameter input candidate := ⟨position, hat⟩
  have hselected : Classical.choose hexists = position :=
    atEncodingPosition_unique (Classical.choose_spec hexists) hat
  unfold parentStoppedEncodingQueryCharge
  split_ifs with hfresh
  · simp only [hselected, encodingMessageIncrement, if_pos hsettled]
    norm_num
  · norm_num

theorem expectedQueryCharge_encode_le_hashQueries
    (secretKey : SecretKey) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) (cache : QueryCache HashSpec)
    (hsettled : EncodingMessageSettledAt cache secretKey ⟨lay, tree, leafIdx⟩) :
    expectedQueryCharge (signingStructuralCharge secretKey)
        (liftM (encode secretKey.parameter lay tree leafIdx message counter : OracleComp HashSpec (Option Encoding)) : OracleComp OracleWorld _) cache ≤
      expectedQueryCharge (fun _ _ => 1)
        (liftM (encode secretKey.parameter lay tree leafIdx message counter : OracleComp HashSpec (Option Encoding)) : OracleComp OracleWorld _) cache := by
  have hcharge := signingStructuralCharge_le_one_of_encoding_settled secretKey cache
    (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) (digestBytes message ++ counterBytes counter))
    ⟨lay, tree, leafIdx⟩ ⟨_, rfl⟩ hsettled
  change expectedQueryCharge (signingStructuralCharge secretKey)
      ((liftM (OracleWorld.query (.inr (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)
        (digestBytes message ++ counterBytes counter)))) : OracleComp OracleWorld HashOutput) >>=
        fun answer => pure (TargetSum.decodeDigest (truncateHash answer))) cache ≤
    expectedQueryCharge (fun _ _ => 1)
      ((liftM (OracleWorld.query (.inr (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)
        (digestBytes message ++ counterBytes counter)))) : OracleComp OracleWorld HashOutput) >>=
        fun answer => pure (TargetSum.decodeDigest (truncateHash answer))) cache
  rw [expectedQueryCharge_query_bind, expectedQueryCharge_query_bind]
  simpa only [expectedQueryCharge_pure, mul_zero, tsum_zero,
    add_zero, hashQueryCharge, Sum.elim_inr] using hcharge

theorem expectedQueryCharge_otsSignFrom_le_hashQueries
    (secretKey : SecretKey) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (attempts counter : Nat) (cache : QueryCache HashSpec)
    (hsettled : EncodingMessageSettledAt cache secretKey ⟨lay, tree, leafIdx⟩) :
    expectedQueryCharge (signingStructuralCharge secretKey)
        (liftM (otsSignFrom secretKey.parameter lay tree leafIdx (secretKey.otsSecret lay tree leafIdx) message attempts counter :
          OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) : OracleComp OracleWorld _) cache ≤
      expectedQueryCharge (fun _ _ => 1)
        (liftM (otsSignFrom secretKey.parameter lay tree leafIdx (secretKey.otsSecret lay tree leafIdx) message attempts counter :
          OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) : OracleComp OracleWorld _) cache := by
  induction attempts generalizing counter cache with
  | zero => simp [otsSignFrom]
  | succ attempts ih =>
      rw [otsSignFrom, liftM_bind]
      apply expectedQueryCharge_bind_le_bind _ _ _ _ _
        (expectedQueryCharge_encode_le_hashQueries secretKey lay tree leafIdx message _ cache hsettled)
      intro result hr
      have hnextSettled := hsettled.mono (simulateQ_romImpl_cache_le _ cache result hr)
      cases he : result.1 with
      | none => exact ih (counter + 1) result.2 hnextSettled
      | some encoding =>
          rw [liftM_bind]
          apply expectedQueryCharge_bind_le_bind
          · apply expectedQueryCharge_lift_sequenceFin_le
            intro chainIdx currentCache
            rw [expectedQueryCharge_chainWalk_eq_zero]
            exact bot_le
          · intros; simp

theorem expectedQueryCharge_signLayer_le_hashQueries
    (secretKey : SecretKey) (index : Index) (lay : Layer) (cache : QueryCache HashSpec) :
    expectedQueryCharge (signingStructuralCharge secretKey)
        (liftM (signLayer secretKey index lay : OracleComp HashSpec _) : OracleComp OracleWorld _) cache ≤
      expectedQueryCharge (fun _ _ => 1)
        (liftM (signLayer secretKey index lay : OracleComp HashSpec _) : OracleComp OracleWorld _) cache := by
  rw [signLayer, liftM_bind]
  apply expectedQueryCharge_bind_le_bind
  · rw [expectedQueryCharge_layerMessage_eq_zero]
    exact bot_le
  · intro result hr
    have hrun := (replay_of_mem_support _ cache result.1 result.2
      (by simpa only [simulateQ_romImpl_liftM] using hr) (fromCache result.2) (agreesWithFn_fromCache result.2)).2.2
    have hsettled : EncodingMessageSettledAt result.2 secretKey ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ :=
      ⟨index, rfl, rfl, layerMessagePosition_settled_of_cachedRun (agreesWithFn_fromCache result.2) hrun⟩
    rw [liftM_bind]
    apply expectedQueryCharge_bind_le_bind _ _ _ _ _
      (expectedQueryCharge_otsSignFrom_le_hashQueries secretKey lay _ _ result.1 _ _ result.2 hsettled)
    intro signed _
    cases signed.1 with
    | none => simp
    | some part =>
        rw [liftM_bind]
        apply expectedQueryCharge_bind_le_bind
        · rw [expectedQueryCharge_treePath_eq_zero]
          exact bot_le
        · intros; simp

theorem signingStructuralCharge_message_eq_zero
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (payload : HashInput) :
    signingStructuralCharge secretKey cache (tweakableHashInput secretKey.parameter .message payload) = 0 := by
  classical
  have hnposition : ∀ position, ¬ AtPosition secretKey.parameter
      (tweakableHashInput secretKey.parameter .message payload) position := by
    rintro position ⟨otherPayload, hinput⟩
    have hdomain := (tweakableHashInput_injective secretKey.parameter (by trivial)
      (Position.domain_inRange position) hinput).1
    cases position <;> simp [Position.domain] at hdomain
  have hnencoding : ∀ position, ¬ AtEncodingPosition secretKey.parameter
      (tweakableHashInput secretKey.parameter .message payload) position := by
    rintro position ⟨otherPayload, hinput⟩
    have hdomain := (tweakableHashInput_injective secretKey.parameter (by trivial) (by trivial) hinput).1
    simp [EncodingPosition.domain] at hdomain
  simp [signingStructuralCharge, parentStoppedEncodingQueryCharge, ftsParentQueryCharge,
    parentReserveCharge, hnposition, hnencoding]

theorem expectedQueryCharge_messageDigest_eq_zero
    (secretKey : SecretKey) (message : Message) (randomness : Randomness) (cache : QueryCache HashSpec) :
    expectedQueryCharge (signingStructuralCharge secretKey)
      (liftM (messageDigest secretKey.parameter secretKey.root message randomness : OracleComp HashSpec MessageDigest) :
        OracleComp OracleWorld _) cache = 0 := by
  change expectedQueryCharge (signingStructuralCharge secretKey)
    ((liftM (OracleWorld.query (.inr (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)))) : OracleComp OracleWorld HashOutput) >>=
      fun answer => pure (truncateMessageDigest answer)) cache = 0
  rw [expectedQueryCharge_query_bind]
  simp only [expectedQueryCharge_pure, mul_zero, tsum_zero, add_zero, hashQueryCharge, Sum.elim_inr,
    signingStructuralCharge_message_eq_zero]

theorem expectedQueryCharge_signAttempt_eq_zero
    (secretKey : SecretKey) (message : Message) (randomness : Randomness) (cache : QueryCache HashSpec) :
    expectedQueryCharge (signingStructuralCharge secretKey)
      (liftM (signAttempt secretKey message randomness : OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))) :
        OracleComp OracleWorld _) cache = 0 := by
  rw [signAttempt, liftM_bind, expectedQueryCharge_bind, expectedQueryCharge_messageDigest_eq_zero, zero_add]
  apply ENNReal.tsum_eq_zero.mpr
  intro result
  split_ifs <;> simp

theorem expectedQueryCharge_signDigestLoop_eq_zero
    (attempts : Nat) (secretKey : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    expectedQueryCharge (signingStructuralCharge secretKey) (signDigestLoop attempts secretKey message) cache = 0 := by
  induction attempts generalizing cache with
  | zero => simp [signDigestLoop]
  | succ attempts ih =>
      rw [signDigestLoop, expectedQueryCharge_bind, expectedQueryCharge_lift_unif_eq_zero, zero_add]
      apply ENNReal.tsum_eq_zero.mpr
      intro sampled
      rw [expectedQueryCharge_bind, expectedQueryCharge_signAttempt_eq_zero, zero_add]
      apply mul_eq_zero_of_right
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      cases result.1 <;> simp [ih]

theorem expectedQueryCharge_sign_le_hashQueries
    (secretKey : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    expectedQueryCharge (signingStructuralCharge secretKey) (sign secretKey message) cache ≤
      expectedQueryCharge (fun _ _ => 1) (sign secretKey message) cache := by
  rw [sign]
  apply expectedQueryCharge_bind_le_bind
  · rw [expectedQueryCharge_signDigestLoop_eq_zero]
    exact bot_le
  · intro selected _
    cases selected.1 with
    | none => simp
    | some selectedDigest =>
        apply expectedQueryCharge_bind_le_bind
        · rw [expectedQueryCharge_ftsOpen_eq_zero]
          exact bot_le
        · intro opening _
          apply expectedQueryCharge_bind_le_bind
          · apply expectedQueryCharge_lift_sequenceFin_le
            intro lay currentCache
            exact expectedQueryCharge_signLayer_le_hashQueries secretKey selectedDigest.2.1 lay currentCache
          · intro layers _
            split <;> simp

theorem expectedPreExceptionCharge_sign_le_hashQueries
    (secretKey : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (hit : Bool) :
    expectedPreExceptionCharge exception (signingStructuralCharge secretKey) (sign secretKey message) cache hit ≤
      expectedQueryCharge (fun _ _ => 1) (sign secretKey message) cache :=
  (expectedPreExceptionCharge_le_queryCharge exception _ _ cache hit).trans
    (expectedQueryCharge_sign_le_hashQueries secretKey message cache)

end SphincsSecurity.Concrete
