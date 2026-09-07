import SphincsSecurity.Proof.SigningStoppedStructuralBudget

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

variable (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)

theorem expectedPreExceptionCharge_encode_le_encodingCharge
    (secretKey : SecretKey) (charge : QueryCache HashSpec → HashInput → ENNReal)
    (hencoding : ∀ cache input position, AtEncodingPosition secretKey.parameter input position → 1 ≤ charge cache input) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) (cache : QueryCache HashSpec) (hit : Bool)
    (hsettled : EncodingMessageSettledAt cache secretKey ⟨lay, tree, leafIdx⟩) :
    expectedPreExceptionCharge exception (signingStructuralCharge secretKey)
        (liftM (encode secretKey.parameter lay tree leafIdx message counter : OracleComp HashSpec (Option Encoding)) : OracleComp OracleWorld _) cache hit ≤
      expectedPreExceptionCharge exception charge
        (liftM (encode secretKey.parameter lay tree leafIdx message counter : OracleComp HashSpec (Option Encoding)) : OracleComp OracleWorld _) cache hit := by
  cases hit with
  | true => simp
  | false =>
      have hcharge := signingStructuralCharge_le_one_of_encoding_settled secretKey cache
        (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) (digestBytes message ++ counterBytes counter))
        ⟨lay, tree, leafIdx⟩ ⟨_, rfl⟩ hsettled
      have hcharge := hcharge.trans (hencoding cache
        (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) (digestBytes message ++ counterBytes counter))
        ⟨lay, tree, leafIdx⟩ ⟨_, rfl⟩)
      change expectedPreExceptionCharge exception (signingStructuralCharge secretKey)
          ((liftM (OracleWorld.query (.inr (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)
            (digestBytes message ++ counterBytes counter)))) : OracleComp OracleWorld HashOutput) >>=
            fun answer => pure (TargetSum.decodeDigest (truncateHash answer))) cache false ≤
        expectedPreExceptionCharge exception charge
          ((liftM (OracleWorld.query (.inr (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)
            (digestBytes message ++ counterBytes counter)))) : OracleComp OracleWorld HashOutput) >>=
            fun answer => pure (TargetSum.decodeDigest (truncateHash answer))) cache false
      rw [expectedPreExceptionCharge_query_bind, expectedPreExceptionCharge_query_bind]
      simpa only [expectedPreExceptionCharge_pure, mul_zero, tsum_zero, add_zero,
        Bool.false_eq_true, if_false, hashQueryCharge, Sum.elim_inr] using hcharge

theorem expectedPreExceptionCharge_otsSignFrom_le_encodingCharge
    (secretKey : SecretKey) (charge : QueryCache HashSpec → HashInput → ENNReal)
    (hencoding : ∀ cache input position, AtEncodingPosition secretKey.parameter input position → 1 ≤ charge cache input) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (attempts counter : Nat) (cache : QueryCache HashSpec) (hit : Bool)
    (hsettled : EncodingMessageSettledAt cache secretKey ⟨lay, tree, leafIdx⟩) :
    expectedPreExceptionCharge exception (signingStructuralCharge secretKey)
        (liftM (otsSignFrom secretKey.parameter lay tree leafIdx (secretKey.otsSecret lay tree leafIdx) message attempts counter :
          OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) : OracleComp OracleWorld _) cache hit ≤
      expectedPreExceptionCharge exception charge
        (liftM (otsSignFrom secretKey.parameter lay tree leafIdx (secretKey.otsSecret lay tree leafIdx) message attempts counter :
          OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) : OracleComp OracleWorld _) cache hit := by
  induction attempts generalizing counter cache hit with
  | zero => simp [otsSignFrom]
  | succ attempts ih =>
      rw [otsSignFrom, liftM_bind]
      apply expectedPreExceptionCharge_bind_le_bind _ _ _ _ _ _ _
        (expectedPreExceptionCharge_encode_le_encodingCharge exception secretKey charge hencoding lay tree leafIdx message _ cache hit hsettled)
      intro result hr
      have hnextSettled := hsettled.mono (runExceptionMonitor_cache_le exception _ cache hit hr)
      cases result.1.1 with
      | none => exact ih (counter + 1) result.1.2 result.2 hnextSettled
      | some encoding =>
          rw [liftM_bind]
          apply expectedPreExceptionCharge_bind_le_bind
          · apply expectedPreExceptionCharge_lift_sequenceFin_le
            intro chainIdx currentCache currentHit
            rw [expectedPreExceptionCharge_eq_zero_of_queryCharge_eq_zero exception _ _ _ _
              (expectedQueryCharge_chainWalk_eq_zero secretKey lay tree leafIdx chainIdx _ currentCache)]
            exact bot_le
          · intros; simp

theorem expectedPreExceptionCharge_signLayer_le_encodingCharge
    (secretKey : SecretKey) (charge : QueryCache HashSpec → HashInput → ENNReal)
    (hencoding : ∀ cache input position, AtEncodingPosition secretKey.parameter input position → 1 ≤ charge cache input) (index : Index) (lay : Layer) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (signingStructuralCharge secretKey)
        (liftM (signLayer secretKey index lay : OracleComp HashSpec _) : OracleComp OracleWorld _) cache hit ≤
      expectedPreExceptionCharge exception charge
        (liftM (signLayer secretKey index lay : OracleComp HashSpec _) : OracleComp OracleWorld _) cache hit := by
  rw [signLayer, liftM_bind]
  apply expectedPreExceptionCharge_bind_le_bind
  · rw [expectedPreExceptionCharge_eq_zero_of_queryCharge_eq_zero exception _ _ _ _
      (expectedQueryCharge_layerMessage_eq_zero secretKey index lay cache)]
    exact bot_le
  · intro result hr
    have hprojection := runExceptionMonitor_support_project exception _ cache hit hr
    have hrun := (replay_of_mem_support _ cache result.1.1 result.1.2
      (by simpa only [simulateQ_romImpl_liftM] using hprojection)
      (fromCache result.1.2) (agreesWithFn_fromCache result.1.2)).2.2
    have hsettled : EncodingMessageSettledAt result.1.2 secretKey ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ :=
      ⟨index, rfl, rfl, layerMessagePosition_settled_of_cachedRun (agreesWithFn_fromCache result.1.2) hrun⟩
    rw [liftM_bind]
    apply expectedPreExceptionCharge_bind_le_bind _ _ _ _ _ _ _
      (expectedPreExceptionCharge_otsSignFrom_le_encodingCharge exception secretKey charge hencoding lay _ _ result.1.1 _ _ result.1.2 result.2 hsettled)
    intro signed _
    cases signed.1.1 with
    | none => simp
    | some part =>
        rw [liftM_bind]
        apply expectedPreExceptionCharge_bind_le_bind
        · rw [expectedPreExceptionCharge_eq_zero_of_queryCharge_eq_zero exception _ _ _ _
            (expectedQueryCharge_treePath_eq_zero secretKey lay _ _ signed.1.2)]
          exact bot_le
        · intros; simp

theorem expectedPreExceptionCharge_sign_le_encodingCharge
    (secretKey : SecretKey) (charge : QueryCache HashSpec → HashInput → ENNReal)
    (hencoding : ∀ cache input position, AtEncodingPosition secretKey.parameter input position → 1 ≤ charge cache input) (message : Message) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (signingStructuralCharge secretKey) (sign secretKey message) cache hit ≤
      expectedPreExceptionCharge exception charge (sign secretKey message) cache hit := by
  rw [sign]
  apply expectedPreExceptionCharge_bind_le_bind
  · rw [expectedPreExceptionCharge_eq_zero_of_queryCharge_eq_zero exception _ _ _ _
      (expectedQueryCharge_signDigestLoop_eq_zero _ secretKey message cache)]
    exact bot_le
  · intro selected _
    cases selected.1.1 with
    | none => simp
    | some selectedDigest =>
        apply expectedPreExceptionCharge_bind_le_bind
        · rw [expectedPreExceptionCharge_eq_zero_of_queryCharge_eq_zero exception _ _ _ _
            (expectedQueryCharge_ftsOpen_eq_zero secretKey _ _ selected.1.2)]
          exact bot_le
        · intro opening _
          apply expectedPreExceptionCharge_bind_le_bind
          · apply expectedPreExceptionCharge_lift_sequenceFin_le
            intro lay currentCache currentHit
            exact expectedPreExceptionCharge_signLayer_le_encodingCharge exception secretKey charge hencoding selectedDigest.2.1 lay currentCache currentHit
          · intro layers _
            split <;> simp

end SphincsSecurity.Concrete
