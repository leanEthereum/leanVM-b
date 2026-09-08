import SphincsSecurity.Proof.EncodingFreshSearchBudget
import SphincsSecurity.Proof.FreshEncodingCharge
import SphincsSecurity.Proof.LayerMessageSurvivalCost
import SphincsSecurity.Proof.PreExceptionSurvivalPayment

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local irreducible] freshEncodingHashCharge freshCacheCharge
set_option backward.isDefEq.respectTransparency false

theorem expectedQueryCharge_encode (charge : QueryCache HashSpec → HashInput → ENNReal)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) (cache : QueryCache HashSpec) :
    expectedQueryCharge charge (liftM (encode parameter lay tree leafIdx message counter : OracleComp HashSpec (Option Encoding))) cache =
      charge cache (tweakableHashInput parameter (.encoding lay tree leafIdx) (digestBytes message ++ counterBytes counter)) := by
  simp only [encode, liftM_bind, liftM_pure, expectedQueryCharge_bind, expectedQueryCharge_pure,
    mul_zero, tsum_zero, add_zero]
  change expectedQueryCharge charge
    ((liftM (OracleWorld.query (.inr (tweakableHashInput parameter (.encoding lay tree leafIdx)
      (digestBytes message ++ counterBytes counter)))) : OracleComp OracleWorld HashOutput) >>=
        fun answer => pure (truncateHash answer)) cache = _
  rw [expectedQueryCharge_query_bind]
  simp only [expectedQueryCharge_pure, mul_zero, tsum_zero, add_zero, hashQueryCharge, Sum.elim_inr]

theorem expected_freshEncoding_encode_eq_fresh (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) (counter : Counter) (cache : QueryCache HashSpec) :
    expectedQueryCharge (freshEncodingHashCharge parameter)
        (liftM (encode parameter lay tree leafIdx message counter : OracleComp HashSpec (Option Encoding))) cache =
      expectedQueryCharge freshCacheCharge
        (liftM (encode parameter lay tree leafIdx message counter : OracleComp HashSpec (Option Encoding))) cache := by
  calc
    _ = freshEncodingHashCharge parameter cache (tweakableHashInput parameter (.encoding lay tree leafIdx)
        (digestBytes message ++ counterBytes counter)) := expectedQueryCharge_encode _ _ _ _ _ _ _ _
    _ = freshCacheCharge cache (tweakableHashInput parameter (.encoding lay tree leafIdx)
        (digestBytes message ++ counterBytes counter)) := freshEncodingHashCharge_atEncoding _ _ _ ⟨lay, tree, leafIdx⟩ ⟨_, rfl⟩
    _ = _ := (expectedQueryCharge_encode _ _ _ _ _ _ _ _).symm

theorem expected_freshEncoding_otsSignFrom_eq_search (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (secret : ChainIndex → Digest)
    (message : Digest) (attempts counter : Nat) (cache : QueryCache HashSpec) :
    expectedQueryCharge (freshEncodingHashCharge parameter)
        (liftM (otsSignFrom parameter lay tree leafIdx secret message attempts counter : OracleComp HashSpec _)) cache =
      expectedQueryCharge freshCacheCharge
        (liftM (encodingSearchFrom parameter lay tree leafIdx message attempts counter)) cache := by
  induction attempts generalizing counter cache with
  | zero => simp [otsSignFrom, encodingSearchFrom]
  | succ attempts ih =>
      rw [otsSignFrom, encodingSearchFrom, liftM_bind, liftM_bind, expectedQueryCharge_bind, expectedQueryCharge_bind,
        expected_freshEncoding_encode_eq_fresh]
      congr 1
      apply tsum_congr
      intro result
      congr 1
      cases result.1 with
      | none => exact ih (counter + 1) result.2
      | some encoding =>
          rw [liftM_bind, expectedQueryCharge_bind]
          rw [expected_freshEncoding_eq_zero_of_avoidsEncoding parameter _ (fun f =>
            avoidsEncodingQueries_sequenceFin parameter f _ (fun chainIdx =>
              QueriesAtPositions.avoidsEncoding (queriesAtPositions_chainWalk parameter f lay tree leafIdx chainIdx 0 _ _)))]
          simp

theorem expectedPreException_freshEncoding_otsSignFrom_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (secret : ChainIndex → Digest)
    (message : Digest) (attempts counter : Nat) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (freshEncodingHashCharge parameter)
      (liftM (otsSignFrom parameter lay tree leafIdx secret message attempts counter : OracleComp HashSpec _)) cache hit ≤ 24576 := by
  apply (expectedPreExceptionCharge_le_queryCharge _ _ _ _ _).trans
  rw [expected_freshEncoding_otsSignFrom_eq_search]
  exact (expected_fresh_encodingSearchFrom_le_success_budget _ _ _ _ _ _ _ _).trans
    ((mul_le_mul' probEvent_le_one le_rfl).trans_eq (one_mul _))

theorem expectedPreException_freshEncoding_signLayer_le_reserved
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (index : Index) (lay : Layer) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (freshEncodingHashCharge key.parameter)
        (liftM (signLayer key index lay : OracleComp HashSpec _)) cache hit ≤
      expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter)
        (liftM (signLayer key index lay : OracleComp HashSpec _)) cache hit := by
  rw [signLayer, liftM_bind]
  apply expectedPreExceptionCharge_bind_le_of_survivalCost _ _ _ _ _ 24576
    (preExceptionSurvivalCost_reserved_layerMessage_encodingBudget _ _ _ _)
  · intro message current
    rw [liftM_bind, expectedPreExceptionCharge_bind]
    apply le_trans (add_le_add (expectedPreException_freshEncoding_otsSignFrom_le _ _ _ _ _ _ _ _ _ _ _) ?_)
      (show (24576 : ENNReal) + 0 ≤ (24576 : Nat) by norm_num)
    apply le_of_eq
    apply ENNReal.tsum_eq_zero.mpr
    intro result
    cases result.1.1 with
    | none => simp
    | some part =>
        rw [liftM_bind, expectedPreExceptionCharge_bind,
          expectedPreException_freshEncoding_eq_zero_of_avoidsEncoding exception key.parameter _
            (fun f => avoidsEncodingQueries_treePath _ f _ _ _ _)]
        simp
  · exact expectedPreException_freshEncoding_eq_zero_of_avoidsEncoding exception key.parameter _
      (fun f => avoidsEncodingQueries_layerMessage f key index lay) cache hit

theorem expectedPreException_freshEncoding_sign_le_reserved
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (freshEncodingHashCharge key.parameter) (sign key message) cache hit ≤
      expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter) (sign key message) cache hit := by
  rw [sign]
  apply expectedPreExceptionCharge_bind_le_bind
  · rw [expectedPreExceptionCharge_eq_zero_of_queryCharge_eq_zero exception _ _ _ _
      (expected_freshEncoding_signDigestLoop_eq_zero key message _ cache)]
    exact zero_le
  · intro selected _
    cases selected.1.1 with
    | none => simp
    | some selectedDigest =>
        apply expectedPreExceptionCharge_bind_le_bind
        · rw [expectedPreException_freshEncoding_eq_zero_of_avoidsEncoding exception key.parameter _
            (fun f => avoidsEncodingQueries_ftsOpen _ f _ _ _)]
          exact zero_le
        · intro opening _
          apply expectedPreExceptionCharge_bind_le_bind
          · apply expectedPreExceptionCharge_lift_sequenceFin_le
            intro lay current currentHit
            exact expectedPreException_freshEncoding_signLayer_le_reserved exception key selectedDigest.2.1 lay current currentHit
          · intro layers _
            split <;> simp

end SphincsSecurity.Concrete.FtsProbeSimulation
