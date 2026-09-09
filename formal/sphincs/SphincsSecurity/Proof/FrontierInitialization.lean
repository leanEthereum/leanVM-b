import SphincsSecurity.Proof.FrontierSigningOracleCongruence

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local irreducible] referenceEncodingSearch
set_option backward.isDefEq.respectTransparency false

noncomputable def frontierEncodingSearch (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (cutWords : OtsReferenceWords)
    (cutValues : OtsFrontierValues) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    Option (Counter × Encoding) × Nat :=
  referenceEncodingSearch parameter f lay tree leaf
    (evalWithAnswerFn f (frontierLayerMessage parameter ftsSecret cutWords cutValues
      (referenceIndex lay tree leaf) lay)) encodingAttemptLimit 0

theorem canonicalEncodingSearch_eq_frontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (cutWords : OtsReferenceWords) (cutValues : OtsFrontierValues)
    (hcut : IsSigningFrontier key f cutWords cutValues) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    canonicalEncodingSearch key f lay tree leaf =
      frontierEncodingSearch key.parameter f key.ftsSecret cutWords cutValues lay tree leaf := by
  rw [canonicalEncodingSearch, frontierEncodingSearch, eval_frontierLayerMessage key f cutWords cutValues hcut]

theorem frontierEncodingSearch_eq_of_agree (parameter : PublicParameter) (cutWords : OtsReferenceWords)
    (f g : QueryImpl HashSpec Id) (h : AgreeOutsideOtsPrefixes parameter cutWords f g)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (cutValues : OtsFrontierValues)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    frontierEncodingSearch parameter f ftsSecret cutWords cutValues lay tree leaf =
      frontierEncodingSearch parameter g ftsSecret cutWords cutValues lay tree leaf := by
  rw [frontierEncodingSearch, frontierEncodingSearch,
    eval_frontierLayerMessage_eq_of_agree parameter cutWords f g h,
    referenceEncodingSearch_eq_of_agree parameter cutWords f g h]

theorem canonicalEncodingSearch_eq_masked_frontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (cutWords : OtsReferenceWords) (cutValues : OtsFrontierValues)
    (hcut : IsSigningFrontier key f cutWords cutValues) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    canonicalEncodingSearch key f lay tree leaf =
      frontierEncodingSearch key.parameter (maskOtsPrefixes key.parameter cutWords f)
        key.ftsSecret cutWords cutValues lay tree leaf := by
  rw [canonicalEncodingSearch_eq_frontier key f cutWords cutValues hcut]
  exact frontierEncodingSearch_eq_of_agree key.parameter cutWords f (maskOtsPrefixes key.parameter cutWords f)
    (maskOtsPrefixes_agrees key.parameter cutWords f) key.ftsSecret cutValues lay tree leaf

noncomputable def frontierReferenceWords (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (cutWords : OtsReferenceWords)
    (cutValues : OtsFrontierValues) (dummy : OtsReferenceWords) : OtsReferenceWords :=
  fun lay tree leaf =>
    ((frontierEncodingSearch parameter f ftsSecret cutWords cutValues lay tree leaf).1.map Prod.snd).getD
      (dummy lay tree leaf)

theorem canonicalReferenceWords_eq_masked_frontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (cutWords : OtsReferenceWords) (cutValues : OtsFrontierValues)
    (hcut : IsSigningFrontier key f cutWords cutValues) (dummy : OtsReferenceWords) :
    canonicalReferenceWords key f dummy =
      frontierReferenceWords key.parameter (maskOtsPrefixes key.parameter cutWords f)
        key.ftsSecret cutWords cutValues dummy := by
  funext lay tree leaf
  simp only [canonicalReferenceWords, frontierReferenceWords,
    canonicalEncodingSearch_eq_masked_frontier key f cutWords cutValues hcut]

theorem frontierRoot_masked_eq (key : SecretKey) (f : QueryImpl HashSpec Id)
    (cutWords : OtsReferenceWords) (cutValues : OtsFrontierValues)
    (hcut : IsSigningFrontier key f cutWords cutValues) :
    frontierRoot key.parameter (maskOtsPrefixes key.parameter cutWords f) cutWords cutValues =
      evalWithAnswerFn f (treeRoot key.parameter topLayer rootTree (key.otsSecret topLayer rootTree)) := by
  rw [← frontierRoot_eq_of_agree key.parameter cutWords f (maskOtsPrefixes key.parameter cutWords f)
    (maskOtsPrefixes_agrees key.parameter cutWords f)]
  exact frontierRoot_eq key f cutWords cutValues hcut

end SphincsSecurity.Concrete
