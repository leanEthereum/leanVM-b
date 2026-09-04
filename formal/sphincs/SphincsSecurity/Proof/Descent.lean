import SphincsSecurity.Proof.SettledPath
import SphincsSecurity.Proof.HitBad
import SphincsSecurity.Proof.Hypertree

/-!
# Deterministic forgery descent

At one hypertree layer, acceptance at the honest root either creates `Bad`, or the supplied chain
values and authentication path are exactly the honest values selected by the decoded codeword.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

variable {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
  {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
  {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
  {cache : QueryCache HashSpec}

theorem verify_extract (publicKey : PublicKey) (message : Message) (signature : Signature)
    (hverify : evalWithAnswerFn f (verify publicKey message signature) = true)
    (hrun : CachedRun cache f (verify publicKey message signature)) :
    ∃ digest : MessageDigest,
      evalWithAnswerFn f
          (messageDigest publicKey.parameter publicKey.root message signature.randomness) = digest
        ∧ CachedRun cache f
          (messageDigest publicKey.parameter publicKey.root message signature.randomness)
        ∧ Admissible digest
        ∧ let index := digestIndex digest
          let leaves := digestLeaves digest
          let ftsPublicKey := evalWithAnswerFn f
            (ftsRecover publicKey.parameter index leaves signature.ftsSecret signature.ftsPath)
          evalWithAnswerFn f
              (verifyLayers publicKey.parameter index signature numLayers ftsPublicKey)
              = some publicKey.root
            ∧ CachedRun cache f
              (ftsRecover publicKey.parameter index leaves signature.ftsSecret signature.ftsPath)
            ∧ CachedRun cache f
              (verifyLayers publicKey.parameter index signature numLayers ftsPublicKey) := by
  let digest := evalWithAnswerFn f
    (messageDigest publicKey.parameter publicKey.root message signature.randomness)
  have hadmissible : Admissible digest := by
    by_contra hnot
    rw [verify_eq, evalWithAnswerFn_bind] at hverify
    simp only [digest] at hnot
    rw [if_pos hnot] at hverify
    simp at hverify
  let index := digestIndex digest
  let leaves := digestLeaves digest
  let ftsPublicKey := evalWithAnswerFn f
    (ftsRecover publicKey.parameter index leaves signature.ftsSecret signature.ftsPath)
  have hlayers : evalWithAnswerFn f
      (verifyLayers publicKey.parameter index signature numLayers ftsPublicKey)
      = some publicKey.root := by
    rw [verify_eq, evalWithAnswerFn_bind] at hverify
    simp only [digest, hadmissible, not_true_eq_false, if_false, evalWithAnswerFn_bind] at hverify
    cases hresult : evalWithAnswerFn f
        (verifyLayers publicKey.parameter index signature numLayers ftsPublicKey) with
    | none =>
        rw [hresult] at hverify
        simp at hverify
    | some root =>
        rw [hresult] at hverify
        simp only [evalWithAnswerFn_pure, decide_eq_true_eq] at hverify
        simp [hverify]
  rw [verify_eq] at hrun
  have hmessageRun := hrun.bind_left
  have hafterDigest := hrun.bind_right
  simp only [digest, hadmissible, not_true_eq_false, if_false] at hafterDigest
  change CachedRun cache f (do
    let ftsPublicKey ←
      ftsRecover publicKey.parameter index leaves signature.ftsSecret signature.ftsPath
    match ← verifyLayers publicKey.parameter index signature numLayers ftsPublicKey with
    | none => pure false
    | some root => pure (decide (root = publicKey.root))) at hafterDigest
  have hfts : CachedRun cache f
      (ftsRecover publicKey.parameter index leaves signature.ftsSecret signature.ftsPath) :=
    hafterDigest.bind_left
  have hlayersRun : CachedRun cache f
      (verifyLayers publicKey.parameter index signature numLayers ftsPublicKey) := by
    have := hafterDigest.bind_right.bind_left
    simpa only [ftsPublicKey] using this
  exact ⟨digest, rfl, hmessageRun, hadmissible, hlayers, hfts, hlayersRun⟩

theorem verifyLayers_succ_extract_cached (index : Index) (signature : Signature)
    (remaining : Nat) (hlayer : remaining < numLayers) (message target : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayers parameter index signature (remaining + 1) message) = some target)
    (hrun : CachedRun cache f
      (verifyLayers parameter index signature (remaining + 1) message)) :
    ∃ leafValue,
      let lay : Layer := ⟨remaining, hlayer⟩
      let tree := treeIndexAt index lay
      let leafIdx := leafIndexAt index lay
      let rootValue := foldValue f parameter lay tree leafIdx (signaturePath signature lay)
        leafValue (layerHeight lay)
      evalWithAnswerFn f (otsLeaf parameter lay tree leafIdx message (signature.counter lay)
          (signature.chainValue lay)) = some leafValue
        ∧ evalWithAnswerFn f (verifyLayers parameter index signature remaining rootValue)
          = some target
        ∧ CachedRun cache f (otsLeaf parameter lay tree leafIdx message (signature.counter lay)
          (signature.chainValue lay))
        ∧ CachedRun cache f (treeFold parameter lay tree leafIdx (signaturePath signature lay)
          (layerHeight lay) leafValue)
        ∧ CachedRun cache f (verifyLayers parameter index signature remaining rootValue) := by
  obtain ⟨leafValue, hleaf, hrest⟩ :=
    verifyLayers_succ_extract f parameter index signature remaining hlayer message target hverify
  rw [verifyLayers_succ_eq, dif_pos hlayer] at hrun
  have hots := hrun.bind_left
  have hafter := hrun.bind_right
  rw [hleaf] at hafter
  exact ⟨leafValue, hleaf, hrest, hots, hafter.bind_left, hafter.bind_right⟩

def LayerFrame (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (index : Index) (signature : Signature)
    (lay : Layer) (message target leafValue : Digest) : Prop :=
  evalWithAnswerFn f
        (otsLeaf parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message
          (signature.counter lay) (signature.chainValue lay)) = some leafValue
      ∧ evalWithAnswerFn f
        (verifyLayers parameter index signature lay.val
          (foldValue f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (signaturePath signature lay) leafValue (layerHeight lay))) = some target
      ∧ CachedRun cache f
        (otsLeaf parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message
          (signature.counter lay) (signature.chainValue lay))
      ∧ CachedRun cache f
        (treeFold parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (signaturePath signature lay) (layerHeight lay) leafValue)
      ∧ CachedRun cache f
        (verifyLayers parameter index signature lay.val
          (foldValue f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (signaturePath signature lay) leafValue (layerHeight lay)))

def LayerRun (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (index : Index) (signature : Signature)
    (lay : Layer) (message target : Digest) : Prop :=
  ∃ leafValue, LayerFrame f cache parameter index signature lay message target leafValue

theorem layerRun_of_verify (index : Index) (signature : Signature)
    (lay : Layer) (message target : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayers parameter index signature (lay.val + 1) message) = some target)
    (hrun : CachedRun cache f
      (verifyLayers parameter index signature (lay.val + 1) message)) :
    LayerRun f cache parameter index signature lay message target := by
  obtain ⟨leafValue, hleaf, hnext, hleafRun, hfoldRun, hnextRun⟩ :=
    verifyLayers_succ_extract_cached (f := f) (cache := cache) index signature lay.val lay.isLt
      message target hverify hrun
  exact ⟨leafValue, hleaf, hnext, hleafRun, hfoldRun, hnextRun⟩

def HypertreeRun (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (index : Index) (signature : Signature)
    (message target : Digest) : Prop :=
  ∃ bottomLeaf,
    LayerFrame f cache parameter index signature bottomLayer message target bottomLeaf
      ∧ let middleMessage := foldValue f parameter bottomLayer
          (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer)
          (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer)
        ∃ middleLeaf,
          LayerFrame f cache parameter index signature middleLayer middleMessage target middleLeaf
            ∧ let topMessage := foldValue f parameter middleLayer
                (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
                (signaturePath signature middleLayer) middleLeaf (layerHeight middleLayer)
              LayerRun f cache parameter index signature topLayer topMessage target

theorem hypertreeRun_of_verify (index : Index) (signature : Signature)
    (message target : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayers parameter index signature numLayers message) = some target)
    (hrun : CachedRun cache f
      (verifyLayers parameter index signature numLayers message)) :
    HypertreeRun f cache parameter index signature message target := by
  have hbottom := layerRun_of_verify (f := f) (cache := cache) index signature bottomLayer
    message target (by simpa only [numLayers, bottomLayer] using hverify)
    (by simpa only [numLayers, bottomLayer] using hrun)
  obtain ⟨bottomLeaf, hbottom⟩ := hbottom
  let middleMessage := foldValue f parameter bottomLayer
    (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer)
    (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer)
  have hmiddle := layerRun_of_verify (f := f) (cache := cache) index signature middleLayer
    middleMessage target (by
      simpa only [middleMessage, bottomLayer, middleLayer, numLayers] using hbottom.2.1)
    (by simpa only [middleMessage, bottomLayer, middleLayer, numLayers] using hbottom.2.2.2.2)
  obtain ⟨middleLeaf, hmiddle⟩ := hmiddle
  let topMessage := foldValue f parameter middleLayer
    (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
    (signaturePath signature middleLayer) middleLeaf (layerHeight middleLayer)
  have htop := layerRun_of_verify (f := f) (cache := cache) index signature topLayer
    topMessage target (by simpa only [topMessage, middleLayer, topLayer] using hmiddle.2.1)
    (by simpa only [topMessage, middleLayer, topLayer] using hmiddle.2.2.2.2)
  exact ⟨bottomLeaf, hbottom, middleLeaf, hmiddle, htop⟩

theorem layer_extract_or_bad (hf : cache.AgreesWithFn f) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) (counter : Counter)
    (values : ChainIndex → Digest) (path : Nat → Digest) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leafIdx message counter)
      = some codeword) (leafValue : Digest)
    (hleaf : evalWithAnswerFn f
      (otsLeaf parameter lay tree leafIdx message counter values) = some leafValue)
    (hfold : foldValue f parameter lay tree leafIdx path leafValue (layerHeight lay)
      = honestNode f parameter lay tree (otsSecret lay tree) (layerHeight lay)
        (leafIdx.val / 2 ^ layerHeight lay))
    (hotsRun : CachedRun cache f (otsLeaf parameter lay tree leafIdx message counter values))
    (hfoldRun : CachedRun cache f
      (treeFold parameter lay tree leafIdx path (layerHeight lay) leafValue))
    (hchains : ∀ chainIdx position (hposition : position < chainLength - 1),
      Settled parameter otsSecret ftsSecret cache
        (.chain lay tree leafIdx chainIdx ⟨position, hposition⟩))
    (hleafSettled : Settled parameter otsSecret ftsSecret cache (.leaf lay tree leafIdx))
    (hnodes : ∀ level (hlevel : level < layerHeight lay),
      Settled parameter otsSecret ftsSecret cache
        (.node lay tree ⟨level, lt_of_lt_of_le hlevel (layerHeight_le lay)⟩
          ⟨leafIdx.val / 2 ^ (level + 1), lt_of_le_of_lt (Nat.div_le_self _ _)
            leafIdx.isLt⟩)) :
    Bad parameter otsSecret ftsSecret cache ∨
      ((∀ chainIdx, values chainIdx
          = honestChain f parameter lay tree leafIdx chainIdx
            (otsSecret lay tree leafIdx chainIdx) (codeword chainIdx).val)
        ∧ ∀ level, level < layerHeight lay → path level
          = honestNode f parameter lay tree (otsSecret lay tree) level
            (Nat.xor (leafIdx.val / 2 ^ level) 1)) := by
  rcases treeFold_extract f parameter lay tree (otsSecret lay tree) leafIdx path leafValue
      (layerHeight lay) hfold with ⟨hleafValue, hpath⟩ | ⟨level, hlevel, hhit⟩
  · have hleafHonest : evalWithAnswerFn f
        (otsLeaf parameter lay tree leafIdx message counter values)
        = some (honestNode f parameter lay tree (otsSecret lay tree) 0 leafIdx.val) := by
      rw [hleaf, hleafValue]
    rcases otsLeaf_extract f parameter lay tree (otsSecret lay tree) leafIdx message counter values
        codeword hencode hleafHonest with hvalues | hhit | ⟨chainIdx, offset, hrange, hoffset, hhit⟩
    · exact Or.inr ⟨hvalues, hpath⟩
    · left
      apply bad_of_leafHit hf lay tree leafIdx _ hhit hleafSettled
      apply hotsRun
      exact otsLeaf_leaf_query_mem f parameter lay tree leafIdx message counter values codeword hencode
    · left
      apply bad_of_chainHit hf lay tree leafIdx chainIdx ((codeword chainIdx).val + offset)
        hrange _ hhit (hchains chainIdx _ hrange)
      apply hotsRun
      exact otsLeaf_chain_query_mem f parameter lay tree leafIdx message counter values codeword
        hencode chainIdx offset hoffset hrange
  · left
    have hlevelMax : level < maxLayerHeight := lt_of_lt_of_le hlevel (layerHeight_le lay)
    have hnodeIdx : leafIdx.val / 2 ^ (level + 1) < 2 ^ maxLayerHeight :=
      lt_of_le_of_lt (Nat.div_le_self _ _) leafIdx.isLt
    apply bad_of_nodeHit hf lay tree level (leafIdx.val / 2 ^ (level + 1)) hlevelMax
      hnodeIdx _ hhit (hnodes level hlevel)
    apply hfoldRun
    exact treeFold_query_mem f parameter lay tree leafIdx path leafValue (layerHeight lay) level hlevel

theorem layer_extract_or_bad' (hf : cache.AgreesWithFn f) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) (counter : Counter)
    (values : ChainIndex → Digest) (path : Nat → Digest) (leafValue : Digest)
    (hleaf : evalWithAnswerFn f
      (otsLeaf parameter lay tree leafIdx message counter values) = some leafValue)
    (hfold : foldValue f parameter lay tree leafIdx path leafValue (layerHeight lay)
      = honestNode f parameter lay tree (otsSecret lay tree) (layerHeight lay)
        (leafIdx.val / 2 ^ layerHeight lay))
    (hotsRun : CachedRun cache f (otsLeaf parameter lay tree leafIdx message counter values))
    (hfoldRun : CachedRun cache f
      (treeFold parameter lay tree leafIdx path (layerHeight lay) leafValue))
    (hchains : ∀ chainIdx position (hposition : position < chainLength - 1),
      Settled parameter otsSecret ftsSecret cache
        (.chain lay tree leafIdx chainIdx ⟨position, hposition⟩))
    (hleafSettled : Settled parameter otsSecret ftsSecret cache (.leaf lay tree leafIdx))
    (hnodes : ∀ level (hlevel : level < layerHeight lay),
      Settled parameter otsSecret ftsSecret cache
        (.node lay tree ⟨level, lt_of_lt_of_le hlevel (layerHeight_le lay)⟩
          ⟨leafIdx.val / 2 ^ (level + 1), lt_of_le_of_lt (Nat.div_le_self _ _)
            leafIdx.isLt⟩)) :
    Bad parameter otsSecret ftsSecret cache ∨ ∃ codeword : Encoding,
      evalWithAnswerFn f (encode parameter lay tree leafIdx message counter) = some codeword
        ∧ (∀ chainIdx, values chainIdx
          = honestChain f parameter lay tree leafIdx chainIdx
            (otsSecret lay tree leafIdx chainIdx) (codeword chainIdx).val)
        ∧ ∀ level, level < layerHeight lay → path level
          = honestNode f parameter lay tree (otsSecret lay tree) level
            (Nat.xor (leafIdx.val / 2 ^ level) 1) := by
  cases hencode : evalWithAnswerFn f (encode parameter lay tree leafIdx message counter) with
  | none =>
      simp only [otsLeaf, evalWithAnswerFn_bind, hencode, evalWithAnswerFn_pure] at hleaf
      simp at hleaf
  | some codeword =>
      rcases layer_extract_or_bad hf lay tree leafIdx message counter values path codeword hencode
          leafValue hleaf hfold hotsRun hfoldRun hchains hleafSettled hnodes with hbad | hhonest
      · exact Or.inl hbad
      · exact Or.inr ⟨codeword, rfl, hhonest⟩

def HonestLayerOpening (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (counter : Counter) (values : ChainIndex → Digest) (path : Nat → Digest) : Prop :=
  ∃ codeword : Encoding,
    evalWithAnswerFn f (encode parameter lay tree leafIdx message counter) = some codeword
      ∧ (∀ chainIdx, values chainIdx
        = honestChain f parameter lay tree leafIdx chainIdx
          (otsSecret lay tree leafIdx chainIdx) (codeword chainIdx).val)
      ∧ ∀ level, level < layerHeight lay → path level
        = honestNode f parameter lay tree (otsSecret lay tree) level
          (Nat.xor (leafIdx.val / 2 ^ level) 1)

theorem layer_extract_from_settled_root_or_bad (hf : cache.AgreesWithFn f)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (hleafIdx : leafIdx.val < 2 ^ layerHeight lay) (message : Digest) (counter : Counter)
    (values : ChainIndex → Digest) (path : Nat → Digest) (leafValue : Digest)
    (hleaf : evalWithAnswerFn f
      (otsLeaf parameter lay tree leafIdx message counter values) = some leafValue)
    (hfold : foldValue f parameter lay tree leafIdx path leafValue (layerHeight lay)
      = honestNode f parameter lay tree (otsSecret lay tree) (layerHeight lay) 0)
    (hotsRun : CachedRun cache f (otsLeaf parameter lay tree leafIdx message counter values))
    (hfoldRun : CachedRun cache f
      (treeFold parameter lay tree leafIdx path (layerHeight lay) leafValue))
    (hroot : Settled parameter otsSecret ftsSecret cache
      (.node lay tree ⟨layerHeight lay - 1, by
        have hpos : 0 < layerHeight lay := by unfold layerHeight; split <;> norm_num [maxLayerHeight]
        have hle := layerHeight_le lay
        omega⟩ ⟨0, by positivity⟩)) :
    Bad parameter otsSecret ftsSecret cache ∨
      HonestLayerOpening f parameter otsSecret lay tree leafIdx message counter values path := by
  obtain ⟨hleafSettled, hnodes⟩ :=
    settled_tree_path_of_settled_root lay tree leafIdx hleafIdx hroot
  apply layer_extract_or_bad' hf lay tree leafIdx message counter values path leafValue hleaf
  · simpa only [Nat.div_eq_of_lt hleafIdx] using hfold
  · exact hotsRun
  · exact hfoldRun
  · intro chainIdx position hposition
    exact settled_chain_of_settled_leaf lay tree leafIdx hleafSettled chainIdx position hposition
  · exact hleafSettled
  · exact hnodes

def HypertreeTopOpening (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (index : Index) (signature : Signature) (message target : Digest) : Prop :=
  ∃ bottomLeaf,
    LayerFrame f cache parameter index signature bottomLayer message target bottomLeaf
      ∧ let middleMessage := foldValue f parameter bottomLayer
          (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer)
          (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer)
        ∃ middleLeaf,
          LayerFrame f cache parameter index signature middleLayer middleMessage target middleLeaf
            ∧ let topMessage := foldValue f parameter middleLayer
                (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
                (signaturePath signature middleLayer) middleLeaf (layerHeight middleLayer)
              HonestLayerOpening f parameter otsSecret topLayer (treeIndexAt index topLayer)
                (leafIndexAt index topLayer) topMessage (signature.counter topLayer)
                (signature.chainValue topLayer) (signaturePath signature topLayer)
                ∧ CachedRun cache f (otsLeaf parameter topLayer (treeIndexAt index topLayer)
                  (leafIndexAt index topLayer) topMessage (signature.counter topLayer)
                  (signature.chainValue topLayer))

theorem hypertree_top_extract_or_bad (hf : cache.AgreesWithFn f)
    (index : Index) (signature : Signature) (message target : Digest)
    (hrun : HypertreeRun f cache parameter index signature message target)
    (htarget : target
      = honestNode f parameter topLayer rootTree (otsSecret topLayer rootTree)
          (layerHeight topLayer) 0)
    (hroot : Settled parameter otsSecret ftsSecret cache
      (.node topLayer rootTree ⟨layerHeight topLayer - 1, by decide⟩ ⟨0, by positivity⟩)) :
    Bad parameter otsSecret ftsSecret cache ∨
      HypertreeTopOpening f cache parameter otsSecret index signature message target := by
  obtain ⟨bottomLeaf, hbottom, middleLeaf, hmiddle, topLeaf, htop⟩ := hrun
  let topMessage := foldValue f parameter middleLayer
    (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
    (signaturePath signature middleLayer) middleLeaf (layerHeight middleLayer)
  have htopFold : foldValue f parameter topLayer (treeIndexAt index topLayer)
      (leafIndexAt index topLayer) (signaturePath signature topLayer) topLeaf
      (layerHeight topLayer) = target := by
    have := htop.2.1
    simpa only [topLayer, verifyLayers_zero_eq, evalWithAnswerFn_pure,
      Option.some.injEq] using this
  have htree : treeIndexAt index topLayer = rootTree := by
    apply Fin.ext
    exact treeIndexAt_topLayer index
  have hroot' : Settled parameter otsSecret ftsSecret cache
      (.node topLayer (treeIndexAt index topLayer)
        ⟨layerHeight topLayer - 1, by decide⟩ ⟨0, by positivity⟩) := by
    simpa only [htree] using hroot
  have hfold : foldValue f parameter topLayer (treeIndexAt index topLayer)
      (leafIndexAt index topLayer) (signaturePath signature topLayer) topLeaf
      (layerHeight topLayer)
      = honestNode f parameter topLayer (treeIndexAt index topLayer)
          (otsSecret topLayer (treeIndexAt index topLayer)) (layerHeight topLayer) 0 := by
    rw [htopFold, htarget, htree]
  rcases layer_extract_from_settled_root_or_bad hf topLayer (treeIndexAt index topLayer)
      (leafIndexAt index topLayer) (leafIndexAt_lt index topLayer) topMessage
      (signature.counter topLayer) (signature.chainValue topLayer)
      (signaturePath signature topLayer) topLeaf htop.1 hfold htop.2.2.1 htop.2.2.2.1
      hroot' with hbad | hhonest
  · exact Or.inl hbad
  · exact Or.inr ⟨bottomLeaf, hbottom, middleLeaf, hmiddle, hhonest, htop.2.2.1⟩

theorem ftsTree_extract_or_bad (hf : cache.AgreesWithFn f) (index : Index)
    (leaves : DigestTree → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest) (tree : FtsTree)
    (hfold : ftsFoldValue f parameter index tree (leaves (ftsIndexOf tree)) (paths tree)
      (truncateHash (f (tweakableHashInput parameter
        (.ftsLeaf index tree (leaves (ftsIndexOf tree))) (digestBytes (secrets tree)))))
      ftsTreeHeight = honestFtsNode f parameter index tree (ftsSecret index tree)
        ftsTreeHeight 0)
    (hrun : CachedRun cache f (ftsRecover parameter index leaves secrets paths))
    (hleafSettled : Settled parameter otsSecret ftsSecret cache
      (.ftsLeaf index tree (leaves (ftsIndexOf tree))))
    (hnodes : ∀ level (hlevel : level < ftsTreeHeight),
      Settled parameter otsSecret ftsSecret cache
        (.ftsNode index tree ⟨level, hlevel⟩
          ⟨(leaves (ftsIndexOf tree)).val / 2 ^ (level + 1),
            lt_of_le_of_lt (Nat.div_le_self _ _) (leaves (ftsIndexOf tree)).isLt⟩)) :
    Bad parameter otsSecret ftsSecret cache ∨
      (secrets tree = ftsSecret index tree (leaves (ftsIndexOf tree))
        ∧ ∀ level (hlevel : level < ftsTreeHeight), paths tree ⟨level, hlevel⟩
          = honestFtsNode f parameter index tree (ftsSecret index tree) level
            (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level) 1)) := by
  let leafIdx := leaves (ftsIndexOf tree)
  let leafValue := truncateHash (f (tweakableHashInput parameter
    (.ftsLeaf index tree leafIdx) (digestBytes (secrets tree))))
  have hroot : leafIdx.val / 2 ^ ftsTreeHeight = 0 := Nat.div_eq_of_lt leafIdx.isLt
  rcases ftsFold_extract f parameter index tree (ftsSecret index tree) leafIdx (paths tree)
      leafValue ftsTreeHeight (le_refl _) (by simpa only [leafIdx, leafValue, hroot] using hfold) with
    ⟨hleafValue, hpath⟩ | ⟨level, hlevel, hhit⟩
  · rcases ftsLeaf_extract f parameter index tree (ftsSecret index tree) leafIdx (secrets tree)
      hleafValue with hsecret | hhit
    · right
      refine ⟨hsecret, ?_⟩
      intro level hlevel
      simpa only [ftsSibling, dif_pos hlevel, leafIdx] using hpath level hlevel
    · left
      apply bad_of_ftsLeafHit hf index tree leafIdx (secrets tree) hhit hleafSettled
      apply hrun
      exact ftsRecover_leaf_query_mem f parameter index leaves secrets paths tree
  · left
    have hnodeIdx : leafIdx.val / 2 ^ (level + 1) < 2 ^ ftsTreeHeight :=
      lt_of_le_of_lt (Nat.div_le_self _ _) leafIdx.isLt
    apply bad_of_ftsNodeHit hf index tree level (leafIdx.val / 2 ^ (level + 1)) hlevel
      hnodeIdx _ hhit (hnodes level hlevel)
    apply hrun
    exact ftsRecover_fold_query_mem f parameter index leaves secrets paths tree level hlevel

theorem ftsRecover_extract_or_bad (hf : cache.AgreesWithFn f) (index : Index)
    (leaves : DigestTree → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest)
    (hrecover : evalWithAnswerFn f (ftsRecover parameter index leaves secrets paths)
      = honestFtsKey f parameter index (ftsSecret index))
    (hrun : CachedRun cache f (ftsRecover parameter index leaves secrets paths))
    (hrootsSettled : Settled parameter otsSecret ftsSecret cache (.ftsRoots index))
    (hleavesSettled : ∀ tree, Settled parameter otsSecret ftsSecret cache
      (.ftsLeaf index tree (leaves (ftsIndexOf tree))))
    (hnodes : ∀ tree level (hlevel : level < ftsTreeHeight),
      Settled parameter otsSecret ftsSecret cache
        (.ftsNode index tree ⟨level, hlevel⟩
          ⟨(leaves (ftsIndexOf tree)).val / 2 ^ (level + 1),
            lt_of_le_of_lt (Nat.div_le_self _ _) (leaves (ftsIndexOf tree)).isLt⟩)) :
    Bad parameter otsSecret ftsSecret cache ∨
      ∀ tree, secrets tree = ftsSecret index tree (leaves (ftsIndexOf tree))
        ∧ ∀ level (hlevel : level < ftsTreeHeight), paths tree ⟨level, hlevel⟩
          = honestFtsNode f parameter index tree (ftsSecret index tree) level
            (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level) 1) := by
  let roots : FtsTree → Digest := fun tree => evalWithAnswerFn f
    (ftsFold parameter index tree (leaves (ftsIndexOf tree)) (paths tree) ftsTreeHeight
      (evalWithAnswerFn f
        (ftsLeafHash parameter index tree (leaves (ftsIndexOf tree)) (secrets tree))))
  by_cases hpayload : ftsRootsPayload roots
      = honestPayload f parameter otsSecret ftsSecret (.ftsRoots index)
  · have hrootValues : roots = fun tree =>
        honestFtsNode f parameter index tree (ftsSecret index tree) ftsTreeHeight 0 := by
      apply TargetSum.ftsRootsPayload_injective
      simpa only [roots, honestPayload] using hpayload
    by_cases hbad : Bad parameter otsSecret ftsSecret cache
    · exact Or.inl hbad
    · right
      intro tree
      have hfold : ftsFoldValue f parameter index tree (leaves (ftsIndexOf tree)) (paths tree)
          (truncateHash (f (tweakableHashInput parameter
            (.ftsLeaf index tree (leaves (ftsIndexOf tree))) (digestBytes (secrets tree)))))
          ftsTreeHeight = honestFtsNode f parameter index tree (ftsSecret index tree)
            ftsTreeHeight 0 := by
        have := congrFun hrootValues tree
        simpa only [roots, evalWithAnswerFn_bind, ftsLeafHash, eval_tweakableHash,
          ftsFoldValue] using this
      rcases ftsTree_extract_or_bad hf index leaves secrets paths tree hfold hrun
          (hleavesSettled tree) (hnodes tree) with hbad' | hhonest
      · exact absurd hbad' hbad
      · exact hhonest
  · left
    apply bad_of_settled_payload_collision parameter otsSecret ftsSecret hf hrootsSettled hpayload
    · apply hrun
      have hmem := ftsRecover_roots_query_mem f parameter index leaves secrets paths
      convert hmem using 1
      all_goals simp [roots, Position.domain]
    · rw [honestValue_ftsRoots]
      have hvalue := hrecover
      simp only [ftsRecover, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
        eval_tweakableHash] at hvalue
      change truncateHash (f (tweakableHashInput parameter (.ftsRoots index)
        (ftsRootsPayload roots))) = honestFtsKey f parameter index (ftsSecret index)
      dsimp only [roots]
      simpa only [evalWithAnswerFn_bind] using hvalue

theorem ftsRecover_extract_from_settled_roots_or_bad (hf : cache.AgreesWithFn f)
    (index : Index) (leaves : DigestTree → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest)
    (hrecover : evalWithAnswerFn f (ftsRecover parameter index leaves secrets paths)
      = honestFtsKey f parameter index (ftsSecret index))
    (hrun : CachedRun cache f (ftsRecover parameter index leaves secrets paths))
    (hroots : Settled parameter otsSecret ftsSecret cache (.ftsRoots index)) :
    Bad parameter otsSecret ftsSecret cache ∨
      ∀ tree, secrets tree = ftsSecret index tree (leaves (ftsIndexOf tree))
        ∧ ∀ level (hlevel : level < ftsTreeHeight), paths tree ⟨level, hlevel⟩
          = honestFtsNode f parameter index tree (ftsSecret index tree) level
            (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level) 1) := by
  obtain ⟨hleaves, hnodes⟩ := settled_fts_path_of_settled_roots index leaves hroots
  exact ftsRecover_extract_or_bad hf index leaves secrets paths hrecover hrun hroots
    hleaves hnodes

end SphincsSecurity.Concrete
