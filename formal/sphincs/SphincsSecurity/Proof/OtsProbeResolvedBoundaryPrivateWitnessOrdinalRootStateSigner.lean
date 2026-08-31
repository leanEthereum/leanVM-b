import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootState

/-!
# Swapped-root signer state coupling

The selected root reveal is the only primitive whose returned digest differs in the two hidden
states. Its dedicated relation feeds the comparison root to both post-message signer continuations.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem RootHiddenCacheRel.update_targets
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : SplitHashCache}
    (hrel : RootHiddenCacheRel target leftOutput rightOutput left right) :
    RootHiddenCacheRel target leftOutput rightOutput
      (Function.update left (.hidden (.position target)) (some leftOutput))
      (Function.update right (.hidden (.position target)) (some rightOutput)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro input
    simp [hrel.ordinary input]
  · simp
  · simp
  · intro coordinate hne
    have hkey : SplitHashKey.hidden coordinate ≠ .hidden (.position target) := by
      intro heq
      exact hne (SplitHashKey.hidden.inj heq)
    simp [Function.update_of_ne hkey, hrel.other_hidden coordinate hne]

def RootHiddenTargetRevealRel
    (target : Position) (leftOutput rightOutput : HashOutput) :
    Option (CleanRunResult (Digest × SplitHashCache)) →
      Option (CleanRunResult (Digest × SplitHashCache)) → Prop
  | some left, some right =>
      RootHiddenStateRel target leftOutput rightOutput left.state right.state ∧
        left.remaining = right.remaining ∧ left.table = right.table ∧
        left.value.1 = truncateHash leftOutput ∧
        right.value.1 = truncateHash rightOutput ∧
        RootHiddenCacheRel target leftOutput rightOutput left.value.2 right.value.2
  | none, none => True
  | _, _ => False

theorem relTriple_rootHidden_revealPosition_target
    (target : Position) (leftOutput rightOutput : HashOutput)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (hstate : RootHiddenStateRel target leftOutput rightOutput leftState rightState)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target leftOutput rightOutput leftCache rightCache) :
    RelTriple
      (runCleanFromTable leftState fuel table ((revealPosition target).run leftCache))
      (runCleanFromTable rightState fuel table ((revealPosition target).run rightCache))
      (RootHiddenTargetRevealRel target leftOutput rightOutput) := by
  rw [revealPosition_run, revealPosition_run, LazyRevealProbe.revealQuery,
    runCleanFromTable_reveal_query_bind, runCleanFromTable_reveal_query_bind,
    hstate.left_target, hstate.right_target]
  simp only [runCleanFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl, rfl, hcache.update_targets⟩

theorem rootHiddenRelates_sequenceFin
    (target : Position) (leftOutput rightOutput : HashOutput) {n : Nat}
    (left right : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index,
      RootHiddenRelates target leftOutput rightOutput (left index) (right index)) :
    RootHiddenRelates target leftOutput rightOutput
      (sequenceFin left) (sequenceFin right) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact rootHiddenRelates_pure target leftOutput rightOutput Fin.elim0
  | succ n ih =>
      rw [sequenceFin, sequenceFin]
      exact (hcomponent 0).bind fun leftHead rightHead hhead =>
        (ih (fun index : Fin n => left index.succ) (fun index : Fin n => right index.succ)
          (fun index => hcomponent index.succ)).bind fun leftTail rightTail htail => by
            subst rightHead
            subst rightTail
            exact rootHiddenRelates_pure target leftOutput rightOutput
              (Fin.cases leftHead leftTail : Fin (n + 1) → α)

theorem rootHiddenRelates_ensureFullChain
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    RootHiddenRelates target leftOutput rightOutput
      (ensureFullChain lay tree leafIdx chainIdx)
      (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (rootHiddenRelates_sequenceFin target leftOutput rightOutput _ _
    (fun step => rootHiddenRelates_ensureCoordinate target leftOutput rightOutput
      (.position (.chain lay tree leafIdx chainIdx step)))).bind fun _ _ _ =>
        rootHiddenRelates_pure target leftOutput rightOutput ()

theorem rootHiddenRelates_ensureOtsLeaf
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    RootHiddenRelates target leftOutput rightOutput
      (ensureOtsLeaf lay tree leafIdx) (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (rootHiddenRelates_sequenceFin target leftOutput rightOutput _ _
    (fun chainIdx => rootHiddenRelates_ensureFullChain target leftOutput rightOutput
      lay tree leafIdx chainIdx)).bind fun _ _ _ =>
        rootHiddenRelates_ensureCoordinate target leftOutput rightOutput
          (.position (.leaf lay tree leafIdx))

theorem rootHiddenRelates_ensureTreeNode
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex) : ∀ level nodeIdx,
    RootHiddenRelates target leftOutput rightOutput
      (ensureTreeNode lay tree level nodeIdx)
      (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => by
      rw [ensureTreeNode]
      exact rootHiddenRelates_ensureOtsLeaf target leftOutput rightOutput lay tree
        (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (rootHiddenRelates_ensureTreeNode target leftOutput rightOutput lay tree level
        (2 * nodeIdx)).bind fun _ _ _ =>
          (rootHiddenRelates_ensureTreeNode target leftOutput rightOutput lay tree level
            (2 * nodeIdx + 1)).bind fun _ _ _ => by
              by_cases hlevel : level < maxLayerHeight
              · rw [dif_pos hlevel]
                exact rootHiddenRelates_ensureCoordinate target leftOutput rightOutput
                  (.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)))
              · rw [dif_neg hlevel]
                exact rootHiddenRelates_pure target leftOutput rightOutput ()

theorem rootHiddenRelates_ensureChainPrefix
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) :
    RootHiddenRelates target leftOutput rightOutput
      (ensureChainPrefix lay tree leafIdx chainIdx digit)
      (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (rootHiddenRelates_sequenceFin target leftOutput rightOutput _ _
    (fun step => by
      by_cases hstep : step.val < digit.val
      · rw [if_pos hstep]
        exact rootHiddenRelates_ensureCoordinate target leftOutput rightOutput
          (.position (.chain lay tree leafIdx chainIdx step))
      · rw [if_neg hstep]
        exact rootHiddenRelates_pure target leftOutput rightOutput ())).bind fun _ _ _ =>
          rootHiddenRelates_pure target leftOutput rightOutput ()

theorem rootHiddenRelates_ensureTreePath
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    RootHiddenRelates target leftOutput rightOutput
      (ensureTreePath lay tree leafIdx) (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (rootHiddenRelates_sequenceFin target leftOutput rightOutput _ _
    (fun level => by
      by_cases hlevel : level.val < layerHeight lay
      · rw [if_pos hlevel]
        exact rootHiddenRelates_ensureTreeNode target leftOutput rightOutput lay tree
          level.val (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
      · rw [if_neg hlevel]
        exact rootHiddenRelates_pure target leftOutput rightOutput ())).bind fun _ _ _ =>
          rootHiddenRelates_pure target leftOutput rightOutput ()

theorem rootHiddenRelates_simulateQ
    {spec : OracleSpec ι}
    (target : Position) (leftOutput rightOutput : HashOutput)
    (leftImpl rightImpl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (himpl : ∀ query,
      RootHiddenRelates target leftOutput rightOutput
        (leftImpl query) (rightImpl query))
    (computation : OracleComp spec α) :
    RootHiddenRelates target leftOutput rightOutput
      (simulateQ leftImpl computation) (simulateQ rightImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      rw [simulateQ_pure, simulateQ_pure]
      exact rootHiddenRelates_pure target leftOutput rightOutput value
  | query_bind query next ih =>
      rw [simulateQ_query_bind, simulateQ_query_bind]
      exact (himpl query).bind fun leftValue rightValue hvalue => by
        subst rightValue
        exact ih leftValue

theorem rootHiddenRelates_ordinaryHashImpl
    (target : Position) (leftOutput rightOutput : HashOutput)
    (input : HashInput) :
    RootHiddenRelates target leftOutput rightOutput
      (ordinaryHashImpl input) (ordinaryHashImpl input) :=
  rootHiddenRelates_splitHashQuery_ordinary target leftOutput rightOutput input

theorem rootHiddenRelates_maskedOtsSignFrom
    (target : Position) (leftOutput rightOutput : HashOutput)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) : ∀ attempts counter,
    RootHiddenRelates target leftOutput rightOutput
      (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
      (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => by
      rw [maskedOtsSignFrom]
      exact rootHiddenRelates_pure target leftOutput rightOutput none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      apply (rootHiddenRelates_simulateQ target leftOutput rightOutput
        ordinaryHashImpl ordinaryHashImpl
        (rootHiddenRelates_ordinaryHashImpl target leftOutput rightOutput)
        (encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))).bind
      intro leftEncoded rightEncoded hencoded
      subst rightEncoded
      cases leftEncoded with
      | none =>
          exact rootHiddenRelates_maskedOtsSignFrom target leftOutput rightOutput parameter
            lay tree leafIdx message attempts (counter + 1)
      | some encoding =>
          exact (rootHiddenRelates_sequenceFin target leftOutput rightOutput _ _
            (fun chainIdx => rootHiddenRelates_ensureChainPrefix target leftOutput rightOutput
              lay tree leafIdx chainIdx (encoding chainIdx))).bind fun _ _ _ =>
                rootHiddenRelates_pure target leftOutput rightOutput
                  (some (BitVec.ofNat counterBits counter, encoding))

theorem rootHiddenRelates_maskedOtsSign
    (target : Position) (leftOutput rightOutput : HashOutput)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) :
    RootHiddenRelates target leftOutput rightOutput
      (maskedOtsSign parameter lay tree leafIdx message)
      (maskedOtsSign parameter lay tree leafIdx message) :=
  rootHiddenRelates_maskedOtsSignFrom target leftOutput rightOutput parameter lay tree leafIdx
    message encodingAttemptLimit 0

theorem rootHiddenRelates_maskedOtsLayerAfterMessage
    (target : Position) (leftOutput rightOutput : HashOutput)
    (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest) :
    RootHiddenRelates target leftOutput rightOutput
      (maskedOtsLayerAfterMessage parameter index lay message)
      (maskedOtsLayerAfterMessage parameter index lay message) := by
  unfold maskedOtsLayerAfterMessage
  apply (rootHiddenRelates_maskedOtsSign target leftOutput rightOutput parameter lay
    (treeIndexAt index lay) (leafIndexAt index lay) message).bind
  intro leftResult rightResult hresult
  subst rightResult
  cases leftResult with
  | none => exact rootHiddenRelates_pure target leftOutput rightOutput none
  | some part =>
      exact (rootHiddenRelates_ensureTreePath target leftOutput rightOutput lay
        (treeIndexAt index lay) (leafIndexAt index lay)).bind fun _ _ _ =>
          rootHiddenRelates_pure target leftOutput rightOutput (some part)

theorem maskedTreeRoot_eq_ensure_reveal (lay : Layer) (tree : TreeIndex) :
    maskedTreeRoot lay tree = (do
      ensureTreeNode lay tree (layerHeight lay) 0
      revealPosition (layerRootPosition lay tree)) := by
  fin_cases lay <;>
    simp [maskedTreeRoot, maskedTreeNode, layerRootPosition, layerHeight,
      maxLayerHeight, leafOfNat] <;> congr 1

theorem relTriple_rootHidden_maskedTreeRoot_target
    (lay : Layer) (tree : TreeIndex)
    (leftOutput rightOutput : HashOutput)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (hstate : RootHiddenStateRel (layerRootPosition lay tree) leftOutput rightOutput
      leftState rightState)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel (layerRootPosition lay tree) leftOutput rightOutput
      leftCache rightCache) :
    RelTriple
      (runCleanFromTable leftState fuel table ((maskedTreeRoot lay tree).run leftCache))
      (runCleanFromTable rightState fuel table ((maskedTreeRoot lay tree).run rightCache))
      (RootHiddenTargetRevealRel (layerRootPosition lay tree) leftOutput rightOutput) := by
  rw [maskedTreeRoot_eq_ensure_reveal, StateT.run_bind, StateT.run_bind,
    runCleanFromTable_bind, runCleanFromTable_bind]
  apply relTriple_bind
    (rootHiddenRelates_ensureTreeNode (layerRootPosition lay tree) leftOutput rightOutput
      lay tree (layerHeight lay) 0 leftState rightState hstate fuel table leftCache rightCache
        hcache)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [RootHiddenCleanSameRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [RootHiddenCleanSameRel] at hresult
      | some rightResult =>
          rcases hresult with ⟨hnextState, hremaining, htable, _hvalue, hnextCache⟩
          simp only
          rw [← hremaining, ← htable]
          exact relTriple_rootHidden_revealPosition_target (layerRootPosition lay tree)
            leftOutput rightOutput leftResult.state rightResult.state hnextState
              leftResult.remaining leftResult.table leftResult.value.2 rightResult.value.2
                hnextCache

theorem relTriple_rootHidden_maskedLayerMessage_target
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (index : Index) (lay : Layer)
    (htarget : layerMessagePosition index lay = target)
    (leftOutput rightOutput : HashOutput)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (hstate : RootHiddenStateRel target leftOutput rightOutput leftState rightState)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target leftOutput rightOutput leftCache rightCache) :
    RelTriple
      (runCleanFromTable leftState fuel table
        ((maskedLayerMessage parameter ftsSecret index lay).run leftCache))
      (runCleanFromTable rightState fuel table
        ((maskedLayerMessage parameter ftsSecret index lay).run rightCache))
      (RootHiddenTargetRevealRel target leftOutput rightOutput) := by
  obtain ⟨below, hcomputation, hposition⟩ :=
    layerMessage_root_witness_of_isLayerRoot parameter ftsSecret target hroot index lay htarget
  have htargetRoot : target = layerRootPosition below (treeIndexAt index below) :=
    htarget.symm.trans hposition
  rw [hcomputation]
  rw [htargetRoot] at hstate hcache ⊢
  exact relTriple_rootHidden_maskedTreeRoot_target below (treeIndexAt index below)
    leftOutput rightOutput leftState rightState hstate fuel table leftCache rightCache hcache

theorem rootHiddenRelates_maskedSignLayer_comparison_actual
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (index : Index) (lay : Layer)
    (htarget : layerMessagePosition index lay = target)
    (leftOutput rightOutput : HashOutput) :
    RootHiddenRelates target leftOutput rightOutput
      (maskedSignLayerWithComparisonRoot parameter ftsSecret index lay
        (truncateHash rightOutput))
      (maskedSignLayer parameter ftsSecret index lay) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  unfold maskedSignLayerWithComparisonRoot maskedSignLayer
  rw [StateT.run_bind, StateT.run_bind, runCleanFromTable_bind,
    runCleanFromTable_bind]
  apply relTriple_bind
    (relTriple_rootHidden_maskedLayerMessage_target parameter ftsSecret target hroot index lay
      htarget leftOutput rightOutput leftState rightState hstate fuel table leftCache rightCache
        hcache)
  intro leftMessage rightMessage hmessage
  cases leftMessage with
  | none =>
      cases rightMessage with
      | none => exact relTriple_pure_pure trivial
      | some rightMessage => simp [RootHiddenTargetRevealRel] at hmessage
  | some leftMessage =>
      cases rightMessage with
      | none => simp [RootHiddenTargetRevealRel] at hmessage
      | some rightMessage =>
          rcases hmessage with ⟨hnextState, hremaining, htable, _hleftMessage,
            hrightMessage, hnextCache⟩
          simp only
          rw [← hremaining, ← htable, hrightMessage]
          exact rootHiddenRelates_maskedOtsLayerAfterMessage target leftOutput rightOutput
            parameter index lay (truncateHash rightOutput) leftMessage.state rightMessage.state
              hnextState leftMessage.remaining leftMessage.table leftMessage.value.2
                rightMessage.value.2 hnextCache

theorem rootHiddenRelates_maskedTreeRoot_of_ne
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex)
    (hne : layerRootPosition lay tree ≠ target) :
    RootHiddenRelates target leftOutput rightOutput
      (maskedTreeRoot lay tree) (maskedTreeRoot lay tree) := by
  rw [maskedTreeRoot_eq_ensure_reveal]
  exact (rootHiddenRelates_ensureTreeNode target leftOutput rightOutput lay tree
    (layerHeight lay) 0).bind fun _ _ _ =>
      rootHiddenRelates_revealPosition_of_ne target leftOutput rightOutput
        (layerRootPosition lay tree) hne

theorem rootHiddenRelates_maskedLayerMessage_of_ne
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (index : Index) (lay : Layer)
    (hne : layerMessagePosition index lay ≠ target) :
    RootHiddenRelates target leftOutput rightOutput
      (maskedLayerMessage parameter ftsSecret index lay)
      (maskedLayerMessage parameter ftsSecret index lay) := by
  fin_cases lay
  · rw [maskedLayerMessage, dif_pos (by decide)]
    apply rootHiddenRelates_maskedTreeRoot_of_ne
    simpa [layerMessagePosition_top, layerRootPosition]
  · rw [maskedLayerMessage, dif_pos (by decide)]
    apply rootHiddenRelates_maskedTreeRoot_of_ne
    simpa [layerMessagePosition_middle, layerRootPosition]
  · rw [maskedLayerMessage, dif_neg (by decide)]
    exact rootHiddenRelates_simulateQ target leftOutput rightOutput ordinaryHashImpl
      ordinaryHashImpl (rootHiddenRelates_ordinaryHashImpl target leftOutput rightOutput)
        (ftsKey parameter index (ftsSecret index))

theorem rootHiddenRelates_maskedSignLayer_of_ne
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (index : Index) (lay : Layer)
    (hne : layerMessagePosition index lay ≠ target) :
    RootHiddenRelates target leftOutput rightOutput
      (maskedSignLayer parameter ftsSecret index lay)
      (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (rootHiddenRelates_maskedLayerMessage_of_ne parameter ftsSecret target leftOutput
    rightOutput index lay hne).bind fun leftMessage rightMessage hmessage => by
      subst rightMessage
      exact rootHiddenRelates_maskedOtsLayerAfterMessage target leftOutput rightOutput
        parameter index lay leftMessage

theorem rootHiddenRelates_maskedSignLayerWithTargetComparison_actual
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput)
    (index : Index) (lay : Layer) :
    RootHiddenRelates target leftOutput rightOutput
      (maskedSignLayerWithTargetComparison parameter target (truncateHash rightOutput)
        ftsSecret index lay)
      (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayerWithTargetComparison
  by_cases htarget : layerMessagePosition index lay = target
  · rw [if_pos htarget]
    exact rootHiddenRelates_maskedSignLayer_comparison_actual parameter ftsSecret target hroot
      index lay htarget leftOutput rightOutput
  · rw [if_neg htarget]
    exact rootHiddenRelates_maskedSignLayer_of_ne parameter ftsSecret target leftOutput
      rightOutput index lay htarget

theorem rootHiddenRelates_maskedSignLayersWithTargetComparison_actual
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput) (index : Index) :
    RootHiddenRelates target leftOutput rightOutput
      (maskedSignLayersWithTargetComparison parameter target (truncateHash rightOutput)
        ftsSecret index)
      (sequenceFin fun lay => maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayersWithTargetComparison
  exact rootHiddenRelates_sequenceFin target leftOutput rightOutput _ _ fun lay =>
    rootHiddenRelates_maskedSignLayerWithTargetComparison_actual parameter ftsSecret target
      hroot leftOutput rightOutput index lay

theorem chainValueCoordinate_ne_layerRoot
    {target : Position} (hroot : IsLayerRoot target)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) :
    chainValueCoordinate lay tree leafIdx chainIdx digit ≠ .position target := by
  obtain ⟨rootLay, rootTree, rfl⟩ := hroot
  unfold chainValueCoordinate
  split <;> simp [layerRootPosition]

theorem pathNode_ne_layerRoot
    {target : Position} (hroot : IsLayerRoot target)
    (lay : Layer) (tree : TreeIndex) (current : Nat)
    (hcurrent : current < maxLayerHeight) (nodeIdx : LeafIndex)
    (hlt : current + 1 < layerHeight lay) :
    Position.node lay tree ⟨current, hcurrent⟩ nodeIdx ≠ target := by
  obtain ⟨rootLay, rootTree, rfl⟩ := hroot
  intro heq
  simp only [layerRootPosition, Position.node.injEq] at heq
  have hlay : lay = rootLay := heq.1
  subst rootLay
  have hlevel := congrArg Fin.val heq.2.2.1
  simp only at hlevel
  have hpos : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  have hmax : 0 < maxLayerHeight := by norm_num [maxLayerHeight]
  omega

theorem rootHiddenRelates_revealLayerValues
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput)
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    RootHiddenRelates target leftOutput rightOutput
      (revealLayerValues index lay encoding) (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  apply (rootHiddenRelates_sequenceFin target leftOutput rightOutput _ _ fun chainIdx =>
    rootHiddenRelates_revealPublishedCoordinate_of_ne target leftOutput rightOutput
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
        (encoding chainIdx))
      (chainValueCoordinate_ne_layerRoot hroot lay (treeIndexAt index lay)
        (leafIndexAt index lay) chainIdx (encoding chainIdx))).bind
  intro leftValues rightValues hvalues
  subst rightValues
  apply (rootHiddenRelates_sequenceFin target leftOutput rightOutput _ _ fun level => by
    by_cases hlevel : level.val < layerHeight lay
    · rw [if_pos hlevel]
      cases hzero : level.val with
      | zero =>
          exact rootHiddenRelates_revealPublishedCoordinate_of_ne target leftOutput rightOutput
            (.position (.leaf lay (treeIndexAt index lay)
              (leafOfNat (Nat.xor (leafIndexAt index lay).val 1)))) (by
                obtain ⟨rootLay, rootTree, rfl⟩ := hroot
                simp [layerRootPosition])
      | succ current =>
          rw [Nat.add_one]
          simp only
          by_cases hcurrent : current < maxLayerHeight
          · rw [dif_pos hcurrent]
            exact rootHiddenRelates_revealPublishedCoordinate_of_ne target leftOutput rightOutput
              (.position (.node lay (treeIndexAt index lay) ⟨current, hcurrent⟩
                (leafOfNat (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
              (by
                intro heq
                exact (pathNode_ne_layerRoot hroot lay (treeIndexAt index lay) current hcurrent _
                  (by omega)) (Coordinate.position.inj heq))
          · rw [dif_neg hcurrent]
            exact rootHiddenRelates_pure target leftOutput rightOutput 0
    · rw [if_neg hlevel]
      exact rootHiddenRelates_pure target leftOutput rightOutput 0).bind
  intro leftPath rightPath hpath
  subst rightPath
  exact rootHiddenRelates_pure target leftOutput rightOutput (leftValues, leftPath)

theorem rootHiddenRelates_maskedSignAfterDigestWithTargetComparison_actual
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    RootHiddenRelates target leftOutput rightOutput
      (maskedSignAfterDigestWithTargetComparison parameter target (truncateHash rightOutput)
        ftsSecret randomness index leaves)
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigestWithTargetComparison maskedSignAfterDigest
  apply (rootHiddenRelates_simulateQ target leftOutput rightOutput ordinaryHashImpl
    ordinaryHashImpl (rootHiddenRelates_ordinaryHashImpl target leftOutput rightOutput)
      (ftsOpen parameter index leaves (ftsSecret index))).bind
  intro leftPath rightPath hpath
  subst rightPath
  apply (rootHiddenRelates_maskedSignLayersWithTargetComparison_actual parameter ftsSecret
    target hroot leftOutput rightOutput index).bind
  intro leftLayers rightLayers hlayers
  subst rightLayers
  cases hparts : traverseOption leftLayers with
  | none => exact rootHiddenRelates_pure target leftOutput rightOutput none
  | some parts =>
      apply (rootHiddenRelates_sequenceFin target leftOutput rightOutput _ _ fun lay =>
        rootHiddenRelates_revealLayerValues target hroot leftOutput rightOutput index lay
          (parts lay).2).bind
      intro leftRevealed rightRevealed hrevealed
      subst rightRevealed
      let signature : Signature :=
        { randomness := randomness
          ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := leftPath
          counter := fun lay => (parts lay).1
          chainValue := fun lay => (leftRevealed lay).1
          authPath := flattenPaths fun lay => (leftRevealed lay).2 }
      exact rootHiddenRelates_pure target leftOutput rightOutput (some signature)

theorem rootHiddenRelates_ordinaryRomImpl
    (target : Position) (leftOutput rightOutput : HashOutput)
    (query : OracleWorld.Domain) :
    RootHiddenRelates target leftOutput rightOutput
      (ordinaryRomImpl query) (ordinaryRomImpl query) := by
  cases query with
  | inl n => exact rootHiddenRelates_splitUniformImpl target leftOutput rightOutput n
  | inr input => exact rootHiddenRelates_ordinaryHashImpl target leftOutput rightOutput input

theorem rootHiddenRelates_maskedSignWithTargetComparison_actual
    (parameter : PublicParameter) (publicRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput) (message : Message) :
    RootHiddenRelates target leftOutput rightOutput
      (maskedSignWithTargetComparison parameter publicRoot target (truncateHash rightOutput)
        ftsSecret message)
      (maskedSign parameter publicRoot ftsSecret message) := by
  unfold maskedSignWithTargetComparison maskedSign
  let secretKey : SecretKey :=
    ⟨parameter, publicRoot, fun _ _ _ _ => 0, ftsSecret⟩
  apply (rootHiddenRelates_simulateQ target leftOutput rightOutput ordinaryRomImpl
    ordinaryRomImpl (rootHiddenRelates_ordinaryRomImpl target leftOutput rightOutput)
      (signDigestLoop digestAttemptLimit secretKey message)).bind
  intro leftSelected rightSelected hselected
  subst rightSelected
  cases leftSelected with
  | none => exact rootHiddenRelates_pure target leftOutput rightOutput none
  | some selected =>
      exact rootHiddenRelates_maskedSignAfterDigestWithTargetComparison_actual parameter
        ftsSecret target hroot leftOutput rightOutput selected.1 selected.2.1 selected.2.2

noncomputable def fullSwapRootCache
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (rightOutput : HashOutput)
    (cache : SplitHashCache) : SplitHashCache :=
  replaceHiddenRootCache target rightOutput
    (swapCanonicalRootEncodingCache parameter target leftRoot rightRoot cache)

theorem rootHiddenCacheRel_fullSwapRootCache
    (parameter : PublicParameter) (target : Position)
    (leftOutput rightOutput : HashOutput) (cache : SplitHashCache)
    (hleft : cache (.hidden (.position target)) = some leftOutput) :
    RootHiddenCacheRel target leftOutput rightOutput
      (swapCanonicalRootEncodingCache parameter target (truncateHash leftOutput)
        (truncateHash rightOutput) cache)
      (fullSwapRootCache parameter target (truncateHash leftOutput)
        (truncateHash rightOutput) rightOutput cache) := by
  apply rootHiddenCacheRel_replace
  exact hleft

theorem evalDist_swappedRoot_maskedSign_eq
    (parameter : PublicParameter) (publicRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (hprivate : Coordinate.position target ∉ state.revealed)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache)
    (hhidden : cache (.hidden (.position target)) = some leftOutput)
    (message : Message) :
    evalDist (cleanRunReturnedValue? <$>
        runCleanFromTable (state.materialize (.position target) leftOutput) fuel table
          ((maskedSign parameter publicRoot ftsSecret message).run cache)) =
      evalDist (cleanRunReturnedValue? <$>
        runCleanFromTable (state.materialize (.position target) rightOutput) fuel table
          ((maskedSign parameter publicRoot ftsSecret message).run
            (fullSwapRootCache parameter target (truncateHash leftOutput)
              (truncateHash rightOutput) rightOutput cache))) := by
  let comparisonCache := swapCanonicalRootEncodingCache parameter target
    (truncateHash leftOutput) (truncateHash rightOutput) cache
  let rightCache := fullSwapRootCache parameter target
    (truncateHash leftOutput) (truncateHash rightOutput) rightOutput cache
  have hstored : StoredLayerRoot
      (state.materialize (.position target) leftOutput) target (truncateHash leftOutput) := by
    refine ⟨leftOutput, ?_, rfl⟩
    simp [LazyRevealProbe.State.materialize]
  have hencoding := rootEncodingCacheRel_swapCanonical parameter target
    (truncateHash leftOutput) (truncateHash rightOutput) cache
  have hab := evalDist_cleanRunReturnedValue_eq_of_rootEncodingStored
    (rootEncodingCacheRelatesStored_maskedSign_targetComparison parameter publicRoot target hroot
      (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret message)
    cache comparisonCache hencoding
    (state.materialize (.position target) leftOutput) fuel table hstored
  have hstate := rootHiddenStateRel_materialize target leftOutput rightOutput state hprivate
  have hcache : RootHiddenCacheRel target leftOutput rightOutput comparisonCache rightCache := by
    exact rootHiddenCacheRel_fullSwapRootCache parameter target leftOutput rightOutput cache hhidden
  have hbc := evalDist_cleanRunReturnedValue_eq_of_rootHidden
    (rootHiddenRelates_maskedSignWithTargetComparison_actual parameter publicRoot ftsSecret
      target hroot leftOutput rightOutput message)
    (state.materialize (.position target) leftOutput)
    (state.materialize (.position target) rightOutput) hstate fuel table
    comparisonCache rightCache hcache
  exact hab.trans hbc

end SphincsSecurity.Concrete.OtsProbeSimulation
