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

end SphincsSecurity.Concrete.OtsProbeSimulation
