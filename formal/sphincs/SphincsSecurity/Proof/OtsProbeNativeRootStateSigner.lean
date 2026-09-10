import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootStateCoupling
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootStateSigner

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem nativeRootRelates_sequenceFin
    (target : Position) (leftOutput rightOutput : HashOutput) {n : Nat}
    (left right : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index,
      NativeRootRelates target leftOutput rightOutput (left index) (right index)) :
    NativeRootRelates target leftOutput rightOutput
      (sequenceFin left) (sequenceFin right) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact nativeRootRelates_pure target leftOutput rightOutput Fin.elim0
  | succ n ih =>
      rw [sequenceFin, sequenceFin]
      exact (hcomponent 0).bind fun leftHead rightHead hhead =>
        (ih (fun index : Fin n => left index.succ) (fun index : Fin n => right index.succ)
          (fun index => hcomponent index.succ)).bind fun leftTail rightTail htail => by
            subst rightHead
            subst rightTail
            exact nativeRootRelates_pure target leftOutput rightOutput
              (Fin.cases leftHead leftTail : Fin (n + 1) → α)

theorem nativeRootRelates_ensureFullChain
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    NativeRootRelates target leftOutput rightOutput
      (ensureFullChain lay tree leafIdx chainIdx)
      (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (nativeRootRelates_sequenceFin target leftOutput rightOutput _ _
    (fun step => nativeRootRelates_ensureCoordinate target leftOutput rightOutput
      (.position (.chain lay tree leafIdx chainIdx step)))).bind fun _ _ _ =>
        nativeRootRelates_pure target leftOutput rightOutput ()

theorem nativeRootRelates_ensureOtsLeaf
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    NativeRootRelates target leftOutput rightOutput
      (ensureOtsLeaf lay tree leafIdx) (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (nativeRootRelates_sequenceFin target leftOutput rightOutput _ _
    (fun chainIdx => nativeRootRelates_ensureFullChain target leftOutput rightOutput
      lay tree leafIdx chainIdx)).bind fun _ _ _ =>
        nativeRootRelates_ensureCoordinate target leftOutput rightOutput
          (.position (.leaf lay tree leafIdx))

theorem nativeRootRelates_ensureTreeNode
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex) : ∀ level nodeIdx,
    NativeRootRelates target leftOutput rightOutput
      (ensureTreeNode lay tree level nodeIdx)
      (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => by
      rw [ensureTreeNode]
      exact nativeRootRelates_ensureOtsLeaf target leftOutput rightOutput lay tree
        (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (nativeRootRelates_ensureTreeNode target leftOutput rightOutput lay tree level
        (2 * nodeIdx)).bind fun _ _ _ =>
          (nativeRootRelates_ensureTreeNode target leftOutput rightOutput lay tree level
            (2 * nodeIdx + 1)).bind fun _ _ _ => by
              by_cases hlevel : level < maxLayerHeight
              · rw [dif_pos hlevel]
                exact nativeRootRelates_ensureCoordinate target leftOutput rightOutput
                  (.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)))
              · rw [dif_neg hlevel]
                exact nativeRootRelates_pure target leftOutput rightOutput ()

theorem nativeRootRelates_ensureChainPrefix
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) :
    NativeRootRelates target leftOutput rightOutput
      (ensureChainPrefix lay tree leafIdx chainIdx digit)
      (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (nativeRootRelates_sequenceFin target leftOutput rightOutput _ _
    (fun step => by
      by_cases hstep : step.val < digit.val
      · rw [if_pos hstep]
        exact nativeRootRelates_ensureCoordinate target leftOutput rightOutput
          (.position (.chain lay tree leafIdx chainIdx step))
      · rw [if_neg hstep]
        exact nativeRootRelates_pure target leftOutput rightOutput ())).bind fun _ _ _ =>
          nativeRootRelates_pure target leftOutput rightOutput ()

theorem nativeRootRelates_ensureTreePath
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    NativeRootRelates target leftOutput rightOutput
      (ensureTreePath lay tree leafIdx) (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (nativeRootRelates_sequenceFin target leftOutput rightOutput _ _
    (fun level => by
      by_cases hlevel : level.val < layerHeight lay
      · rw [if_pos hlevel]
        exact nativeRootRelates_ensureTreeNode target leftOutput rightOutput lay tree
          level.val (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
      · rw [if_neg hlevel]
        exact nativeRootRelates_pure target leftOutput rightOutput ())).bind fun _ _ _ =>
          nativeRootRelates_pure target leftOutput rightOutput ()

theorem nativeRootRelates_simulateQ
    {spec : OracleSpec ι}
    (target : Position) (leftOutput rightOutput : HashOutput)
    (leftImpl rightImpl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (himpl : ∀ query,
      NativeRootRelates target leftOutput rightOutput
        (leftImpl query) (rightImpl query))
    (computation : OracleComp spec α) :
    NativeRootRelates target leftOutput rightOutput
      (simulateQ leftImpl computation) (simulateQ rightImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      rw [simulateQ_pure, simulateQ_pure]
      exact nativeRootRelates_pure target leftOutput rightOutput value
  | query_bind query next ih =>
      rw [simulateQ_query_bind, simulateQ_query_bind]
      exact (himpl query).bind fun leftValue rightValue hvalue => by
        subst rightValue
        exact ih leftValue

theorem nativeRootRelates_ordinaryHashImpl
    (target : Position) (leftOutput rightOutput : HashOutput)
    (input : HashInput) :
    NativeRootRelates target leftOutput rightOutput
      (ordinaryHashImpl input) (ordinaryHashImpl input) :=
  nativeRootRelates_splitHashQuery_ordinary target leftOutput rightOutput input

theorem nativeRootRelates_maskedOtsSignFrom
    (target : Position) (leftOutput rightOutput : HashOutput)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) : ∀ attempts counter,
    NativeRootRelates target leftOutput rightOutput
      (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
      (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => by
      rw [maskedOtsSignFrom]
      exact nativeRootRelates_pure target leftOutput rightOutput none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      apply (nativeRootRelates_simulateQ target leftOutput rightOutput
        ordinaryHashImpl ordinaryHashImpl
        (nativeRootRelates_ordinaryHashImpl target leftOutput rightOutput)
        (encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))).bind
      intro leftEncoded rightEncoded hencoded
      subst rightEncoded
      cases leftEncoded with
      | none =>
          exact nativeRootRelates_maskedOtsSignFrom target leftOutput rightOutput parameter
            lay tree leafIdx message attempts (counter + 1)
      | some encoding =>
          exact (nativeRootRelates_sequenceFin target leftOutput rightOutput _ _
            (fun chainIdx => nativeRootRelates_ensureChainPrefix target leftOutput rightOutput
              lay tree leafIdx chainIdx (encoding chainIdx))).bind fun _ _ _ =>
                nativeRootRelates_pure target leftOutput rightOutput
                  (some (BitVec.ofNat counterBits counter, encoding))

theorem nativeRootRelates_maskedOtsSign
    (target : Position) (leftOutput rightOutput : HashOutput)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) :
    NativeRootRelates target leftOutput rightOutput
      (maskedOtsSign parameter lay tree leafIdx message)
      (maskedOtsSign parameter lay tree leafIdx message) :=
  nativeRootRelates_maskedOtsSignFrom target leftOutput rightOutput parameter lay tree leafIdx
    message encodingAttemptLimit 0

theorem nativeRootRelates_maskedOtsLayerAfterMessage
    (target : Position) (leftOutput rightOutput : HashOutput)
    (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest) :
    NativeRootRelates target leftOutput rightOutput
      (maskedOtsLayerAfterMessage parameter index lay message)
      (maskedOtsLayerAfterMessage parameter index lay message) := by
  unfold maskedOtsLayerAfterMessage
  apply (nativeRootRelates_maskedOtsSign target leftOutput rightOutput parameter lay
    (treeIndexAt index lay) (leafIndexAt index lay) message).bind
  intro leftResult rightResult hresult
  subst rightResult
  cases leftResult with
  | none => exact nativeRootRelates_pure target leftOutput rightOutput none
  | some part =>
      exact (nativeRootRelates_ensureTreePath target leftOutput rightOutput lay
        (treeIndexAt index lay) (leafIndexAt index lay)).bind fun _ _ _ =>
          nativeRootRelates_pure target leftOutput rightOutput (some part)

theorem relTriple_nativeRoot_maskedTreeRoot_target
    (lay : Layer) (tree : TreeIndex)
    (leftOutput rightOutput : HashOutput)
    (leftState rightState : DeferredContext)
    (hstate : NativeRootContextRel (layerRootPosition lay tree) leftOutput rightOutput
      leftState rightState)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel (layerRootPosition lay tree) leftOutput rightOutput
      leftCache rightCache) :
    RelTriple
      (runResolvedFromTable leftState fuel table ((maskedTreeRoot lay tree).run leftCache))
      (runResolvedFromTable rightState fuel table ((maskedTreeRoot lay tree).run rightCache))
      (NativeRootTargetRevealRel (layerRootPosition lay tree) leftOutput rightOutput) := by
  rw [maskedTreeRoot_eq_ensure_reveal, StateT.run_bind, StateT.run_bind,
    runResolvedFromTable_bind, runResolvedFromTable_bind]
  apply relTriple_bind
    (nativeRootRelates_ensureTreeNode (layerRootPosition lay tree) leftOutput rightOutput
      lay tree (layerHeight lay) 0 leftState rightState hstate fuel table leftCache rightCache
        hcache)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [NativeRootSameRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [NativeRootSameRel] at hresult
      | some rightResult =>
          rcases hresult with ⟨hnextState, hremaining, htable, _hvalue, hnextCache⟩
          simp only
          rw [← hremaining, ← htable]
          exact relTriple_nativeRoot_revealPosition_target (layerRootPosition lay tree)
            leftOutput rightOutput leftResult.context rightResult.context hnextState
              leftResult.remaining leftResult.table leftResult.value.2 rightResult.value.2
                hnextCache

theorem relTriple_nativeRoot_maskedLayerMessage_target
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (index : Index) (lay : Layer)
    (htarget : layerMessagePosition index lay = target)
    (leftOutput rightOutput : HashOutput)
    (leftState rightState : DeferredContext)
    (hstate : NativeRootContextRel target leftOutput rightOutput leftState rightState)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target leftOutput rightOutput leftCache rightCache) :
    RelTriple
      (runResolvedFromTable leftState fuel table
        ((maskedLayerMessage parameter ftsSecret index lay).run leftCache))
      (runResolvedFromTable rightState fuel table
        ((maskedLayerMessage parameter ftsSecret index lay).run rightCache))
      (NativeRootTargetRevealRel target leftOutput rightOutput) := by
  obtain ⟨below, hcomputation, hposition⟩ :=
    layerMessage_root_witness_of_isLayerRoot parameter ftsSecret target hroot index lay htarget
  have htargetRoot : target = layerRootPosition below (treeIndexAt index below) :=
    htarget.symm.trans hposition
  rw [hcomputation]
  rw [htargetRoot] at hstate hcache ⊢
  exact relTriple_nativeRoot_maskedTreeRoot_target below (treeIndexAt index below)
    leftOutput rightOutput leftState rightState hstate fuel table leftCache rightCache hcache

theorem nativeRootRelates_maskedSignLayer_comparison_actual
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (index : Index) (lay : Layer)
    (htarget : layerMessagePosition index lay = target)
    (leftOutput rightOutput : HashOutput) :
    NativeRootRelates target leftOutput rightOutput
      (maskedSignLayerWithComparisonRoot parameter ftsSecret index lay
        (truncateHash rightOutput))
      (maskedSignLayer parameter ftsSecret index lay) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  unfold maskedSignLayerWithComparisonRoot maskedSignLayer
  rw [StateT.run_bind, StateT.run_bind, runResolvedFromTable_bind,
    runResolvedFromTable_bind]
  apply relTriple_bind
    (relTriple_nativeRoot_maskedLayerMessage_target parameter ftsSecret target hroot index lay
      htarget leftOutput rightOutput leftState rightState hstate fuel table leftCache rightCache
        hcache)
  intro leftMessage rightMessage hmessage
  cases leftMessage with
  | none =>
      cases rightMessage with
      | none => exact relTriple_pure_pure trivial
      | some rightMessage => simp [NativeRootTargetRevealRel] at hmessage
  | some leftMessage =>
      cases rightMessage with
      | none => simp [NativeRootTargetRevealRel] at hmessage
      | some rightMessage =>
          rcases hmessage with ⟨hnextState, hremaining, htable, _hleftMessage,
            hrightMessage, hnextCache⟩
          simp only
          rw [← hremaining, ← htable, hrightMessage]
          exact nativeRootRelates_maskedOtsLayerAfterMessage target leftOutput rightOutput
            parameter index lay (truncateHash rightOutput) leftMessage.context rightMessage.context
              hnextState leftMessage.remaining leftMessage.table leftMessage.value.2
                rightMessage.value.2 hnextCache

theorem nativeRootRelates_maskedTreeRoot_of_ne
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex)
    (hne : layerRootPosition lay tree ≠ target) :
    NativeRootRelates target leftOutput rightOutput
      (maskedTreeRoot lay tree) (maskedTreeRoot lay tree) := by
  rw [maskedTreeRoot_eq_ensure_reveal]
  exact (nativeRootRelates_ensureTreeNode target leftOutput rightOutput lay tree
    (layerHeight lay) 0).bind fun _ _ _ =>
      nativeRootRelates_revealPosition_of_ne target leftOutput rightOutput
        (layerRootPosition lay tree) hne

theorem nativeRootRelates_maskedLayerMessage_of_ne
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (index : Index) (lay : Layer)
    (hne : layerMessagePosition index lay ≠ target) :
    NativeRootRelates target leftOutput rightOutput
      (maskedLayerMessage parameter ftsSecret index lay)
      (maskedLayerMessage parameter ftsSecret index lay) := by
  fin_cases lay
  · rw [maskedLayerMessage, dif_pos (by decide)]
    apply nativeRootRelates_maskedTreeRoot_of_ne
    simpa [layerMessagePosition_top, layerRootPosition]
  · rw [maskedLayerMessage, dif_pos (by decide)]
    apply nativeRootRelates_maskedTreeRoot_of_ne
    simpa [layerMessagePosition_middle, layerRootPosition]
  · rw [maskedLayerMessage, dif_neg (by decide)]
    exact nativeRootRelates_simulateQ target leftOutput rightOutput ordinaryHashImpl
      ordinaryHashImpl (nativeRootRelates_ordinaryHashImpl target leftOutput rightOutput)
        (ftsKey parameter index (ftsSecret index))

theorem nativeRootRelates_maskedSignLayer_of_ne
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (index : Index) (lay : Layer)
    (hne : layerMessagePosition index lay ≠ target) :
    NativeRootRelates target leftOutput rightOutput
      (maskedSignLayer parameter ftsSecret index lay)
      (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (nativeRootRelates_maskedLayerMessage_of_ne parameter ftsSecret target leftOutput
    rightOutput index lay hne).bind fun leftMessage rightMessage hmessage => by
      subst rightMessage
      exact nativeRootRelates_maskedOtsLayerAfterMessage target leftOutput rightOutput
        parameter index lay leftMessage

theorem nativeRootRelates_maskedSignLayerWithTargetComparison_actual
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput)
    (index : Index) (lay : Layer) :
    NativeRootRelates target leftOutput rightOutput
      (maskedSignLayerWithTargetComparison parameter target (truncateHash rightOutput)
        ftsSecret index lay)
      (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayerWithTargetComparison
  by_cases htarget : layerMessagePosition index lay = target
  · rw [if_pos htarget]
    exact nativeRootRelates_maskedSignLayer_comparison_actual parameter ftsSecret target hroot
      index lay htarget leftOutput rightOutput
  · rw [if_neg htarget]
    exact nativeRootRelates_maskedSignLayer_of_ne parameter ftsSecret target leftOutput
      rightOutput index lay htarget

theorem nativeRootRelates_revealLayerValues
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput)
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    NativeRootRelates target leftOutput rightOutput
      (revealLayerValues index lay encoding) (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  apply (nativeRootRelates_sequenceFin target leftOutput rightOutput _ _ fun chainIdx =>
    nativeRootRelates_revealPublishedCoordinate_of_ne target leftOutput rightOutput
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
        (encoding chainIdx))
      (chainValueCoordinate_ne_layerRoot hroot lay (treeIndexAt index lay)
        (leafIndexAt index lay) chainIdx (encoding chainIdx))).bind
  intro leftValues rightValues hvalues
  subst rightValues
  apply (nativeRootRelates_sequenceFin target leftOutput rightOutput _ _ fun level => by
    by_cases hlevel : level.val < layerHeight lay
    · rw [if_pos hlevel]
      cases hzero : level.val with
      | zero =>
          exact nativeRootRelates_revealPublishedCoordinate_of_ne target leftOutput rightOutput
            (.position (.leaf lay (treeIndexAt index lay)
              (leafOfNat (Nat.xor (leafIndexAt index lay).val 1)))) (by
                obtain ⟨rootLay, rootTree, rfl⟩ := hroot
                simp [layerRootPosition])
      | succ current =>
          rw [Nat.add_one]
          simp only
          by_cases hcurrent : current < maxLayerHeight
          · rw [dif_pos hcurrent]
            exact nativeRootRelates_revealPublishedCoordinate_of_ne target leftOutput rightOutput
              (.position (.node lay (treeIndexAt index lay) ⟨current, hcurrent⟩
                (leafOfNat (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
              (by
                intro heq
                exact (pathNode_ne_layerRoot hroot lay (treeIndexAt index lay) current hcurrent _
                  (by omega)) (Coordinate.position.inj heq))
          · rw [dif_neg hcurrent]
            exact nativeRootRelates_pure target leftOutput rightOutput 0
    · rw [if_neg hlevel]
      exact nativeRootRelates_pure target leftOutput rightOutput 0).bind
  intro leftPath rightPath hpath
  subst rightPath
  exact nativeRootRelates_pure target leftOutput rightOutput (leftValues, leftPath)

theorem nativeRootRelates_ordinaryRomImpl
    (target : Position) (leftOutput rightOutput : HashOutput)
    (query : OracleWorld.Domain) :
    NativeRootRelates target leftOutput rightOutput
      (ordinaryRomImpl query) (ordinaryRomImpl query) := by
  cases query with
  | inl n => exact nativeRootRelates_splitUniformImpl target leftOutput rightOutput n
  | inr input => exact nativeRootRelates_ordinaryHashImpl target leftOutput rightOutput input

end SphincsSecurity.Concrete.OtsProbeSimulation
