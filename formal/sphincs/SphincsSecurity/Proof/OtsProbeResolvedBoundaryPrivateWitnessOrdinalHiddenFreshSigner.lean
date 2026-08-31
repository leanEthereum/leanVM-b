import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateRootCandidate
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHiddenFreshSteps

/-!
# Signer freshness

The masked signer can materialize an unpublished position only while computing a layer message.
Such a position is exactly the root of the tree below that layer. Every other coordinate is either
left unchanged or revealed together with publication. This file isolates those exceptional roots
from the candidate-freshness argument.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

theorem rootAwarePlannedCandidate?_hasStructuralParent
    {parameter : PublicParameter} {input : HashInput}
    {state : LazyRevealProbe.State Coordinate} {candidate : Probe}
    (hplan : rootAwarePlannedCandidate? parameter input state = some candidate) :
    candidate.HasStructuralParent := by
  unfold rootAwarePlannedCandidate? at hplan
  cases hstructural : (purePlanProbingHashQuery parameter input state).candidate? with
  | some structural =>
      simp only [hstructural] at hplan
      have heq : candidate = structural := by simpa using hplan.symm
      subst candidate
      exact purePlanProbingHashQuery_candidate_hasStructuralParent parameter input state
        structural hstructural
  | none =>
      simp only [hstructural] at hplan
      exact encodingLayerRootCandidateAt_hasStructuralParent
        ((decodeEncodingLayerRootCandidate?_eq_some_iff parameter input candidate).mp hplan)

theorem PreservesCoordinate.sequenceFin
    {coordinate : Coordinate} {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomputation : ∀ index, PreservesCoordinate coordinate (computation index)) :
    PreservesCoordinate coordinate (sequenceFin computation) := by
  induction n with
  | zero => exact preservesCoordinate_pure coordinate Fin.elim0
  | succ n ih =>
      rw [SphincsSecurity.Concrete.sequenceFin]
      exact (hcomputation 0).bind fun head =>
        (ih (fun index => computation index.succ)
          (fun index => hcomputation index.succ)).bind fun tail =>
            preservesCoordinate_pure coordinate
              (Fin.cases head tail : Fin (n + 1) → α)

theorem PreservesCoordinate.simulateQ
    {spec : OracleSpec ι} {coordinate : Coordinate}
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (himpl : ∀ query, PreservesCoordinate coordinate (impl query))
    (computation : OracleComp spec α) :
    PreservesCoordinate coordinate (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact preservesCoordinate_pure coordinate value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (himpl query).bind ih

theorem preservesCoordinate_ensureCoordinate
    (coordinate ensured : Coordinate) :
    PreservesCoordinate coordinate (ensureCoordinate ensured) := by
  intro state cache fuel finalState remaining value finalCache hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.ensureQuery ensured >>= fun result => pure (result, cache))) at hresult
  rw [LazyRevealProbe.ensureQuery, LazyRevealProbe.runRaw_ensure_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  simp [LazyRevealProbe.State.ensure]

theorem preservesCoordinate_simulateQ_ordinaryHashImpl
    (coordinate : Coordinate) (computation : OracleComp HashSpec α) :
    PreservesCoordinate coordinate (simulateQ ordinaryHashImpl computation) :=
  PreservesCoordinate.simulateQ ordinaryHashImpl
    (fun input => preservesCoordinate_splitHashQuery coordinate (.ordinary input)) computation

theorem preservesCoordinate_simulateQ_splitUniformImpl
    (coordinate : Coordinate) (computation : ProbComp α) :
    PreservesCoordinate coordinate (simulateQ splitUniformImpl computation) := by
  intro state cache fuel finalState remaining value finalCache hresult
  obtain ⟨rfl, rfl, _hcache, _hvalue⟩ :=
    mem_runRaw_simulateQ_splitUniformImpl_projects computation state finalState cache finalCache
      fuel remaining value hresult
  exact ⟨rfl, Iff.rfl⟩

theorem preservesCoordinate_ensureFullChain
    (coordinate : Coordinate) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    PreservesCoordinate coordinate (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (PreservesCoordinate.sequenceFin _ fun step =>
    preservesCoordinate_ensureCoordinate coordinate
      (.position (.chain lay tree leafIdx chainIdx step))).bind fun _ =>
        preservesCoordinate_pure coordinate ()

theorem preservesCoordinate_ensureChainPrefix
    (coordinate : Coordinate) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    PreservesCoordinate coordinate (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (PreservesCoordinate.sequenceFin _ fun step => by
    split
    · exact preservesCoordinate_ensureCoordinate coordinate
        (.position (.chain lay tree leafIdx chainIdx step))
    · exact preservesCoordinate_pure coordinate ()).bind fun _ =>
        preservesCoordinate_pure coordinate ()

theorem preservesCoordinate_ensureOtsLeaf
    (coordinate : Coordinate) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    PreservesCoordinate coordinate (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (PreservesCoordinate.sequenceFin _ fun chainIdx =>
    preservesCoordinate_ensureFullChain coordinate lay tree leafIdx chainIdx).bind fun _ =>
      preservesCoordinate_ensureCoordinate coordinate (.position (.leaf lay tree leafIdx))

theorem preservesCoordinate_ensureTreeNode
    (coordinate : Coordinate) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx, PreservesCoordinate coordinate (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => by
      rw [ensureTreeNode]
      exact preservesCoordinate_ensureOtsLeaf coordinate lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (preservesCoordinate_ensureTreeNode coordinate lay tree level
        (2 * nodeIdx)).bind fun _ =>
          (preservesCoordinate_ensureTreeNode coordinate lay tree level
            (2 * nodeIdx + 1)).bind fun _ => by
              split
              · exact preservesCoordinate_ensureCoordinate coordinate _
              · exact preservesCoordinate_pure coordinate ()

theorem preservesCoordinate_ensureTreePath
    (coordinate : Coordinate) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    PreservesCoordinate coordinate (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (PreservesCoordinate.sequenceFin _ fun level => by
    split
    · exact preservesCoordinate_ensureTreeNode coordinate lay tree level.val
        (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
    · exact preservesCoordinate_pure coordinate ()).bind fun _ =>
        preservesCoordinate_pure coordinate ()

theorem preservesCoordinate_maskedTreeRoot_of_not_layerRoot
    (position : Position) (hnotRoot : ¬IsLayerRoot position)
    (lay : Layer) (tree : TreeIndex) :
    PreservesCoordinate (.position position) (maskedTreeRoot lay tree) := by
  have hpos : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  have hlevel : layerHeight lay - 1 < maxLayerHeight := by
    have hle := layerHeight_le lay
    omega
  have hne : Coordinate.position position ≠
      .position (.node lay tree ⟨layerHeight lay - 1, hlevel⟩ (leafOfNat 0)) := by
    intro heq
    have hposition : position =
        .node lay tree ⟨layerHeight lay - 1, hlevel⟩ (leafOfNat 0) := by
      simpa using heq
    apply hnotRoot
    refine ⟨lay, tree, ?_⟩
    rw [hposition]
    rfl
  unfold maskedTreeRoot
  rw [show layerHeight lay = (layerHeight lay - 1) + 1 by omega, maskedTreeNode]
  exact (preservesCoordinate_ensureTreeNode (.position position) lay tree
    (layerHeight lay - 1 + 1) 0).bind fun _ => by
      rw [dif_pos hlevel]
      exact preservesCoordinate_revealPosition_of_ne (.position position)
        (.node lay tree ⟨layerHeight lay - 1, hlevel⟩ (leafOfNat 0)) hne

theorem preservesCoordinate_maskedLayerMessage_of_not_layerRoot
    (position : Position) (hnotRoot : ¬IsLayerRoot position)
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    PreservesCoordinate (.position position)
      (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split
  · exact preservesCoordinate_maskedTreeRoot_of_not_layerRoot position hnotRoot _ _
  · exact preservesCoordinate_simulateQ_ordinaryHashImpl (.position position) _

theorem preservesCoordinate_maskedOtsSignFrom
    (coordinate : Coordinate) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter,
      PreservesCoordinate coordinate
        (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, _ => preservesCoordinate_pure coordinate none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      exact (preservesCoordinate_simulateQ_ordinaryHashImpl coordinate _).bind fun encoded =>
        match encoded with
        | none => preservesCoordinate_maskedOtsSignFrom coordinate parameter lay tree leafIdx
            message attempts (counter + 1)
        | some encoding =>
            (PreservesCoordinate.sequenceFin _ fun chainIdx =>
              preservesCoordinate_ensureChainPrefix coordinate lay tree leafIdx chainIdx
                (encoding chainIdx)).bind fun _ => preservesCoordinate_pure coordinate _

theorem preservesCoordinate_maskedOtsSign
    (coordinate : Coordinate) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    PreservesCoordinate coordinate (maskedOtsSign parameter lay tree leafIdx message) :=
  preservesCoordinate_maskedOtsSignFrom coordinate parameter lay tree leafIdx message
    encodingAttemptLimit 0

theorem preservesCoordinateMaterializedPublished_maskedSignLayer_of_not_layerRoot
    (position : Position) (hnotRoot : ¬IsLayerRoot position)
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    PreservesCoordinateMaterializedPublished (.position position)
      (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  apply (preservesCoordinate_maskedLayerMessage_of_not_layerRoot position hnotRoot parameter
    ftsSecret index lay).to_materializedPublished.bind
  intro message
  apply (preservesCoordinate_maskedOtsSign (.position position) parameter lay
    (treeIndexAt index lay) (leafIndexAt index lay) message).to_materializedPublished.bind
  intro selected
  cases selected with
  | none => exact (preservesCoordinate_pure (.position position) none).to_materializedPublished
  | some selected =>
      exact (preservesCoordinate_ensureTreePath (.position position) lay
        (treeIndexAt index lay) (leafIndexAt index lay)).to_materializedPublished.bind fun _ =>
          (preservesCoordinate_pure (.position position) (some selected)).to_materializedPublished

theorem preservesCoordinateMaterializedPublished_revealPublishedCoordinate
    (coordinate : Coordinate) :
    PreservesCoordinateMaterializedPublished coordinate
      (revealPublishedCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  unfold revealPublishedCoordinate at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨revealRaw, hreveal, hrest⟩ := hresult
  cases revealRaw with
  | stopped hit => simp at hrest
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealed, revealCache⟩
      simp [publishCoordinate, LazyRevealProbe.publishQuery,
        LazyRevealProbe.runRaw] at hrest
      rcases hrest with ⟨rfl, rfl, rfl, rfl⟩
      intro _hvalue
      simp [LazyRevealProbe.State.publish]

theorem preservesCoordinateMaterializedPublished_revealPublishedCoordinate_at
    (coordinate published : Coordinate) :
    PreservesCoordinateMaterializedPublished coordinate
      (revealPublishedCoordinate published) := by
  by_cases heq : coordinate = published
  · subst published
    exact preservesCoordinateMaterializedPublished_revealPublishedCoordinate coordinate
  · unfold revealPublishedCoordinate
    exact ((preservesCoordinate_revealCoordinate_of_ne coordinate published heq).bind
      fun _ => (preservesCoordinate_publishCoordinate_of_ne coordinate published heq).bind
        fun _ => preservesCoordinate_pure coordinate _).to_materializedPublished

theorem PreservesCoordinateMaterializedPublished.sequenceFin
    {coordinate : Coordinate} {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomputation : ∀ index,
      PreservesCoordinateMaterializedPublished coordinate (computation index)) :
    PreservesCoordinateMaterializedPublished coordinate (sequenceFin computation) := by
  induction n with
  | zero => exact (preservesCoordinate_pure coordinate Fin.elim0).to_materializedPublished
  | succ n ih =>
      rw [SphincsSecurity.Concrete.sequenceFin]
      exact (hcomputation 0).bind fun head =>
        (ih (fun index => computation index.succ)
          (fun index => hcomputation index.succ)).bind fun tail =>
            (preservesCoordinate_pure coordinate
              (Fin.cases head tail : Fin (n + 1) → α)).to_materializedPublished

theorem preservesCoordinateMaterializedPublished_revealLayerValues
    (coordinate : Coordinate) (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) :
    PreservesCoordinateMaterializedPublished coordinate
      (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  apply (PreservesCoordinateMaterializedPublished.sequenceFin _ fun chainIdx =>
    preservesCoordinateMaterializedPublished_revealPublishedCoordinate_at coordinate
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
        (encoding chainIdx))).bind
  intro _
  apply (PreservesCoordinateMaterializedPublished.sequenceFin _ fun level => by
    split
    · cases hvalue : level.val with
      | zero =>
          exact preservesCoordinateMaterializedPublished_revealPublishedCoordinate_at coordinate _
      | succ current =>
          rw [show current + 1 = Nat.succ current by omega]
          change PreservesCoordinateMaterializedPublished coordinate
            (if hlevel : current < maxLayerHeight then
              revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
                ⟨current, hlevel⟩ (leafOfNat
                  (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
            else pure 0)
          by_cases hlevel : current < maxLayerHeight
          · rw [dif_pos hlevel]
            exact preservesCoordinateMaterializedPublished_revealPublishedCoordinate_at coordinate _
          · rw [dif_neg hlevel]
            exact (preservesCoordinate_pure coordinate 0).to_materializedPublished
    · exact (preservesCoordinate_pure coordinate 0).to_materializedPublished).bind
  intro _
  exact (preservesCoordinate_pure coordinate _).to_materializedPublished

theorem preservesCoordinate_simulateQ_ordinaryRomImpl
    (coordinate : Coordinate) (computation : OracleComp OracleWorld α) :
    PreservesCoordinate coordinate (simulateQ ordinaryRomImpl computation) := by
  apply PreservesCoordinate.simulateQ ordinaryRomImpl
  intro query
  cases query with
  | inl n =>
      exact preservesCoordinate_simulateQ_splitUniformImpl coordinate
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
  | inr input => exact preservesCoordinate_splitHashQuery coordinate (.ordinary input)

theorem preservesCoordinateMaterializedPublished_maskedSignAfterDigest_of_not_layerRoot
    (position : Position) (hnotRoot : ¬IsLayerRoot position)
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    PreservesCoordinateMaterializedPublished (.position position)
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest
  apply (preservesCoordinate_simulateQ_ordinaryHashImpl (.position position) _).to_materializedPublished.bind
  intro _
  apply (PreservesCoordinateMaterializedPublished.sequenceFin _ fun lay =>
    preservesCoordinateMaterializedPublished_maskedSignLayer_of_not_layerRoot position hnotRoot
      parameter ftsSecret index lay).bind
  intro layers
  cases hparts : traverseOption layers with
  | none => exact (preservesCoordinate_pure (.position position) none).to_materializedPublished
  | some parts =>
      apply (PreservesCoordinateMaterializedPublished.sequenceFin _ fun lay =>
        preservesCoordinateMaterializedPublished_revealLayerValues (.position position) index lay
          (parts lay).2).bind
      intro _
      exact (preservesCoordinate_pure (.position position) _).to_materializedPublished

theorem preservesCoordinateMaterializedPublished_maskedSign_of_not_layerRoot
    (position : Position) (hnotRoot : ¬IsLayerRoot position)
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    PreservesCoordinateMaterializedPublished (.position position)
      (maskedSign parameter root ftsSecret message) := by
  unfold maskedSign
  apply (preservesCoordinate_simulateQ_ordinaryRomImpl (.position position) _).to_materializedPublished.bind
  intro selected
  cases selected with
  | none => exact (preservesCoordinate_pure (.position position) none).to_materializedPublished
  | some selected =>
      exact preservesCoordinateMaterializedPublished_maskedSignAfterDigest_of_not_layerRoot
        position hnotRoot parameter ftsSecret selected.1 selected.2.1 selected.2.2

def CandidatePositionsFreshExceptLayerRoots (context : DeferredContext) : Prop :=
  ∀ position parent, Position.parentOf position = some parent →
    Coordinate.position position ∉ context.state.revealed →
    (context.state.values (.position position) = none ∧ context.values position = none) ∨
      IsLayerRoot position

theorem CandidatePositionsFresh.exceptLayerRoots
    {context : DeferredContext} (hfresh : CandidatePositionsFresh context) :
    CandidatePositionsFreshExceptLayerRoots context := by
  intro position parent hparent hhidden
  exact Or.inl (hfresh position parent hparent hhidden)

theorem CandidatePositionsFreshExceptLayerRoots.canonicalize
    {context : DeferredContext} (hfresh : CandidatePositionsFreshExceptLayerRoots context)
    (table : OtsSecretIndex → HashOutput) :
    CandidatePositionsFreshExceptLayerRoots
      (canonicalizeMaterializedValues table context) := by
  intro position parent hparent hhidden
  have horiginalHidden : Coordinate.position position ∉ context.state.revealed := by
    simpa [canonicalizeMaterializedValues_revealed] using hhidden
  rcases hfresh position parent hparent horiginalHidden with hfreshPosition | hroot
  · left
    constructor
    · unfold canonicalizeMaterializedValues publicMaterializedValues
      simp [horiginalHidden]
    · exact hfreshPosition.2
  · exact Or.inr hroot

theorem candidatePositionsFreshExceptLayerRoots_uniformStep
    (n : Nat) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Fin (n + 1) × SplitHashCache))
    (hfresh : CandidatePositionsFreshExceptLayerRoots context)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table
        ((splitUniformImpl n).run cache))) :
    CandidatePositionsFreshExceptLayerRoots
      (canonicalizeMaterializedValues table result.context) := by
  unfold splitUniformImpl at hresult
  rw [StateT.run_liftM, LazyRevealProbe.uniformQuery,
    runDirectResolvedWitnessFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
  obtain ⟨output, _houtput, htail⟩ := hresult
  simp [runDirectResolvedWitnessFromTable] at htail
  subst result
  exact hfresh.canonicalize table

theorem candidatePositionsFreshExceptLayerRoots_hashStep
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (hfresh : CandidatePositionsFreshExceptLayerRoots context)
    (hpublished : PublishedValues context.state)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table
        ((probingHashQueryAfterPlan parameter input plan).run cache))) :
    CandidatePositionsFreshExceptLayerRoots
      (canonicalizeMaterializedValues table result.context) := by
  let computation := (probingHashQueryAfterPlan parameter input plan).run cache
  have hdetailed : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation) := by
    rw [← map_erase_runDirectResolvedWitnessFromTable computation context fuel table,
      support_map]
    exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
  have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed computation context fuel
    table result hdetailed
  have hraw := raw_done_of_mem_runDirectResolvedFromTable computation context fuel table result
    hdirect
  intro position parent hparent hhidden
  by_cases hroot : IsLayerRoot position
  · exact Or.inr hroot
  · left
    have hfinalHidden : Coordinate.position position ∉ result.context.state.revealed := by
      simpa [canonicalizeMaterializedValues_revealed] using hhidden
    have hinitialHidden : Coordinate.position position ∉ context.state.revealed := by
      intro hinitialRevealed
      obtain ⟨output, hvalue⟩ := Option.ne_none_iff_exists'.mp
        (hpublished (.position position) hinitialRevealed)
      have hknown := knownPublishedCoordinateResult_of_mem_runDirectResolvedWitnessFromTable
        (.position position) output computation context fuel table hvalue hinitialRevealed
        (DirectWitnessResult.done result) hresult
      exact hfinalHidden hknown.2
    have hinitialFresh : context.state.values (.position position) = none ∧
        context.values position = none := by
      rcases hfresh position parent hparent hinitialHidden with hfreshPosition | hrootPosition
      · exact hfreshPosition
      · exact False.elim (hroot hrootPosition)
    have hfinalState : result.context.state.values (.position position) = none := by
      by_contra hvalue
      exact hfinalHidden
        (preservesCoordinateMaterializedPublished_probingHashQueryAfterPlan parameter input plan
          (.position position) context.state cache fuel result.context.state result.remaining
            result.value.1 result.value.2
            (fun hvalue => False.elim (hvalue hinitialFresh.1)) hraw hvalue)
    have hfinalPrivate := auxiliaryPositionValue_none_of_done_runDirectResolvedWitnessFromTable
      position computation context fuel table result hinitialFresh.1 hinitialFresh.2 hresult
        hfinalState
    constructor
    · unfold canonicalizeMaterializedValues publicMaterializedValues
      simp [hfinalHidden]
    · exact hfinalPrivate

theorem candidatePositionsFreshExceptLayerRoots_signStep
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hfresh : CandidatePositionsFreshExceptLayerRoots context)
    (hpublished : PublishedValues context.state)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table
        ((maskedSign parameter root ftsSecret message).run cache))) :
    CandidatePositionsFreshExceptLayerRoots
      (canonicalizeMaterializedValues table result.context) := by
  let computation := (maskedSign parameter root ftsSecret message).run cache
  have hdetailed : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation) := by
    rw [← map_erase_runDirectResolvedWitnessFromTable computation context fuel table,
      support_map]
    exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
  have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed computation context fuel
    table result hdetailed
  have hraw := raw_done_of_mem_runDirectResolvedFromTable computation context fuel table result
    hdirect
  intro position parent hparent hhidden
  by_cases hrootPosition : IsLayerRoot position
  · exact Or.inr hrootPosition
  · left
    have hfinalHidden : Coordinate.position position ∉ result.context.state.revealed := by
      simpa [canonicalizeMaterializedValues_revealed] using hhidden
    have hinitialHidden : Coordinate.position position ∉ context.state.revealed := by
      intro hinitialRevealed
      obtain ⟨output, hvalue⟩ := Option.ne_none_iff_exists'.mp
        (hpublished (.position position) hinitialRevealed)
      have hknown := knownPublishedCoordinateResult_of_mem_runDirectResolvedWitnessFromTable
        (.position position) output computation context fuel table hvalue hinitialRevealed
        (DirectWitnessResult.done result) hresult
      exact hfinalHidden hknown.2
    have hinitialFresh : context.state.values (.position position) = none ∧
        context.values position = none := by
      rcases hfresh position parent hparent hinitialHidden with hfreshPosition | hroot
      · exact hfreshPosition
      · exact False.elim (hrootPosition hroot)
    have hfinalState : result.context.state.values (.position position) = none := by
      by_contra hvalue
      exact hfinalHidden
        (preservesCoordinateMaterializedPublished_maskedSign_of_not_layerRoot position
          hrootPosition parameter root ftsSecret message context.state cache fuel
            result.context.state result.remaining result.value.1 result.value.2
              (fun hvalue => False.elim (hvalue hinitialFresh.1)) hraw hvalue)
    have hfinalPrivate := auxiliaryPositionValue_none_of_done_runDirectResolvedWitnessFromTable
      position computation context fuel table result hinitialFresh.1 hinitialFresh.2 hresult
        hfinalState
    constructor
    · unfold canonicalizeMaterializedValues publicMaterializedValues
      simp [hfinalHidden]
    · exact hfinalPrivate

end SphincsSecurity.Concrete.OtsProbeSimulation
