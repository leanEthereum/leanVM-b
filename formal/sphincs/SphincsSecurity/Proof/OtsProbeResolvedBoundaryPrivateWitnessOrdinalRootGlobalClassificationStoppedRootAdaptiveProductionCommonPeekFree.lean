import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionCommonFactorization

/-!
# Target-peek freedom of common root production

The concrete actions executed by the permissive selector never inspect a hidden position through
the lazy-state peek query. Their decisions use the canonical public state passed as ordinary data.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def TargetPeekFree (target : Position)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ cache, (computation.run cache).IsQueryBoundP (IsTargetPeek target) 0

namespace TargetPeekFree

theorem pure (target : Position) (value : α) :
    TargetPeekFree target
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro cache
  simp

theorem get (target : Position) :
    TargetPeekFree target
      (get : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) SplitHashCache) := by
  intro cache
  simp

theorem modify (target : Position) (update : SplitHashCache → SplitHashCache) :
    TargetPeekFree target
      (modify update : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) Unit) := by
  intro cache
  simp

theorem bind
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    {target : Position}
    (hleft : TargetPeekFree target left)
    (hnext : ∀ value, TargetPeekFree target (next value)) :
    TargetPeekFree target (left >>= next) := by
  intro cache
  rw [StateT.run_bind]
  have hbound := OracleComp.isQueryBoundP_bind (n := 0) (m := 0) (hleft cache)
    (fun result _ => hnext result.1 result.2)
  simpa using hbound

theorem map
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {target : Position}
    (hcomputation : TargetPeekFree target computation) (transform : α → β) :
    TargetPeekFree target (transform <$> computation) := by
  rw [map_eq_bind_pure_comp]
  exact hcomputation.bind fun value => TargetPeekFree.pure target (transform value)

end TargetPeekFree

theorem splitHashQuery_targetPeekFree
    (target : Position) (key : SplitHashKey) :
    TargetPeekFree target (splitHashQuery key) := by
  intro cache
  rw [splitHashQuery_run_eq]
  cases hlookup : cache key with
  | some output => simp
  | none =>
      change (LazyRevealProbe.hashOutputQuery (Coordinate := Coordinate) >>= fun output =>
        pure (output, Function.update cache key (some output))).IsQueryBoundP
          (IsTargetPeek target) 0
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
      · simp [LazyRevealProbe.hashOutputQuery, IsTargetPeek]
      · intro _ _
        simp

theorem splitUniformImpl_targetPeekFree
    (target : Position) (n : unifSpec.Domain) :
    TargetPeekFree target (splitUniformImpl n) := by
  intro cache
  change (((fun output : Fin (n + 1) => (output, cache)) <$>
    LazyRevealProbe.uniformQuery (Coordinate := Coordinate) n).IsQueryBoundP
      (IsTargetPeek target) 0)
  rw [OracleComp.isQueryBoundP_map_iff]
  simp [LazyRevealProbe.uniformQuery, IsTargetPeek]

theorem ensureCoordinate_targetPeekFree
    (target : Position) (coordinate : Coordinate) :
    TargetPeekFree target (ensureCoordinate coordinate) := by
  intro cache
  unfold ensureCoordinate
  change (((fun value : Unit => (value, cache)) <$>
    LazyRevealProbe.ensureQuery coordinate).IsQueryBoundP (IsTargetPeek target) 0)
  rw [OracleComp.isQueryBoundP_map_iff]
  simp [LazyRevealProbe.ensureQuery, IsTargetPeek]

theorem revealCoordinateOutput_targetPeekFree
    (target : Position) (coordinate : Coordinate) :
    TargetPeekFree target (revealCoordinateOutput coordinate) := by
  intro cache
  change (LazyRevealProbe.revealQuery coordinate >>= fun output =>
    pure (output, Function.update cache (.hidden coordinate) (some output))).IsQueryBoundP
      (IsTargetPeek target) 0
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
  · simp [LazyRevealProbe.revealQuery, IsTargetPeek]
  · intro _ _
    simp

theorem revealCoordinate_targetPeekFree
    (target : Position) (coordinate : Coordinate) :
    TargetPeekFree target (revealCoordinate coordinate) := by
  unfold revealCoordinate
  exact (revealCoordinateOutput_targetPeekFree target coordinate).bind fun output =>
    TargetPeekFree.pure target (truncateHash output)

theorem revealPosition_targetPeekFree
    (target : Position) (position : Position) :
    TargetPeekFree target (revealPosition position) :=
  revealCoordinate_targetPeekFree target (.position position)

theorem publishCoordinate_targetPeekFree
    (target : Position) (coordinate : Coordinate) :
    TargetPeekFree target (publishCoordinate coordinate) := by
  intro cache
  unfold publishCoordinate
  change (((fun value : Unit => (value, cache)) <$>
    LazyRevealProbe.publishQuery coordinate).IsQueryBoundP (IsTargetPeek target) 0)
  rw [OracleComp.isQueryBoundP_map_iff]
  simp [LazyRevealProbe.publishQuery, IsTargetPeek]

theorem probe_targetPeekFree (target : Position) (candidate : Probe) :
    TargetPeekFree target (probe candidate) := by
  intro cache
  unfold probe
  change (((fun value : Unit => (value, cache)) <$>
    LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate).IsQueryBoundP
      (IsTargetPeek target) 0)
  rw [OracleComp.isQueryBoundP_map_iff]
  simp [LazyRevealProbe.probeQuery, IsTargetPeek]

theorem executeCandidate?_targetPeekFree
    (target : Position) (candidate : Option Probe) :
    TargetPeekFree target (executeCandidate? candidate) := by
  cases candidate with
  | none => exact TargetPeekFree.pure target ()
  | some candidate => exact probe_targetPeekFree target candidate

theorem resolvePublicKnownInput_targetPeekFree
    (target : Position) (parameter : PublicParameter)
    (publicState : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (input : HashInput) :
    TargetPeekFree target
      (resolvePublicKnownInput parameter publicState coordinate input) := by
  unfold resolvePublicKnownInput
  cases hknown : purePeekTableInput parameter publicState coordinate with
  | none => exact splitHashQuery_targetPeekFree target (.ordinary input)
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        exact (revealCoordinateOutput_targetPeekFree target coordinate).bind fun output =>
          (publishCoordinate_targetPeekFree target coordinate).bind fun _ =>
            (TargetPeekFree.modify target fun cache : SplitHashCache =>
              Function.update cache (.ordinary input) (some output)).bind fun _ =>
                TargetPeekFree.pure target output
      · simp only [heq, ↓reduceIte]
        exact splitHashQuery_targetPeekFree target (.ordinary input)

theorem probingHashQueryPublicAction_targetPeekFree
    (target : Position) (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (action : PlannedHashAction) :
    TargetPeekFree target
      (probingHashQueryPublicAction parameter input publicState action) := by
  cases action with
  | ordinary => exact splitHashQuery_targetPeekFree target (.ordinary input)
  | resolve coordinate =>
      exact resolvePublicKnownInput_targetPeekFree target parameter publicState coordinate input

theorem probingHashQueryAfterRootAwarePublicPlan_targetPeekFree
    (target : Position) (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery) :
    TargetPeekFree target
      (probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan) := by
  unfold probingHashQueryAfterRootAwarePublicPlan
  exact (executeCandidate?_targetPeekFree target
    (rootAwareCandidateForPlan? parameter input plan)).bind fun _ =>
      probingHashQueryPublicAction_targetPeekFree target parameter input publicState plan.action

theorem permissiveRootAwarePublicAction_targetPeekFree
    (target : Position) (parameter : PublicParameter) (input : HashInput)
    (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) :
    (permissiveRootAwarePublicAction parameter input table state cache).IsQueryBoundP
      (IsTargetPeek target) 0 :=
  probingHashQueryAfterRootAwarePublicPlan_targetPeekFree target parameter input
    (materializedCanonicalContext table state).state
    (permissiveRootAwarePlan parameter input table state) cache

theorem sequenceFin_targetPeekFree
    {n : Nat} (target : Position)
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomputation : ∀ index, TargetPeekFree target (computation index)) :
    TargetPeekFree target (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact TargetPeekFree.pure target Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomputation 0).bind fun head =>
        (ih (fun index => computation index.succ)
          (fun index => hcomputation index.succ)).bind fun tail =>
            TargetPeekFree.pure target (Fin.cases head tail : Fin (n + 1) → α)

theorem simulateQ_ordinaryHashImpl_targetPeekFree
    (target : Position) (computation : OracleComp HashSpec α) :
    TargetPeekFree target (simulateQ ordinaryHashImpl computation) := by
  intro cache
  apply (OracleComp.isQueryBoundP_false computation 0).simulateQ_run_StateT_of_step
  intro input workingCache
  exact splitHashQuery_targetPeekFree target (.ordinary input) workingCache

theorem simulateQ_ordinaryRomImpl_targetPeekFree
    (target : Position) (computation : OracleComp OracleWorld α) :
    TargetPeekFree target (simulateQ ordinaryRomImpl computation) := by
  intro cache
  apply (OracleComp.isQueryBoundP_false computation 0).simulateQ_run_StateT_of_step
  intro input workingCache
  cases input with
  | inl n => exact splitUniformImpl_targetPeekFree target n workingCache
  | inr hashInput =>
      exact splitHashQuery_targetPeekFree target (.ordinary hashInput) workingCache

theorem ensureFullChain_targetPeekFree
    (target : Position) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    TargetPeekFree target (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (sequenceFin_targetPeekFree target _ fun step =>
    ensureCoordinate_targetPeekFree target
      (.position (.chain lay tree leafIdx chainIdx step))).bind fun _ =>
        TargetPeekFree.pure target ()

theorem ensureChainPrefix_targetPeekFree
    (target : Position) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    TargetPeekFree target (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (sequenceFin_targetPeekFree target _ fun step => by
    split
    · exact ensureCoordinate_targetPeekFree target
        (.position (.chain lay tree leafIdx chainIdx step))
    · exact TargetPeekFree.pure target ()).bind fun _ => TargetPeekFree.pure target ()

theorem ensureOtsLeaf_targetPeekFree
    (target : Position) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    TargetPeekFree target (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (sequenceFin_targetPeekFree target _ fun chainIdx =>
    ensureFullChain_targetPeekFree target lay tree leafIdx chainIdx).bind fun _ =>
      ensureCoordinate_targetPeekFree target (.position (.leaf lay tree leafIdx))

theorem ensureTreeNode_targetPeekFree
    (target : Position) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx, TargetPeekFree target (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => ensureOtsLeaf_targetPeekFree target lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (ensureTreeNode_targetPeekFree target lay tree level (2 * nodeIdx)).bind fun _ =>
        (ensureTreeNode_targetPeekFree target lay tree level (2 * nodeIdx + 1)).bind fun _ => by
          split
          · exact ensureCoordinate_targetPeekFree target
              (.position (.node lay tree ⟨level, by assumption⟩ (leafOfNat nodeIdx)))
          · exact TargetPeekFree.pure target ()

theorem maskedTreeNode_targetPeekFree
    (target : Position) (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat) :
    TargetPeekFree target (maskedTreeNode lay tree level nodeIdx) := by
  cases level with
  | zero =>
      rw [maskedTreeNode]
      exact (ensureTreeNode_targetPeekFree target lay tree 0 nodeIdx).bind fun _ =>
        revealPosition_targetPeekFree target (.leaf lay tree (leafOfNat nodeIdx))
  | succ current =>
      rw [maskedTreeNode]
      exact (ensureTreeNode_targetPeekFree target lay tree (current + 1) nodeIdx).bind fun _ => by
        split
        · exact revealPosition_targetPeekFree target
            (.node lay tree ⟨current, by assumption⟩ (leafOfNat nodeIdx))
        · exact TargetPeekFree.pure target 0

theorem maskedTreeRoot_targetPeekFree
    (target : Position) (lay : Layer) (tree : TreeIndex) :
    TargetPeekFree target (maskedTreeRoot lay tree) :=
  maskedTreeNode_targetPeekFree target lay tree (layerHeight lay) 0

theorem ensureTreePath_targetPeekFree
    (target : Position) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    TargetPeekFree target (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (sequenceFin_targetPeekFree target _ fun level => by
    split
    · exact ensureTreeNode_targetPeekFree target lay tree level.val
        (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
    · exact TargetPeekFree.pure target ()).bind fun _ => TargetPeekFree.pure target ()

theorem maskedOtsSignFrom_targetPeekFree
    (target : Position) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter,
      TargetPeekFree target
        (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, _ => TargetPeekFree.pure target none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      exact (simulateQ_ordinaryHashImpl_targetPeekFree target
        (encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))).bind fun encoded => by
            cases encoded with
            | none =>
                exact maskedOtsSignFrom_targetPeekFree target parameter lay tree leafIdx message
                  attempts (counter + 1)
            | some encoding =>
                exact (sequenceFin_targetPeekFree target _ fun chainIdx =>
                  ensureChainPrefix_targetPeekFree target lay tree leafIdx chainIdx
                    (encoding chainIdx)).bind fun _ => TargetPeekFree.pure target _

theorem maskedOtsSign_targetPeekFree
    (target : Position) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    TargetPeekFree target (maskedOtsSign parameter lay tree leafIdx message) :=
  maskedOtsSignFrom_targetPeekFree target parameter lay tree leafIdx message
    encodingAttemptLimit 0

theorem maskedLayerMessage_targetPeekFree
    (target : Position) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    TargetPeekFree target (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split
  · exact maskedTreeRoot_targetPeekFree target _ _
  · exact simulateQ_ordinaryHashImpl_targetPeekFree target _

theorem maskedSignLayer_targetPeekFree
    (target : Position) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    TargetPeekFree target (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (maskedLayerMessage_targetPeekFree target parameter ftsSecret index lay).bind fun message =>
    (maskedOtsSign_targetPeekFree target parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) message).bind fun signed => by
        cases signed with
        | none => exact TargetPeekFree.pure target none
        | some part =>
            exact (ensureTreePath_targetPeekFree target lay (treeIndexAt index lay)
              (leafIndexAt index lay)).bind fun _ => TargetPeekFree.pure target (some part)

theorem revealPublishedCoordinate_targetPeekFree
    (target : Position) (coordinate : Coordinate) :
    TargetPeekFree target (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (revealCoordinate_targetPeekFree target coordinate).bind fun value =>
    (publishCoordinate_targetPeekFree target coordinate).bind fun _ =>
      TargetPeekFree.pure target value

theorem revealLayerPathValue_targetPeekFree
    (target : Position) (index : Index) (lay : Layer) (level : Fin maxLayerHeight) :
    TargetPeekFree target (if level.val < layerHeight lay then
      match level.val with
      | 0 => revealPublishedCoordinate (.position (.leaf lay (treeIndexAt index lay)
          (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
      | current + 1 =>
          if hlevel : current < maxLayerHeight then
            revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
              ⟨current, hlevel⟩
              (leafOfNat (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
          else pure 0
    else pure 0) := by
  by_cases hbelow : level.val < layerHeight lay
  · rw [if_pos hbelow]
    cases hvalue : level.val with
    | zero =>
        exact revealPublishedCoordinate_targetPeekFree target (.position (.leaf lay
          (treeIndexAt index lay) (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
    | succ current =>
        simp only
        split
        · exact revealPublishedCoordinate_targetPeekFree target (.position (.node lay
            (treeIndexAt index lay) ⟨current, by assumption⟩
            (leafOfNat (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
        · exact TargetPeekFree.pure target 0
  · rw [if_neg hbelow]
    exact TargetPeekFree.pure target 0

theorem revealLayerValues_targetPeekFree
    (target : Position) (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) :
    TargetPeekFree target (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (sequenceFin_targetPeekFree target _ fun chainIdx =>
    revealPublishedCoordinate_targetPeekFree target
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx (encoding chainIdx))).bind fun values =>
          (sequenceFin_targetPeekFree target _ fun level =>
            revealLayerPathValue_targetPeekFree target index lay level).bind fun path =>
              TargetPeekFree.pure target (values, path)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem maskedSignAfterDigest_targetPeekFree
    (target : Position) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    TargetPeekFree target
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest
  exact (simulateQ_ordinaryHashImpl_targetPeekFree target
    (ftsOpen parameter index leaves (ftsSecret index))).bind fun ftsPath =>
      (sequenceFin_targetPeekFree target _ fun lay =>
        maskedSignLayer_targetPeekFree target parameter ftsSecret index lay).bind fun layers => by
          cases hparts : traverseOption layers with
          | none => exact TargetPeekFree.pure target none
          | some parts =>
              exact (sequenceFin_targetPeekFree target _ fun lay =>
                revealLayerValues_targetPeekFree target index lay (parts lay).2).bind fun revealed =>
                  TargetPeekFree.pure target (some
                    (show Signature from
                    { randomness := randomness
                      ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
                      ftsPath := ftsPath
                      counter := fun lay => (parts lay).1
                      chainValue := fun lay => (revealed lay).1
                      authPath := flattenPaths fun lay => (revealed lay).2 }))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem maskedSign_targetPeekFree
    (target : Position) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    TargetPeekFree target (maskedSign parameter root ftsSecret message) := by
  unfold maskedSign
  exact (simulateQ_ordinaryRomImpl_targetPeekFree target
    (signDigestLoop digestAttemptLimit
      ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ message)).bind fun selected => by
        cases selected with
        | none => exact TargetPeekFree.pure target none
        | some data =>
            exact maskedSignAfterDigest_targetPeekFree target parameter ftsSecret
              data.1 data.2.1 data.2.2

end SphincsSecurity.Concrete.OtsProbeSimulation
