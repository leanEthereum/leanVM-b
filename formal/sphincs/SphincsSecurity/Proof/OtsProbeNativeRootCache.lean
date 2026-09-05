import SphincsSecurity.Proof.OtsProbeNativeRootEncoding

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem rootEncodingNativeCouples_worldStep
    (parameter : PublicParameter) (target : Position) (leftRoot rightRoot : Digest)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (finish : α → SplitHashCache → β × SplitHashCache)
    (hfinish : ∀ output leftCache rightCache,
      RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache →
      (finish output leftCache).1 = (finish output rightCache).1 ∧
        RootEncodingCacheRel parameter target leftRoot rightRoot
          (finish output leftCache).2 (finish output rightCache).2) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (fun cache => computation >>= fun output => pure (finish output cache)) := by
  intro leftCache rightCache hcache context fuel table
  change RelTriple
    (runResolvedFromTable context fuel table (computation >>= fun output => pure (finish output leftCache)))
    (runResolvedFromTable context fuel table (computation >>= fun output => pure (finish output rightCache))) _
  rw [runResolvedFromTable_bind, runResolvedFromTable_bind]
  apply relTriple_bind (relTriple_refl (runResolvedFromTable context fuel table computation))
  intro leftResult rightResult heq
  subst rightResult
  cases leftResult with
  | none => exact relTriple_pure_pure trivial
  | some result =>
      simp only [runResolvedFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, hfinish result.value leftCache rightCache hcache⟩

theorem rootEncodingNativeCouples_ensureFullChain
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (rootEncodingNativeCouples_sequenceFin parameter target leftRoot rightRoot _
    fun step => rootEncodingNativeCouples_ensureCoordinate parameter target leftRoot rightRoot
      (.position (.chain lay tree leafIdx chainIdx step))).bind fun _ =>
        rootEncodingNativeCouples_pure parameter target leftRoot rightRoot ()

theorem rootEncodingNativeCouples_ensureOtsLeaf
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (rootEncodingNativeCouples_sequenceFin parameter target leftRoot rightRoot _
    fun chainIdx => rootEncodingNativeCouples_ensureFullChain parameter target leftRoot rightRoot
      lay tree leafIdx chainIdx).bind fun _ =>
        rootEncodingNativeCouples_ensureCoordinate parameter target leftRoot rightRoot
          (.position (.leaf lay tree leafIdx))

theorem rootEncodingNativeCouples_ensureTreeNode
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx,
      RootEncodingNativeCouples parameter target leftRoot rightRoot
        (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => by
      rw [ensureTreeNode]
      exact rootEncodingNativeCouples_ensureOtsLeaf parameter target leftRoot rightRoot lay tree
        (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (rootEncodingNativeCouples_ensureTreeNode parameter target leftRoot rightRoot lay tree
        level (2 * nodeIdx)).bind fun _ =>
          (rootEncodingNativeCouples_ensureTreeNode parameter target leftRoot rightRoot lay tree
            level (2 * nodeIdx + 1)).bind fun _ => by
              by_cases hlevel : level < maxLayerHeight
              · rw [dif_pos hlevel]
                exact rootEncodingNativeCouples_ensureCoordinate parameter target leftRoot
                  rightRoot (.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)))
              · rw [dif_neg hlevel]
                exact rootEncodingNativeCouples_pure parameter target leftRoot rightRoot ()

theorem rootEncodingNativeCouples_ensureTreePath
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (rootEncodingNativeCouples_sequenceFin parameter target leftRoot rightRoot _
    fun level => by
      by_cases hlevel : level.val < layerHeight lay
      · rw [if_pos hlevel]
        exact rootEncodingNativeCouples_ensureTreeNode parameter target leftRoot rightRoot lay tree
          level.val (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
      · rw [if_neg hlevel]
        exact rootEncodingNativeCouples_pure parameter target leftRoot rightRoot ()).bind fun _ =>
          rootEncodingNativeCouples_pure parameter target leftRoot rightRoot ()

theorem relTriple_native_splitHashQuery_same_nonroot
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (key : SplitHashKey)
    (hkey : ¬RootEncodingKey parameter target key)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runResolvedFromTable state fuel table ((splitHashQuery key).run leftCache))
      (runResolvedFromTable state fuel table ((splitHashQuery key).run rightCache))
      (RootEncodingNativeSameRel parameter target leftRoot rightRoot) := by
  have hlookup := hcache.lookup_nonroot key hkey
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  cases hleft : leftCache key with
  | some output =>
      have hright : rightCache key = some output := by
        rw [← hlookup]
        exact hleft
      simp only [hright, runResolvedFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩
  | none =>
      have hright : rightCache key = none := by
        rw [← hlookup]
        exact hleft
      simp only [hright]
      unfold LazyRevealProbe.hashOutputQuery
      rw [runResolvedFromTable_hashOutput_query_bind,
        runResolvedFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput houtput
      subst rightOutput
      simp only [runResolvedFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
        hcache.update_same_nonroot key leftOutput hkey⟩

theorem rootEncodingNativeCouples_splitHashQuery_same_nonroot
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (key : SplitHashKey)
    (hkey : ¬RootEncodingKey parameter target key) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (splitHashQuery key) := by
  intro leftCache rightCache hcache state fuel table
  exact relTriple_native_splitHashQuery_same_nonroot parameter target leftRoot rightRoot key hkey
    leftCache rightCache hcache state fuel table

theorem rootEncodingNativeCouples_splitUniformImpl
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (n : Nat) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (splitUniformImpl n) := by
  intro leftCache rightCache hcache state fuel table
  unfold splitUniformImpl LazyRevealProbe.uniformQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runResolvedFromTable_uniform_query_bind, runResolvedFromTable_uniform_query_bind]
  apply relTriple_bind
    (relTriple_refl (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
  intro leftOutput rightOutput houtput
  subst rightOutput
  simp only [runResolvedFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem rootEncodingNativeCouples_simulateQ_splitUniformImpl
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (computation : ProbComp α) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (simulateQ splitUniformImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      rw [simulateQ_pure]
      exact rootEncodingNativeCouples_pure parameter target leftRoot rightRoot value
  | query_bind n next ih =>
      rw [simulateQ_query_bind]
      exact (rootEncodingNativeCouples_splitUniformImpl parameter target leftRoot rightRoot n).bind
        fun output => ih output

theorem rootEncodingNativeCouples_messageDigest
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (publicRoot : Digest)
    (message : Message) (randomness : Randomness) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl
        (messageDigest parameter publicRoot message randomness)) := by
  unfold messageDigest oracleHash
  simp only [simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_spec_query,
    simulateQ_pure, ordinaryHashImpl]
  exact (rootEncodingNativeCouples_splitHashQuery_same_nonroot parameter target leftRoot
    rightRoot (.ordinary (tweakableHashInput parameter .message
      (messageDigestPayload publicRoot message randomness)))
    (not_encodingInputNamesRoot_tweakableHashInput_of_not_encoding parameter target .message
      _ (by trivial) (by simp))).bind fun output =>
        rootEncodingNativeCouples_pure parameter target leftRoot rightRoot
          (truncateMessageDigest output)

theorem rootEncodingNativeCouples_signAttempt
    (target : Position) (leftRoot rightRoot : Digest)
    (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    RootEncodingNativeCouples secretKey.parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl (signAttempt secretKey message randomness)) := by
  unfold signAttempt
  simp only [simulateQ_bind]
  exact (rootEncodingNativeCouples_messageDigest secretKey.parameter target leftRoot rightRoot
    secretKey.root message randomness).bind fun digest => by
      split <;> exact rootEncodingNativeCouples_pure secretKey.parameter target leftRoot rightRoot _

theorem rootEncodingNativeCouples_signDigestLoop
    (target : Position) (leftRoot rightRoot : Digest)
    (secretKey : SecretKey) (message : Message) : ∀ attempts,
    RootEncodingNativeCouples secretKey.parameter target leftRoot rightRoot
      (simulateQ ordinaryRomImpl (signDigestLoop attempts secretKey message))
  | 0 => by
      rw [signDigestLoop, simulateQ_pure]
      exact rootEncodingNativeCouples_pure secretKey.parameter target leftRoot rightRoot none
  | attempts + 1 => by
      rw [signDigestLoop, simulateQ_bind]
      have hrandomness : RootEncodingNativeCouples secretKey.parameter target leftRoot rightRoot
          (simulateQ ordinaryRomImpl (liftM sampleRandomness)) := by
        rw [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_left]
        exact rootEncodingNativeCouples_simulateQ_splitUniformImpl secretKey.parameter target
          leftRoot rightRoot sampleRandomness
      exact hrandomness.bind fun randomness => by
        rw [simulateQ_bind]
        have hattempt : RootEncodingNativeCouples secretKey.parameter target leftRoot rightRoot
            (simulateQ ordinaryRomImpl
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))))) := by
          rw [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_right]
          exact rootEncodingNativeCouples_signAttempt target leftRoot rightRoot secretKey message
            randomness
        exact hattempt.bind fun attempt => by
          cases attempt with
          | none =>
              exact rootEncodingNativeCouples_signDigestLoop target leftRoot rightRoot secretKey
                message attempts
          | some selected =>
              rw [simulateQ_pure]
              exact rootEncodingNativeCouples_pure secretKey.parameter target leftRoot rightRoot
                (some (randomness, selected.1, selected.2))

theorem rootEncodingNativeCouples_tweakableHash_of_not_encoding
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (domain : HashDomain) (payload : HashInput)
    (hinRange : domain.InRange)
    (hnotEncoding : ∀ lay tree leafIdx, domain ≠ .encoding lay tree leafIdx) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl (tweakableHash parameter domain payload)) := by
  unfold tweakableHash oracleHash
  simp only [simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_spec_query,
    simulateQ_pure]
  exact (rootEncodingNativeCouples_splitHashQuery_same_nonroot parameter target leftRoot
    rightRoot (.ordinary (tweakableHashInput parameter domain payload))
    (not_encodingInputNamesRoot_tweakableHashInput_of_not_encoding parameter target domain
      payload hinRange hnotEncoding)).bind fun _ =>
        rootEncodingNativeCouples_pure parameter target leftRoot rightRoot _

theorem rootEncodingNativeCouples_ftsLeafHash
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index) (tree : FtsTree)
    (leafIdx : FtsLeaf) (secret : Digest) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl
        (ftsLeafHash parameter index tree leafIdx secret)) := by
  unfold ftsLeafHash
  exact rootEncodingNativeCouples_tweakableHash_of_not_encoding parameter target leftRoot
    rightRoot (.ftsLeaf index tree leafIdx) (digestBytes secret) (by trivial) (by simp)

theorem rootEncodingNativeCouples_ftsNode
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) : ∀ level nodeIdx,
    level ≤ ftsTreeHeight →
    2 ^ level * (nodeIdx + 1) ≤ 2 ^ ftsTreeHeight →
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl
        (ftsNode parameter index tree secret level nodeIdx))
  | 0, nodeIdx, _hlevel, _hspan => by
      rw [ftsNode_zero_eq]
      exact rootEncodingNativeCouples_ftsLeafHash parameter target leftRoot rightRoot index tree
        (ftsLeafOfNat nodeIdx) (secret (ftsLeafOfNat nodeIdx))
  | level + 1, nodeIdx, hlevel, hspan => by
      rw [ftsNode_succ_eq]
      simp only [simulateQ_bind]
      have hleftSpan : 2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ ftsTreeHeight := by
        rw [pow_succ] at hspan
        calc
          2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ level * (2 * (nodeIdx + 1)) :=
            Nat.mul_le_mul_left _ (by omega)
          _ = 2 ^ level * 2 * (nodeIdx + 1) := by ring
          _ ≤ 2 ^ ftsTreeHeight := hspan
      have hrightSpan : 2 ^ level * (2 * nodeIdx + 1 + 1) ≤ 2 ^ ftsTreeHeight := by
        rw [pow_succ] at hspan
        calc
          2 ^ level * (2 * nodeIdx + 1 + 1) = 2 ^ level * 2 * (nodeIdx + 1) := by ring
          _ ≤ 2 ^ ftsTreeHeight := hspan
      have hinRange : (HashDomain.ftsNode index tree (level + 1) nodeIdx).InRange := by
        show level + 1 < 2 ^ 32 ∧ nodeIdx < 2 ^ 32
        constructor
        · have : ftsTreeHeight < 2 ^ 32 := by norm_num [ftsTreeHeight]
          omega
        · have hnode : nodeIdx < 2 ^ ftsTreeHeight := by
            have hpow : 0 < 2 ^ (level + 1) := Nat.two_pow_pos _
            nlinarith
          have : 2 ^ ftsTreeHeight ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) (by
            norm_num [ftsTreeHeight])
          omega
      exact (rootEncodingNativeCouples_ftsNode parameter target leftRoot rightRoot index tree
        secret level (2 * nodeIdx) (by omega) hleftSpan).bind fun left =>
          (rootEncodingNativeCouples_ftsNode parameter target leftRoot rightRoot index tree
            secret level (2 * nodeIdx + 1) (by omega) hrightSpan).bind fun right =>
              rootEncodingNativeCouples_tweakableHash_of_not_encoding parameter target leftRoot
                rightRoot (.ftsNode index tree (level + 1) nodeIdx) (nodePayload left right)
                hinRange (by simp)

theorem rootEncodingNativeCouples_ftsKey
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index)
    (secret : FtsTree → FtsLeaf → Digest) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl (ftsKey parameter index secret)) := by
  unfold ftsKey
  rw [simulateQ_bind, simulateQ_ordinaryHashImpl_sequenceFin]
  exact (rootEncodingNativeCouples_sequenceFin parameter target leftRoot rightRoot _
    fun tree => rootEncodingNativeCouples_ftsNode parameter target leftRoot rightRoot index tree
      (secret tree) ftsTreeHeight 0 le_rfl (by simp)).bind fun roots =>
        rootEncodingNativeCouples_tweakableHash_of_not_encoding parameter target leftRoot
          rightRoot (.ftsRoots index) (ftsRootsPayload roots) (by trivial) (by simp)

theorem rootEncodingNativeCouples_ftsOpen
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index)
    (leaves : DigestTree → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl (ftsOpen parameter index leaves secret)) := by
  unfold ftsOpen
  rw [simulateQ_ordinaryHashImpl_sequenceFin]
  apply rootEncodingNativeCouples_sequenceFin
  intro tree
  rw [simulateQ_ordinaryHashImpl_sequenceFin]
  apply rootEncodingNativeCouples_sequenceFin
  intro level
  exact rootEncodingNativeCouples_ftsNode parameter target leftRoot rightRoot index tree
    (secret tree) level.val (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)
      (Nat.le_of_lt level.isLt)
      (FtsProbeSimulation.ftsOpen_node_bound (leaves (ftsIndexOf tree)) level)

theorem rootEncodingNativeCouples_revealCoordinateOutput
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (coordinate : Coordinate) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (revealCoordinateOutput coordinate) := by
  have heq : revealCoordinateOutput coordinate =
      (fun cache : SplitHashCache => LazyRevealProbe.revealQuery coordinate >>= fun output =>
        pure (output, Function.update cache (.hidden coordinate) (some output))) := by
    funext cache
    exact revealCoordinateOutput_run_eq coordinate cache
  rw [heq]
  exact rootEncodingNativeCouples_worldStep parameter target leftRoot rightRoot _ _
    fun output leftCache rightCache hcache =>
      ⟨rfl, hcache.update_same_nonroot (.hidden coordinate) output
        (not_rootEncodingKey_hidden parameter target coordinate)⟩

theorem rootEncodingNativeCouples_revealCoordinate
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (coordinate : Coordinate) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (revealCoordinate coordinate) := by
  have heq : revealCoordinate coordinate =
      (fun cache : SplitHashCache => LazyRevealProbe.revealQuery coordinate >>= fun output =>
        pure (truncateHash output, Function.update cache (.hidden coordinate) (some output))) := by
    funext cache
    exact revealCoordinate_run coordinate cache
  rw [heq]
  exact rootEncodingNativeCouples_worldStep parameter target leftRoot rightRoot _ _
    fun output leftCache rightCache hcache =>
      ⟨rfl, hcache.update_same_nonroot (.hidden coordinate) output
        (not_rootEncodingKey_hidden parameter target coordinate)⟩

theorem rootEncodingNativeCouples_publishCoordinate
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (coordinate : Coordinate) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (publishCoordinate coordinate) := by
  unfold publishCoordinate
  exact rootEncodingNativeCouples_worldStep parameter target leftRoot rightRoot _ _
    fun output leftCache rightCache hcache => ⟨rfl, hcache⟩

theorem rootEncodingNativeCouples_revealPosition
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (position : Position) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (revealPosition position) :=
  rootEncodingNativeCouples_revealCoordinate parameter target leftRoot rightRoot
    (.position position)

theorem rootEncodingNativeCouples_revealPublishedCoordinate
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (coordinate : Coordinate) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (rootEncodingNativeCouples_revealCoordinate parameter target leftRoot rightRoot
    coordinate).bind fun _ =>
      (rootEncodingNativeCouples_publishCoordinate parameter target leftRoot rightRoot
        coordinate).bind fun _ =>
          rootEncodingNativeCouples_pure parameter target leftRoot rightRoot _

theorem rootEncodingNativeCouples_revealLayerValues
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  apply (rootEncodingNativeCouples_sequenceFin parameter target leftRoot rightRoot _
    fun chainIdx => rootEncodingNativeCouples_revealPublishedCoordinate parameter target
      leftRoot rightRoot
        (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
          (encoding chainIdx))).bind
  intro values
  apply (rootEncodingNativeCouples_sequenceFin parameter target leftRoot rightRoot _
    fun level => by
      by_cases hlevel : level.val < layerHeight lay
      · rw [if_pos hlevel]
        cases hzero : level.val with
        | zero =>
            exact rootEncodingNativeCouples_revealPublishedCoordinate parameter target leftRoot
              rightRoot (.position (.leaf lay (treeIndexAt index lay)
                (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
        | succ current =>
            rw [Nat.add_one]
            simp only
            by_cases hcurrent : current < maxLayerHeight
            · rw [dif_pos hcurrent]
              exact rootEncodingNativeCouples_revealPublishedCoordinate parameter target leftRoot
                rightRoot (.position (.node lay (treeIndexAt index lay) ⟨current, hcurrent⟩
                  (leafOfNat (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
            · rw [dif_neg hcurrent]
              exact rootEncodingNativeCouples_pure parameter target leftRoot rightRoot 0
      · rw [if_neg hlevel]
        exact rootEncodingNativeCouples_pure parameter target leftRoot rightRoot 0).bind
  intro path
  exact rootEncodingNativeCouples_pure parameter target leftRoot rightRoot (values, path)

theorem rootEncodingNativeCouples_maskedTreeNode
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx,
      RootEncodingNativeCouples parameter target leftRoot rightRoot
        (maskedTreeNode lay tree level nodeIdx)
  | level, nodeIdx => by
      unfold maskedTreeNode
      apply (rootEncodingNativeCouples_ensureTreeNode parameter target leftRoot rightRoot lay tree
        level nodeIdx).bind
      intro _
      cases level with
      | zero =>
          exact rootEncodingNativeCouples_revealPosition parameter target leftRoot rightRoot
            (.leaf lay tree (leafOfNat nodeIdx))
      | succ current =>
          rw [Nat.add_one]
          simp only
          by_cases hlevel : current < maxLayerHeight
          · rw [dif_pos hlevel]
            exact rootEncodingNativeCouples_revealPosition parameter target leftRoot rightRoot
              (.node lay tree ⟨current, hlevel⟩ (leafOfNat nodeIdx))
          · rw [dif_neg hlevel]
            exact rootEncodingNativeCouples_pure parameter target leftRoot rightRoot 0

theorem rootEncodingNativeCouples_maskedTreeRoot
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (maskedTreeRoot lay tree) :=
  rootEncodingNativeCouples_maskedTreeNode parameter target leftRoot rightRoot lay tree
    (layerHeight lay) 0

theorem rootEncodingNativeCouples_maskedLayerMessage
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  by_cases hbelow : lay.val + 1 < numLayers
  · rw [dif_pos hbelow]
    exact rootEncodingNativeCouples_maskedTreeRoot parameter target leftRoot rightRoot
      ⟨lay.val + 1, hbelow⟩ (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
  · rw [dif_neg hbelow]
    exact rootEncodingNativeCouples_ftsKey parameter target leftRoot rightRoot index
      (ftsSecret index)

set_option maxHeartbeats 1000000 in
theorem rootEncodingNativeCouples_encode_of_not_positionNames
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (position : EncodingPosition)
    (message : Digest) (counter : Nat)
    (hnotPosition : ¬EncodingPositionNamesRoot target position) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl
        (encode parameter position.lay position.tree position.leafIdx message
          (BitVec.ofNat counterBits counter))) := by
  unfold encode tweakableHash oracleHash
  simp only [simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_spec_query,
    simulateQ_pure, ordinaryHashImpl, bind_assoc, pure_bind]
  exact (rootEncodingNativeCouples_splitHashQuery_same_nonroot parameter target leftRoot
    rightRoot (.ordinary (encodingRetryInput parameter position message counter))
    (not_encodingInputNamesRoot_encodingRetryInput_of_not_positionNames hnotPosition message
      counter)).bind fun output =>
        rootEncodingNativeCouples_pure parameter target leftRoot rightRoot
          (TargetSum.decodeDigest (truncateHash output))

set_option maxHeartbeats 1000000 in
theorem rootEncodingNativeCouples_maskedOtsSignFrom_of_not_positionNames
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest)
    (hnotPosition : ¬EncodingPositionNamesRoot target ⟨lay, tree, leafIdx⟩) :
    ∀ attempts counter,
      RootEncodingNativeCouples parameter target leftRoot rightRoot
        (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => by
      rw [maskedOtsSignFrom]
      exact rootEncodingNativeCouples_pure parameter target leftRoot rightRoot none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      apply (rootEncodingNativeCouples_encode_of_not_positionNames parameter target leftRoot
        rightRoot ⟨lay, tree, leafIdx⟩ message counter hnotPosition).bind
      intro encoded
      cases encoded with
      | none =>
          exact rootEncodingNativeCouples_maskedOtsSignFrom_of_not_positionNames parameter target
            leftRoot rightRoot lay tree leafIdx message hnotPosition attempts (counter + 1)
      | some encoding =>
          exact (rootEncodingNativeCouples_sequenceFin parameter target leftRoot rightRoot
            (fun chainIdx => ensureChainPrefix lay tree leafIdx chainIdx (encoding chainIdx))
            (fun chainIdx => rootEncodingNativeCouples_ensureChainPrefix parameter target
              leftRoot rightRoot lay tree leafIdx chainIdx (encoding chainIdx))).bind fun _ =>
                rootEncodingNativeCouples_pure parameter target leftRoot rightRoot
                  (some (BitVec.ofNat counterBits counter, encoding))

theorem rootEncodingNativeCouples_maskedOtsSign_of_not_positionNames
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest)
    (hnotPosition : ¬EncodingPositionNamesRoot target ⟨lay, tree, leafIdx⟩) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (maskedOtsSign parameter lay tree leafIdx message) :=
  rootEncodingNativeCouples_maskedOtsSignFrom_of_not_positionNames parameter target leftRoot
    rightRoot lay tree leafIdx message hnotPosition encodingAttemptLimit 0

theorem rootEncodingNativeCouples_maskedOtsLayerAfterMessage_of_not_positionNames
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index) (lay : Layer)
    (message : Digest)
    (hnotPosition : ¬EncodingPositionNamesRoot target
      ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (maskedOtsLayerAfterMessage parameter index lay message) := by
  unfold maskedOtsLayerAfterMessage
  apply (rootEncodingNativeCouples_maskedOtsSign_of_not_positionNames parameter target leftRoot
    rightRoot lay (treeIndexAt index lay) (leafIndexAt index lay) message hnotPosition).bind
  intro selected
  cases selected with
  | none => exact rootEncodingNativeCouples_pure parameter target leftRoot rightRoot none
  | some selected =>
      exact (rootEncodingNativeCouples_ensureTreePath parameter target leftRoot rightRoot lay
        (treeIndexAt index lay) (leafIndexAt index lay)).bind fun _ =>
          rootEncodingNativeCouples_pure parameter target leftRoot rightRoot (some selected)

theorem rootEncodingNativeRelates_maskedOtsLayerAfterMessage
    (parameter : PublicParameter) (index : Index) (lay : Layer)
    (hnotBottom : lay ≠ bottomLayer) (leftRoot rightRoot : Digest) :
    RootEncodingNativeRelates parameter (layerMessagePosition index lay) leftRoot rightRoot
      (maskedOtsLayerAfterMessage parameter index lay leftRoot)
      (maskedOtsLayerAfterMessage parameter index lay rightRoot) := by
  have hposition : EncodingPositionNamesRoot (layerMessagePosition index lay)
      ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ :=
    ⟨index, rfl, rfl, hnotBottom, rfl⟩
  unfold maskedOtsLayerAfterMessage
  apply (rootEncodingNativeRelates_maskedOtsSign parameter (layerMessagePosition index lay)
    leftRoot rightRoot lay (treeIndexAt index lay) (leafIndexAt index lay) hposition).bind
  intro leftSelected rightSelected hselected
  subst rightSelected
  cases leftSelected with
  | none =>
      exact (rootEncodingNativeCouples_pure parameter (layerMessagePosition index lay)
        leftRoot rightRoot none).relates
  | some selected =>
      exact ((rootEncodingNativeCouples_ensureTreePath parameter
        (layerMessagePosition index lay) leftRoot rightRoot lay (treeIndexAt index lay)
        (leafIndexAt index lay)).bind fun _ =>
          rootEncodingNativeCouples_pure parameter (layerMessagePosition index lay)
            leftRoot rightRoot (some selected)).relates

end SphincsSecurity.Concrete.OtsProbeSimulation
