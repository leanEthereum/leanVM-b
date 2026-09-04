import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedRootSwap

/-!
# Permissive encoding-root swap

The first half of the delayed root exchange changes the root used in encoding inputs while keeping
the hidden structural state fixed. This relation retains permissive executions, including an
unrelated pending hit.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def RootEncodingPermissiveCleanSameRel
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) :
    Option (CleanRunResult (α × SplitHashCache)) →
      Option (CleanRunResult (α × SplitHashCache)) → Prop
  | some left, some right =>
      left.state = right.state ∧ left.remaining = right.remaining ∧
        left.table = right.table ∧ left.value.1 = right.value.1 ∧
        RootEncodingCacheRel parameter target leftRoot rightRoot left.value.2 right.value.2
  | none, none => True
  | _, _ => False

def RootEncodingPermissiveRelates
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftCache rightCache,
    RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache →
    ∀ state fuel table,
      RelTriple
        (runPermissiveFromTable state fuel table (left.run leftCache))
        (runPermissiveFromTable state fuel table (right.run rightCache))
        (RootEncodingPermissiveCleanSameRel parameter target leftRoot rightRoot)

def RootEncodingPermissiveCouples
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  RootEncodingPermissiveRelates parameter target leftRoot rightRoot computation computation

theorem rootEncodingPermissiveCouples_pure
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (value : α) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro leftCache rightCache hcache state fuel table
  simp only [StateT.run_pure, runPermissiveFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem RootEncodingPermissiveRelates.bind
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {leftNext rightNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hfirst : RootEncodingPermissiveRelates parameter target leftRoot rightRoot left right)
    (hnext : ∀ leftValue rightValue, leftValue = rightValue →
      RootEncodingPermissiveRelates parameter target leftRoot rightRoot
        (leftNext leftValue) (rightNext rightValue)) :
    RootEncodingPermissiveRelates parameter target leftRoot rightRoot
      (left >>= leftNext) (right >>= rightNext) := by
  intro leftCache rightCache hcache state fuel table
  rw [StateT.run_bind, StateT.run_bind, runPermissiveFromTable_bind,
    runPermissiveFromTable_bind]
  apply relTriple_bind (hfirst leftCache rightCache hcache state fuel table)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [RootEncodingPermissiveCleanSameRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [RootEncodingPermissiveCleanSameRel] at hresult
      | some rightResult =>
          rcases hresult with ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
          simp only
          rw [← hstate, ← hremaining, ← htable, ← hvalue]
          exact hnext leftResult.value.1 leftResult.value.1 rfl leftResult.value.2
            rightResult.value.2 hnextCache leftResult.state leftResult.remaining leftResult.table

theorem RootEncodingPermissiveCouples.bind
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hfirst : RootEncodingPermissiveCouples parameter target leftRoot rightRoot left)
    (hnext : ∀ value,
      RootEncodingPermissiveCouples parameter target leftRoot rightRoot (next value)) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot (left >>= next) :=
  RootEncodingPermissiveRelates.bind hfirst fun leftValue rightValue hvalue => by
    subst rightValue
    exact hnext leftValue

theorem rootEncodingPermissiveCouples_sequenceFin
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index,
      RootEncodingPermissiveCouples parameter target leftRoot rightRoot
        (computation index)) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun head =>
        (ih (fun index : Fin n => computation index.succ)
          (fun index => hcomponent index.succ)).bind fun tail =>
            rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot
              (Fin.cases head tail : Fin (n + 1) → α)

theorem rootEncodingPermissiveCouples_ensureCoordinate
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (coordinate : Coordinate) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (ensureCoordinate coordinate) := by
  intro leftCache rightCache hcache state fuel table
  unfold ensureCoordinate LazyRevealProbe.ensureQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runPermissiveFromTable_ensure_query_bind, runPermissiveFromTable_ensure_query_bind]
  simp only [runPermissiveFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem rootEncodingPermissiveCouples_splitUniformImpl
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (n : Nat) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (splitUniformImpl n) := by
  intro leftCache rightCache hcache state fuel table
  unfold splitUniformImpl LazyRevealProbe.uniformQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runPermissiveFromTable_uniform_query_bind, runPermissiveFromTable_uniform_query_bind]
  apply relTriple_bind
    (relTriple_refl (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
  intro leftOutput rightOutput houtput
  subst rightOutput
  simp only [runPermissiveFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem relTriple_rootEncodingPermissive_splitHashQuery_same_nonroot
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (key : SplitHashKey)
    (hkey : ¬RootEncodingKey parameter target key)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runPermissiveFromTable state fuel table ((splitHashQuery key).run leftCache))
      (runPermissiveFromTable state fuel table ((splitHashQuery key).run rightCache))
      (RootEncodingPermissiveCleanSameRel parameter target leftRoot rightRoot) := by
  have hlookup := hcache.lookup_nonroot key hkey
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  cases hleft : leftCache key with
  | some output =>
      have hright : rightCache key = some output := by
        rw [← hlookup]
        exact hleft
      simp only [hright, runPermissiveFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩
  | none =>
      have hright : rightCache key = none := by
        rw [← hlookup]
        exact hleft
      simp only [hright]
      unfold LazyRevealProbe.hashOutputQuery
      rw [runPermissiveFromTable_hashOutput_query_bind,
        runPermissiveFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput houtput
      subst rightOutput
      simp only [runPermissiveFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
        hcache.update_same_nonroot key leftOutput hkey⟩

theorem rootEncodingPermissiveCouples_splitHashQuery_same_nonroot
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (key : SplitHashKey)
    (hkey : ¬RootEncodingKey parameter target key) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (splitHashQuery key) := by
  intro leftCache rightCache hcache state fuel table
  exact relTriple_rootEncodingPermissive_splitHashQuery_same_nonroot parameter target leftRoot
    rightRoot key hkey leftCache rightCache hcache state fuel table

theorem rootEncodingPermissiveCouples_revealCoordinate
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (coordinate : Coordinate) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (revealCoordinate coordinate) := by
  intro leftCache rightCache hcache state fuel table
  rw [revealCoordinate_run, revealCoordinate_run, LazyRevealProbe.revealQuery,
    runPermissiveFromTable_reveal_query_bind, runPermissiveFromTable_reveal_query_bind]
  have hhidden : ¬RootEncodingKey parameter target (.hidden coordinate) :=
    not_rootEncodingKey_hidden parameter target coordinate
  cases hvalue : state.values coordinate with
  | some output =>
      simp only [runPermissiveFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
        hcache.update_same_nonroot (.hidden coordinate) output hhidden⟩
  | none =>
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          simp only [runPermissiveFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
            hcache.update_same_nonroot
              (.hidden (.chainStart lay tree leafIdx chainIdx))
              (table ⟨lay, tree, leafIdx, chainIdx⟩) hhidden⟩
      | position position =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput houtput
          subst rightOutput
          simp only [runPermissiveFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
            hcache.update_same_nonroot (.hidden (.position position)) leftOutput hhidden⟩

theorem rootEncodingPermissiveCouples_publishCoordinate
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (coordinate : Coordinate) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (publishCoordinate coordinate) := by
  intro leftCache rightCache hcache state fuel table
  unfold publishCoordinate LazyRevealProbe.publishQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runPermissiveFromTable_publish_query_bind, runPermissiveFromTable_publish_query_bind]
  simp only [runPermissiveFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem relTriple_rootEncodingPermissive_splitHashQuery_encodingRetryInput
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (position : EncodingPosition) (counter : Nat)
    (hposition : EncodingPositionNamesRoot target position)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runPermissiveFromTable state fuel table
        ((splitHashQuery (.ordinary
          (encodingRetryInput parameter position leftRoot counter))).run leftCache))
      (runPermissiveFromTable state fuel table
        ((splitHashQuery (.ordinary
          (encodingRetryInput parameter position rightRoot counter))).run rightCache))
      (RootEncodingPermissiveCleanSameRel parameter target leftRoot rightRoot) := by
  let leftInput := encodingRetryInput parameter position leftRoot counter
  let rightInput := encodingRetryInput parameter position rightRoot counter
  have hlookup := hcache.retry position counter hposition
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  cases hleft : leftCache (.ordinary leftInput) with
  | some output =>
      have hright : rightCache (.ordinary rightInput) = some output := by
        rw [← hlookup]
        exact hleft
      simp only [rightInput, hright, runPermissiveFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩
  | none =>
      have hright : rightCache (.ordinary rightInput) = none := by
        rw [← hlookup]
        exact hleft
      simp only [rightInput, hright]
      unfold LazyRevealProbe.hashOutputQuery
      rw [runPermissiveFromTable_hashOutput_query_bind,
        runPermissiveFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput houtput
      subst rightOutput
      simp only [runPermissiveFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
        hcache.update_retry position counter hposition leftOutput⟩

theorem relTriple_rootEncodingPermissiveAttemptRun
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (position : EncodingPosition) (counter : Nat)
    (hposition : EncodingPositionNamesRoot target position)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runPermissiveFromTable state fuel table
        (rootEncodingAttemptRun parameter position leftRoot counter leftCache))
      (runPermissiveFromTable state fuel table
        (rootEncodingAttemptRun parameter position rightRoot counter rightCache))
      (RootEncodingPermissiveCleanSameRel parameter target leftRoot rightRoot) := by
  unfold rootEncodingAttemptRun
  rw [runPermissiveFromTable_bind, runPermissiveFromTable_bind]
  apply relTriple_bind
    (relTriple_rootEncodingPermissive_splitHashQuery_encodingRetryInput parameter target leftRoot
      rightRoot position counter hposition leftCache rightCache hcache state fuel table)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [RootEncodingPermissiveCleanSameRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [RootEncodingPermissiveCleanSameRel] at hresult
      | some rightResult =>
          rcases hresult with ⟨hstate, hremaining, htable, houtput, hnextCache⟩
          simp only
          rw [← hstate, ← hremaining, ← htable, ← houtput]
          simp only [runPermissiveFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hnextCache⟩

theorem rootEncodingPermissiveRelates_encode
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (position : EncodingPosition) (counter : Nat)
    (hposition : EncodingPositionNamesRoot target position) :
    RootEncodingPermissiveRelates parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl
        (encode parameter position.lay position.tree position.leafIdx leftRoot
          (BitVec.ofNat counterBits counter)))
      (simulateQ ordinaryHashImpl
        (encode parameter position.lay position.tree position.leafIdx rightRoot
          (BitVec.ofNat counterBits counter))) := by
  intro leftCache rightCache hcache state fuel table
  rw [← rootEncodingAttemptRun_eq_encode parameter position leftRoot counter leftCache,
    ← rootEncodingAttemptRun_eq_encode parameter position rightRoot counter rightCache]
  exact relTriple_rootEncodingPermissiveAttemptRun parameter target leftRoot rightRoot position
    counter hposition leftCache rightCache hcache state fuel table

theorem rootEncodingPermissiveRelates_maskedOtsSignFrom
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex)
    (hposition : EncodingPositionNamesRoot target ⟨lay, tree, leafIdx⟩) :
    ∀ attempts counter,
      RootEncodingPermissiveRelates parameter target leftRoot rightRoot
        (maskedOtsSignFrom parameter lay tree leafIdx leftRoot attempts counter)
        (maskedOtsSignFrom parameter lay tree leafIdx rightRoot attempts counter)
  | 0, counter => by
      rw [maskedOtsSignFrom, maskedOtsSignFrom]
      exact rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom, maskedOtsSignFrom]
      apply (rootEncodingPermissiveRelates_encode parameter target leftRoot rightRoot
        ⟨lay, tree, leafIdx⟩ counter hposition).bind
      intro leftEncoded rightEncoded hencoded
      subst rightEncoded
      cases leftEncoded with
      | none =>
          exact rootEncodingPermissiveRelates_maskedOtsSignFrom parameter target leftRoot
            rightRoot lay tree leafIdx hposition attempts (counter + 1)
      | some encoding =>
          exact (rootEncodingPermissiveCouples_sequenceFin parameter target leftRoot rightRoot
            (fun chainIdx => ensureChainPrefix lay tree leafIdx chainIdx (encoding chainIdx))
            (fun chainIdx => by
              unfold ensureChainPrefix
              apply (rootEncodingPermissiveCouples_sequenceFin parameter target leftRoot
                rightRoot _ fun step => by
                  by_cases hstep : step.val < (encoding chainIdx).val
                  · rw [if_pos hstep]
                    exact rootEncodingPermissiveCouples_ensureCoordinate parameter target
                      leftRoot rightRoot (.position (.chain lay tree leafIdx chainIdx step))
                  · rw [if_neg hstep]
                    exact rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot
                      ()).bind fun _ =>
                        rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot
                          ())).bind fun _ =>
            rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot
              (some (BitVec.ofNat counterBits counter, encoding))

theorem rootEncodingPermissiveRelates_maskedOtsSign
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex)
    (hposition : EncodingPositionNamesRoot target ⟨lay, tree, leafIdx⟩) :
    RootEncodingPermissiveRelates parameter target leftRoot rightRoot
      (maskedOtsSign parameter lay tree leafIdx leftRoot)
      (maskedOtsSign parameter lay tree leafIdx rightRoot) :=
  rootEncodingPermissiveRelates_maskedOtsSignFrom parameter target leftRoot rightRoot lay tree
    leafIdx hposition encodingAttemptLimit 0

theorem rootEncodingPermissiveCouples_ensureFullChain
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (rootEncodingPermissiveCouples_sequenceFin parameter target leftRoot rightRoot _
    fun step => rootEncodingPermissiveCouples_ensureCoordinate parameter target leftRoot rightRoot
      (.position (.chain lay tree leafIdx chainIdx step))).bind fun _ =>
        rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot ()

theorem rootEncodingPermissiveCouples_ensureOtsLeaf
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (rootEncodingPermissiveCouples_sequenceFin parameter target leftRoot rightRoot _
    fun chainIdx => rootEncodingPermissiveCouples_ensureFullChain parameter target leftRoot
      rightRoot lay tree leafIdx chainIdx).bind fun _ =>
        rootEncodingPermissiveCouples_ensureCoordinate parameter target leftRoot rightRoot
          (.position (.leaf lay tree leafIdx))

theorem rootEncodingPermissiveCouples_ensureTreeNode
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex) : ∀ level nodeIdx,
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => by
      rw [ensureTreeNode]
      exact rootEncodingPermissiveCouples_ensureOtsLeaf parameter target leftRoot rightRoot lay
        tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (rootEncodingPermissiveCouples_ensureTreeNode parameter target leftRoot rightRoot lay
        tree level (2 * nodeIdx)).bind fun _ =>
          (rootEncodingPermissiveCouples_ensureTreeNode parameter target leftRoot rightRoot lay
            tree level (2 * nodeIdx + 1)).bind fun _ => by
              by_cases hlevel : level < maxLayerHeight
              · rw [dif_pos hlevel]
                exact rootEncodingPermissiveCouples_ensureCoordinate parameter target leftRoot
                  rightRoot (.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)))
              · rw [dif_neg hlevel]
                exact rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot ()

theorem rootEncodingPermissiveCouples_ensureTreePath
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (rootEncodingPermissiveCouples_sequenceFin parameter target leftRoot rightRoot _
    fun level => by
      by_cases hlevel : level.val < layerHeight lay
      · rw [if_pos hlevel]
        exact rootEncodingPermissiveCouples_ensureTreeNode parameter target leftRoot rightRoot lay
          tree level.val (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
      · rw [if_neg hlevel]
        exact rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot ()).bind
          fun _ => rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot ()

theorem rootEncodingPermissiveCouples_revealPublishedCoordinate
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (coordinate : Coordinate) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (rootEncodingPermissiveCouples_revealCoordinate parameter target leftRoot rightRoot
    coordinate).bind fun _ =>
      (rootEncodingPermissiveCouples_publishCoordinate parameter target leftRoot rightRoot
        coordinate).bind fun _ =>
          rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot _

theorem rootEncodingPermissiveCouples_revealLayerValues
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  apply (rootEncodingPermissiveCouples_sequenceFin parameter target leftRoot rightRoot _
    fun chainIdx => rootEncodingPermissiveCouples_revealPublishedCoordinate parameter target
      leftRoot rightRoot
        (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
          (encoding chainIdx))).bind
  intro values
  apply (rootEncodingPermissiveCouples_sequenceFin parameter target leftRoot rightRoot _
    fun level => by
      by_cases hlevel : level.val < layerHeight lay
      · rw [if_pos hlevel]
        cases hzero : level.val with
        | zero =>
            exact rootEncodingPermissiveCouples_revealPublishedCoordinate parameter target
              leftRoot rightRoot (.position (.leaf lay (treeIndexAt index lay)
                (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
        | succ current =>
            rw [Nat.add_one]
            simp only
            by_cases hcurrent : current < maxLayerHeight
            · rw [dif_pos hcurrent]
              exact rootEncodingPermissiveCouples_revealPublishedCoordinate parameter target
                leftRoot rightRoot (.position (.node lay (treeIndexAt index lay)
                  ⟨current, hcurrent⟩
                  (leafOfNat (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
            · rw [dif_neg hcurrent]
              exact rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot 0
      · rw [if_neg hlevel]
        exact rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot 0).bind
  intro path
  exact rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot (values, path)

theorem rootEncodingPermissiveCouples_tweakableHash_of_not_encoding
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (domain : HashDomain) (payload : HashInput)
    (hinRange : domain.InRange)
    (hnotEncoding : ∀ lay tree leafIdx, domain ≠ .encoding lay tree leafIdx) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl (tweakableHash parameter domain payload)) := by
  unfold tweakableHash oracleHash
  simp only [simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_spec_query,
    simulateQ_pure]
  exact (rootEncodingPermissiveCouples_splitHashQuery_same_nonroot parameter target leftRoot
    rightRoot (.ordinary (tweakableHashInput parameter domain payload))
    (not_encodingInputNamesRoot_tweakableHashInput_of_not_encoding parameter target domain
      payload hinRange hnotEncoding)).bind fun _ =>
        rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot _

theorem rootEncodingPermissiveCouples_ftsLeafHash
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index) (tree : FtsTree)
    (leafIdx : FtsLeaf) (secret : Digest) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl (ftsLeafHash parameter index tree leafIdx secret)) := by
  unfold ftsLeafHash
  exact rootEncodingPermissiveCouples_tweakableHash_of_not_encoding parameter target leftRoot
    rightRoot (.ftsLeaf index tree leafIdx) (digestBytes secret) (by trivial) (by simp)

theorem rootEncodingPermissiveCouples_ftsNode
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) : ∀ level nodeIdx,
    level ≤ ftsTreeHeight →
    2 ^ level * (nodeIdx + 1) ≤ 2 ^ ftsTreeHeight →
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl (ftsNode parameter index tree secret level nodeIdx))
  | 0, nodeIdx, _hlevel, _hspan => by
      rw [ftsNode_zero_eq]
      exact rootEncodingPermissiveCouples_ftsLeafHash parameter target leftRoot rightRoot index
        tree (ftsLeafOfNat nodeIdx) (secret (ftsLeafOfNat nodeIdx))
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
      exact (rootEncodingPermissiveCouples_ftsNode parameter target leftRoot rightRoot index tree
        secret level (2 * nodeIdx) (by omega) hleftSpan).bind fun left =>
          (rootEncodingPermissiveCouples_ftsNode parameter target leftRoot rightRoot index tree
            secret level (2 * nodeIdx + 1) (by omega) hrightSpan).bind fun right =>
              rootEncodingPermissiveCouples_tweakableHash_of_not_encoding parameter target
                leftRoot rightRoot (.ftsNode index tree (level + 1) nodeIdx)
                (nodePayload left right) hinRange (by simp)

theorem rootEncodingPermissiveCouples_ftsKey
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index)
    (secret : FtsTree → FtsLeaf → Digest) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl (ftsKey parameter index secret)) := by
  unfold ftsKey
  rw [simulateQ_bind, simulateQ_ordinaryHashImpl_sequenceFin]
  exact (rootEncodingPermissiveCouples_sequenceFin parameter target leftRoot rightRoot _
    fun tree => rootEncodingPermissiveCouples_ftsNode parameter target leftRoot rightRoot index
      tree (secret tree) ftsTreeHeight 0 le_rfl (by simp)).bind fun roots =>
        rootEncodingPermissiveCouples_tweakableHash_of_not_encoding parameter target leftRoot
          rightRoot (.ftsRoots index) (ftsRootsPayload roots) (by trivial) (by simp)

theorem rootEncodingPermissiveCouples_ftsOpen
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index)
    (leaves : DigestTree → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl (ftsOpen parameter index leaves secret)) := by
  unfold ftsOpen
  rw [simulateQ_ordinaryHashImpl_sequenceFin]
  apply rootEncodingPermissiveCouples_sequenceFin
  intro tree
  rw [simulateQ_ordinaryHashImpl_sequenceFin]
  apply rootEncodingPermissiveCouples_sequenceFin
  intro level
  exact rootEncodingPermissiveCouples_ftsNode parameter target leftRoot rightRoot index tree
    (secret tree) level.val (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)
      (Nat.le_of_lt level.isLt)
      (FtsProbeSimulation.ftsOpen_node_bound (leaves (ftsIndexOf tree)) level)

theorem rootEncodingPermissiveCouples_simulateQ_splitUniformImpl
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (computation : ProbComp α) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (simulateQ splitUniformImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      rw [simulateQ_pure]
      exact rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot value
  | query_bind n next ih =>
      rw [simulateQ_query_bind]
      exact (rootEncodingPermissiveCouples_splitUniformImpl parameter target leftRoot rightRoot
        n).bind fun output => ih output

theorem rootEncodingPermissiveCouples_messageDigest
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (publicRoot : Digest)
    (message : Message) (randomness : Randomness) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl
        (messageDigest parameter publicRoot message randomness)) := by
  unfold messageDigest oracleHash
  simp only [simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_spec_query,
    simulateQ_pure, ordinaryHashImpl]
  exact (rootEncodingPermissiveCouples_splitHashQuery_same_nonroot parameter target leftRoot
    rightRoot (.ordinary (tweakableHashInput parameter .message
      (messageDigestPayload publicRoot message randomness)))
    (not_encodingInputNamesRoot_tweakableHashInput_of_not_encoding parameter target .message
      _ (by trivial) (by simp))).bind fun output =>
        rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot
          (truncateMessageDigest output)

theorem rootEncodingPermissiveCouples_signAttempt
    (target : Position) (leftRoot rightRoot : Digest)
    (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    RootEncodingPermissiveCouples secretKey.parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl (signAttempt secretKey message randomness)) := by
  unfold signAttempt
  simp only [simulateQ_bind]
  exact (rootEncodingPermissiveCouples_messageDigest secretKey.parameter target leftRoot
    rightRoot secretKey.root message randomness).bind fun digest => by
      split <;>
        exact rootEncodingPermissiveCouples_pure secretKey.parameter target leftRoot rightRoot _

theorem rootEncodingPermissiveCouples_signDigestLoop
    (target : Position) (leftRoot rightRoot : Digest)
    (secretKey : SecretKey) (message : Message) : ∀ attempts,
    RootEncodingPermissiveCouples secretKey.parameter target leftRoot rightRoot
      (simulateQ ordinaryRomImpl (signDigestLoop attempts secretKey message))
  | 0 => by
      rw [signDigestLoop, simulateQ_pure]
      exact rootEncodingPermissiveCouples_pure secretKey.parameter target leftRoot rightRoot none
  | attempts + 1 => by
      rw [signDigestLoop, simulateQ_bind]
      have hrandomness : RootEncodingPermissiveCouples secretKey.parameter target leftRoot
          rightRoot (simulateQ ordinaryRomImpl (liftM sampleRandomness)) := by
        rw [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_left]
        exact rootEncodingPermissiveCouples_simulateQ_splitUniformImpl secretKey.parameter target
          leftRoot rightRoot sampleRandomness
      exact hrandomness.bind fun randomness => by
        rw [simulateQ_bind]
        have hattempt : RootEncodingPermissiveCouples secretKey.parameter target leftRoot
            rightRoot (simulateQ ordinaryRomImpl
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))))) := by
          rw [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_right]
          exact rootEncodingPermissiveCouples_signAttempt target leftRoot rightRoot secretKey
            message randomness
        exact hattempt.bind fun attempt => by
          cases attempt with
          | none =>
              exact rootEncodingPermissiveCouples_signDigestLoop target leftRoot rightRoot
                secretKey message attempts
          | some selected =>
              rw [simulateQ_pure]
              exact rootEncodingPermissiveCouples_pure secretKey.parameter target leftRoot
                rightRoot (some (randomness, selected.1, selected.2))

theorem rootEncodingPermissiveCouples_encode_of_not_positionNames
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (position : EncodingPosition)
    (message : Digest) (counter : Nat)
    (hnotPosition : ¬EncodingPositionNamesRoot target position) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl
        (encode parameter position.lay position.tree position.leafIdx message
          (BitVec.ofNat counterBits counter))) := by
  unfold encode tweakableHash oracleHash
  simp only [simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_spec_query,
    simulateQ_pure, ordinaryHashImpl, bind_assoc, pure_bind]
  exact (rootEncodingPermissiveCouples_splitHashQuery_same_nonroot parameter target leftRoot
    rightRoot (.ordinary (encodingRetryInput parameter position message counter))
    (not_encodingInputNamesRoot_encodingRetryInput_of_not_positionNames hnotPosition message
      counter)).bind fun output =>
        rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot
          (TargetSum.decodeDigest (truncateHash output))

theorem rootEncodingPermissiveCouples_maskedOtsSignFrom_of_not_positionNames
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest)
    (hnotPosition : ¬EncodingPositionNamesRoot target ⟨lay, tree, leafIdx⟩) :
    ∀ attempts counter,
      RootEncodingPermissiveCouples parameter target leftRoot rightRoot
        (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => by
      rw [maskedOtsSignFrom]
      exact rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      apply (rootEncodingPermissiveCouples_encode_of_not_positionNames parameter target leftRoot
        rightRoot ⟨lay, tree, leafIdx⟩ message counter hnotPosition).bind
      intro encoded
      cases encoded with
      | none =>
          exact rootEncodingPermissiveCouples_maskedOtsSignFrom_of_not_positionNames parameter
            target leftRoot rightRoot lay tree leafIdx message hnotPosition attempts (counter + 1)
      | some encoding =>
          exact (rootEncodingPermissiveCouples_sequenceFin parameter target leftRoot rightRoot _
            fun chainIdx => by
              unfold ensureChainPrefix
              exact (rootEncodingPermissiveCouples_sequenceFin parameter target leftRoot
                rightRoot _ fun step => by
                  by_cases hstep : step.val < (encoding chainIdx).val
                  · rw [if_pos hstep]
                    exact rootEncodingPermissiveCouples_ensureCoordinate parameter target
                      leftRoot rightRoot (.position (.chain lay tree leafIdx chainIdx step))
                  · rw [if_neg hstep]
                    exact rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot
                      ()).bind fun _ =>
                        rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot
                          ()).bind fun _ =>
                            rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot
                              (some (BitVec.ofNat counterBits counter, encoding))

theorem rootEncodingPermissiveCouples_maskedOtsSign_of_not_positionNames
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest)
    (hnotPosition : ¬EncodingPositionNamesRoot target ⟨lay, tree, leafIdx⟩) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (maskedOtsSign parameter lay tree leafIdx message) :=
  rootEncodingPermissiveCouples_maskedOtsSignFrom_of_not_positionNames parameter target leftRoot
    rightRoot lay tree leafIdx message hnotPosition encodingAttemptLimit 0

theorem rootEncodingPermissiveCouples_maskedOtsLayerAfterMessage_of_not_positionNames
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index) (lay : Layer)
    (message : Digest)
    (hnotPosition : ¬EncodingPositionNamesRoot target
      ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (maskedOtsLayerAfterMessage parameter index lay message) := by
  unfold maskedOtsLayerAfterMessage
  exact (rootEncodingPermissiveCouples_maskedOtsSign_of_not_positionNames parameter target
    leftRoot rightRoot lay (treeIndexAt index lay) (leafIndexAt index lay) message
    hnotPosition).bind fun selected => by
      cases selected with
      | none => exact rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot none
      | some selected =>
          exact (rootEncodingPermissiveCouples_ensureTreePath parameter target leftRoot rightRoot
            lay (treeIndexAt index lay) (leafIndexAt index lay)).bind fun _ =>
              rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot
                (some selected)

theorem rootEncodingPermissiveRelates_maskedOtsLayerAfterMessage
    (parameter : PublicParameter) (index : Index) (lay : Layer)
    (hnotBottom : lay ≠ bottomLayer) (leftRoot rightRoot : Digest) :
    RootEncodingPermissiveRelates parameter (layerMessagePosition index lay) leftRoot rightRoot
      (maskedOtsLayerAfterMessage parameter index lay leftRoot)
      (maskedOtsLayerAfterMessage parameter index lay rightRoot) := by
  have hposition : EncodingPositionNamesRoot (layerMessagePosition index lay)
      ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ :=
    ⟨index, rfl, rfl, hnotBottom, rfl⟩
  unfold maskedOtsLayerAfterMessage
  apply (rootEncodingPermissiveRelates_maskedOtsSign parameter
    (layerMessagePosition index lay) leftRoot rightRoot lay (treeIndexAt index lay)
    (leafIndexAt index lay) hposition).bind
  intro leftSelected rightSelected hselected
  subst rightSelected
  cases leftSelected with
  | none =>
      exact rootEncodingPermissiveCouples_pure parameter (layerMessagePosition index lay)
        leftRoot rightRoot none
  | some selected =>
      exact (rootEncodingPermissiveCouples_ensureTreePath parameter
        (layerMessagePosition index lay) leftRoot rightRoot lay (treeIndexAt index lay)
        (leafIndexAt index lay)).bind fun _ =>
          rootEncodingPermissiveCouples_pure parameter (layerMessagePosition index lay)
            leftRoot rightRoot (some selected)

theorem rootEncodingPermissiveCouples_maskedTreeNode
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex) : ∀ level nodeIdx,
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (maskedTreeNode lay tree level nodeIdx)
  | level, nodeIdx => by
      unfold maskedTreeNode
      apply (rootEncodingPermissiveCouples_ensureTreeNode parameter target leftRoot rightRoot lay
        tree level nodeIdx).bind
      intro _
      cases level with
      | zero =>
          exact rootEncodingPermissiveCouples_revealCoordinate parameter target leftRoot
            rightRoot (.position (.leaf lay tree (leafOfNat nodeIdx)))
      | succ current =>
          rw [Nat.add_one]
          simp only
          by_cases hlevel : current < maxLayerHeight
          · rw [dif_pos hlevel]
            exact rootEncodingPermissiveCouples_revealCoordinate parameter target leftRoot
              rightRoot (.position (.node lay tree ⟨current, hlevel⟩ (leafOfNat nodeIdx)))
          · rw [dif_neg hlevel]
            exact rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot 0

theorem rootEncodingPermissiveCouples_maskedTreeRoot
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (maskedTreeRoot lay tree) :=
  rootEncodingPermissiveCouples_maskedTreeNode parameter target leftRoot rightRoot lay tree
    (layerHeight lay) 0

theorem rootEncodingPermissiveCouples_maskedLayerMessage
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  by_cases hbelow : lay.val + 1 < numLayers
  · rw [dif_pos hbelow]
    exact rootEncodingPermissiveCouples_maskedTreeRoot parameter target leftRoot rightRoot
      ⟨lay.val + 1, hbelow⟩ (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
  · rw [dif_neg hbelow]
    exact rootEncodingPermissiveCouples_ftsKey parameter target leftRoot rightRoot index
      (ftsSecret index)

set_option maxRecDepth 100000 in
theorem storedLayerRoot_of_mem_runPermissiveFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : CleanRunResult α)
    (position : Position) (root : Digest)
    (hroot : StoredLayerRoot state position root)
    (hresult : some result ∈ support
      (runPermissiveFromTable state fuel table computation)) :
    StoredLayerRoot result.state position root := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      simp [runPermissiveFromTable] at hresult
      subst result
      exact hroot
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runPermissiveFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel hroot hrest
      | hashOutput =>
          rw [runPermissiveFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel hroot hrest
      | ensure coordinate =>
          rw [runPermissiveFromTable_ensure_query_bind] at hresult
          exact ih () (state.ensure coordinate) fuel (hroot.ensure coordinate) hresult
      | probe coordinate candidate =>
          rw [runPermissiveFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · exact ih () state remaining hroot (by simpa [hrevealed] using hresult)
              · exact ih () (state.addPending coordinate candidate) remaining
                  (hroot.addPending coordinate candidate) (by simpa [hrevealed] using hresult)
      | peek coordinate =>
          rw [runPermissiveFromTable_peek_query_bind] at hresult
          exact ih (state.values coordinate) state fuel hroot hresult
      | publish coordinate =>
          rw [runPermissiveFromTable_publish_query_bind] at hresult
          exact ih () (state.publish coordinate) fuel (hroot.publish coordinate) hresult
      | reveal coordinate =>
          rw [runPermissiveFromTable_reveal_query_bind] at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              rw [hvalue] at hresult
              exact ih output state fuel hroot hresult
          | none =>
              have hne : coordinate ≠ .position position := by
                intro heq
                subst coordinate
                obtain ⟨stored, hstored, _⟩ := hroot
                rw [hvalue] at hstored
                simp at hstored
              rw [hvalue] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  exact ih (table ⟨lay, tree, leafIdx, chainIdx⟩)
                    (state.materialize (.chainStart lay tree leafIdx chainIdx)
                      (table ⟨lay, tree, leafIdx, chainIdx⟩)) fuel
                    (hroot.materialize_of_ne _ _ hne) hresult
              | position revealedPosition =>
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, hrest⟩ := hresult
                  exact ih output (state.materialize (.position revealedPosition) output) fuel
                    (hroot.materialize_of_ne _ _ hne) hrest

def RootEncodingPermissiveStoredRel
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) :
    Option (CleanRunResult (α × SplitHashCache)) →
      Option (CleanRunResult (α × SplitHashCache)) → Prop
  | some left, some right =>
      RootEncodingPermissiveCleanSameRel parameter target leftRoot rightRoot
        (some left) (some right) ∧ StoredLayerRoot left.state target leftRoot
  | none, none => True
  | _, _ => False

def RootEncodingPermissiveRelatesStored
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftCache rightCache,
    RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache →
    ∀ state fuel table, StoredLayerRoot state target leftRoot →
      RelTriple
        (runPermissiveFromTable state fuel table (left.run leftCache))
        (runPermissiveFromTable state fuel table (right.run rightCache))
        (RootEncodingPermissiveStoredRel parameter target leftRoot rightRoot)

theorem RootEncodingPermissiveRelates.toStored
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest}
    {left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (hrel : RootEncodingPermissiveRelates parameter target leftRoot rightRoot left right) :
    RootEncodingPermissiveRelatesStored parameter target leftRoot rightRoot left right := by
  intro leftCache rightCache hcache state fuel table hstored
  let leftRun := runPermissiveFromTable state fuel table (left.run leftCache)
  have hboth := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support
    (hrel leftCache rightCache hcache state fuel table)
    (fun result => result ∈ support leftRun) (fun result hresult => hresult)
  apply relTriple_post_mono hboth
  intro leftResult rightResult hresult
  rcases hresult with ⟨hrelation, hleftSupport⟩
  cases leftResult with
  | none =>
      cases rightResult with
      | none => trivial
      | some rightResult => simp [RootEncodingPermissiveCleanSameRel] at hrelation
  | some leftResult =>
      cases rightResult with
      | none => simp [RootEncodingPermissiveCleanSameRel] at hrelation
      | some rightResult =>
          exact ⟨hrelation, storedLayerRoot_of_mem_runPermissiveFromTable (left.run leftCache)
            state fuel table leftResult target leftRoot hstored hleftSupport⟩

theorem RootEncodingPermissiveRelatesStored.bind
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {leftNext rightNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hfirst : RootEncodingPermissiveRelatesStored parameter target leftRoot rightRoot left right)
    (hnext : ∀ leftValue rightValue, leftValue = rightValue →
      RootEncodingPermissiveRelatesStored parameter target leftRoot rightRoot
        (leftNext leftValue) (rightNext rightValue)) :
    RootEncodingPermissiveRelatesStored parameter target leftRoot rightRoot
      (left >>= leftNext) (right >>= rightNext) := by
  intro leftCache rightCache hcache state fuel table hstored
  rw [StateT.run_bind, StateT.run_bind, runPermissiveFromTable_bind,
    runPermissiveFromTable_bind]
  apply relTriple_bind (hfirst leftCache rightCache hcache state fuel table hstored)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [RootEncodingPermissiveStoredRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [RootEncodingPermissiveStoredRel] at hresult
      | some rightResult =>
          rcases hresult with
            ⟨⟨hstate, hremaining, htable, hvalue, hnextCache⟩, hnextStored⟩
          simp only
          rw [← hstate, ← hremaining, ← htable, ← hvalue]
          exact hnext leftResult.value.1 leftResult.value.1 rfl leftResult.value.2
            rightResult.value.2 hnextCache leftResult.state leftResult.remaining leftResult.table
              hnextStored

theorem rootEncodingPermissiveRelatesStored_sequenceFin
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) {n : Nat}
    (left right : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index,
      RootEncodingPermissiveRelatesStored parameter target leftRoot rightRoot
        (left index) (right index)) :
    RootEncodingPermissiveRelatesStored parameter target leftRoot rightRoot
      (sequenceFin left) (sequenceFin right) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact (rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot
        Fin.elim0).toStored
  | succ n ih =>
      rw [sequenceFin, sequenceFin]
      exact (hcomponent 0).bind fun leftHead rightHead hhead =>
        (ih (fun index : Fin n => left index.succ) (fun index : Fin n => right index.succ)
          (fun index => hcomponent index.succ)).bind fun leftTail rightTail htail => by
            subst rightHead
            subst rightTail
            exact (rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot
              (Fin.cases leftHead leftTail : Fin (n + 1) → α)).toStored

set_option maxRecDepth 100000 in
theorem maskedTreeRoot_eq_of_stored_permissive
    (lay : Layer) (tree : TreeIndex)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : CleanRunResult (Digest × SplitHashCache)) (root : Digest)
    (hroot : StoredLayerRoot state (layerRootPosition lay tree) root)
    (hresult : some result ∈ support
      (runPermissiveFromTable state fuel table ((maskedTreeRoot lay tree).run cache))) :
    result.value.1 = root ∧ StoredLayerRoot result.state (layerRootPosition lay tree) root := by
  have hpos : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  have hlevel : layerHeight lay - 1 < maxLayerHeight := by
    have hle := layerHeight_le lay
    omega
  unfold maskedTreeRoot at hresult
  rw [show layerHeight lay = (layerHeight lay - 1) + 1 by omega,
    maskedTreeNode, StateT.run_bind, runPermissiveFromTable_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨administrative, hadministrative, hreveal⟩ := hresult
  cases administrative with
  | none => simp at hreveal
  | some administrative =>
      have hmiddleRoot := storedLayerRoot_of_mem_runPermissiveFromTable
        ((ensureTreeNode lay tree (layerHeight lay - 1 + 1) 0).run cache)
        state fuel table administrative (layerRootPosition lay tree) root hroot
        hadministrative
      simp only at hreveal
      rw [dif_pos hlevel] at hreveal
      obtain ⟨output, hstored, htruncate⟩ := hmiddleRoot
      change some result ∈ support
        (runPermissiveFromTable administrative.state administrative.remaining
          administrative.table
          ((revealCoordinate (.position (layerRootPosition lay tree))).run
            administrative.value.2)) at hreveal
      rw [revealCoordinate_run, LazyRevealProbe.revealQuery,
        runPermissiveFromTable_reveal_query_bind, hstored] at hreveal
      simp [runPermissiveFromTable] at hreveal
      subst result
      exact ⟨htruncate, ⟨output, hstored, htruncate⟩⟩

theorem maskedLayerMessage_value_eq_of_stored_permissive
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target) (root : Digest)
    (index : Index) (lay : Layer)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : CleanRunResult (Digest × SplitHashCache))
    (hstored : StoredLayerRoot state target root)
    (htarget : layerMessagePosition index lay = target)
    (hresult : some result ∈ support
      (runPermissiveFromTable state fuel table
        ((maskedLayerMessage parameter ftsSecret index lay).run cache))) :
    result.value.1 = root := by
  obtain ⟨below, hcomputation, hposition⟩ :=
    layerMessage_root_witness_of_isLayerRoot parameter ftsSecret target hroot index lay htarget
  rw [hcomputation] at hresult
  have hstoredRoot : StoredLayerRoot state
      (layerRootPosition below (treeIndexAt index below)) root := by
    rw [← hposition, htarget]
    exact hstored
  exact (maskedTreeRoot_eq_of_stored_permissive below (treeIndexAt index below) state cache fuel
    table result root hstoredRoot hresult).1

theorem rootEncodingPermissiveCouples_maskedSignLayer_of_layerMessagePosition_ne
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer)
    (hne : layerMessagePosition index lay ≠ target) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (rootEncodingPermissiveCouples_maskedLayerMessage parameter target leftRoot rightRoot
    ftsSecret index lay).bind fun message =>
      rootEncodingPermissiveCouples_maskedOtsLayerAfterMessage_of_not_positionNames parameter
        target leftRoot rightRoot index lay message
          (not_encodingPositionNamesRoot_of_layerMessagePosition_ne target index lay hne)

theorem rootEncodingPermissiveRelatesStored_maskedSignLayer_targetComparison
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    RootEncodingPermissiveRelatesStored parameter target leftRoot rightRoot
      (maskedSignLayer parameter ftsSecret index lay)
      (maskedSignLayerWithTargetComparison parameter target rightRoot ftsSecret index lay) := by
  by_cases htarget : layerMessagePosition index lay = target
  · rw [maskedSignLayerWithTargetComparison, if_pos htarget]
    intro leftCache rightCache hcache state fuel table hstored
    unfold maskedSignLayer maskedSignLayerWithComparisonRoot
    change RelTriple
      (runPermissiveFromTable state fuel table
        ((maskedLayerMessage parameter ftsSecret index lay >>= fun message =>
          maskedOtsLayerAfterMessage parameter index lay message).run leftCache))
      (runPermissiveFromTable state fuel table
        ((maskedLayerMessage parameter ftsSecret index lay >>= fun _ =>
          maskedOtsLayerAfterMessage parameter index lay rightRoot).run rightCache)) _
    rw [StateT.run_bind, StateT.run_bind, runPermissiveFromTable_bind,
      runPermissiveFromTable_bind]
    let leftMessageRun := runPermissiveFromTable state fuel table
      ((maskedLayerMessage parameter ftsSecret index lay).run leftCache)
    have hmessages :=
      (rootEncodingPermissiveCouples_maskedLayerMessage parameter target leftRoot rightRoot
        ftsSecret index lay).toStored leftCache rightCache hcache state fuel table hstored
    have hsupported :=
      SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hmessages
        (fun result => result ∈ support leftMessageRun) (fun result hresult => hresult)
    apply relTriple_bind hsupported
    intro leftResult rightResult hresult
    rcases hresult with ⟨hrelation, hleftSupport⟩
    cases leftResult with
    | none =>
        cases rightResult with
        | none => exact relTriple_pure_pure trivial
        | some rightResult => simp [RootEncodingPermissiveStoredRel] at hrelation
    | some leftResult =>
        cases rightResult with
        | none => simp [RootEncodingPermissiveStoredRel] at hrelation
        | some rightResult =>
            rcases hrelation with
              ⟨⟨hstate, hremaining, htable, _hmessage, hnextCache⟩, hnextStored⟩
            have hactual := maskedLayerMessage_value_eq_of_stored_permissive parameter ftsSecret
              target hroot leftRoot index lay state leftCache fuel table leftResult hstored htarget
                hleftSupport
            simp only
            rw [← hstate, ← hremaining, ← htable, hactual]
            rw [← htarget] at hnextCache hnextStored ⊢
            exact (rootEncodingPermissiveRelates_maskedOtsLayerAfterMessage parameter index lay
              (layer_ne_bottom_of_layerMessagePosition_isLayerRoot htarget hroot) leftRoot
              rightRoot).toStored leftResult.value.2 rightResult.value.2 hnextCache leftResult.state
                leftResult.remaining leftResult.table hnextStored
  · rw [maskedSignLayerWithTargetComparison, if_neg htarget]
    exact (rootEncodingPermissiveCouples_maskedSignLayer_of_layerMessagePosition_ne parameter
      target leftRoot rightRoot ftsSecret index lay htarget).toStored

theorem rootEncodingPermissiveRelatesStored_maskedSignLayers_targetComparison
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) :
    RootEncodingPermissiveRelatesStored parameter target leftRoot rightRoot
      (sequenceFin fun lay => maskedSignLayer parameter ftsSecret index lay)
      (maskedSignLayersWithTargetComparison parameter target rightRoot ftsSecret index) := by
  unfold maskedSignLayersWithTargetComparison
  apply rootEncodingPermissiveRelatesStored_sequenceFin
  intro lay
  exact rootEncodingPermissiveRelatesStored_maskedSignLayer_targetComparison parameter target
    hroot leftRoot rightRoot ftsSecret index lay

theorem rootEncodingPermissiveRelatesStored_maskedSignAfterDigest_targetComparison
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    RootEncodingPermissiveRelatesStored parameter target leftRoot rightRoot
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves)
      (maskedSignAfterDigestWithTargetComparison parameter target rightRoot ftsSecret
        randomness index leaves) := by
  unfold maskedSignAfterDigest maskedSignAfterDigestWithTargetComparison
  apply (rootEncodingPermissiveCouples_ftsOpen parameter target leftRoot rightRoot index leaves
    (ftsSecret index)).toStored.bind
  intro leftPath rightPath hpath
  subst rightPath
  apply (rootEncodingPermissiveRelatesStored_maskedSignLayers_targetComparison parameter target
    hroot leftRoot rightRoot ftsSecret index).bind
  intro leftLayers rightLayers hlayers
  subst rightLayers
  cases hparts : traverseOption leftLayers with
  | none =>
      exact (rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot none).toStored
  | some parts =>
      apply (rootEncodingPermissiveCouples_sequenceFin parameter target leftRoot rightRoot
        (fun lay => revealLayerValues index lay (parts lay).2)
        (fun lay => rootEncodingPermissiveCouples_revealLayerValues parameter target leftRoot
          rightRoot index lay (parts lay).2)).toStored.bind
      intro leftRevealed rightRevealed hrevealed
      subst rightRevealed
      let signature : Signature :=
        { randomness := randomness
          ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := leftPath
          counter := fun lay => (parts lay).1
          chainValue := fun lay => (leftRevealed lay).1
          authPath := flattenPaths fun lay => (leftRevealed lay).2 }
      exact (rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot
        (some signature)).toStored

theorem rootEncodingPermissiveRelatesStored_maskedSign_targetComparison
    (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    RootEncodingPermissiveRelatesStored parameter target leftRoot rightRoot
      (maskedSign parameter publicRoot ftsSecret message)
      (maskedSignWithTargetComparison parameter publicRoot target rightRoot ftsSecret message) := by
  unfold maskedSign maskedSignWithTargetComparison
  let secretKey : SecretKey :=
    ⟨parameter, publicRoot, fun _ _ _ _ => 0, ftsSecret⟩
  apply (rootEncodingPermissiveCouples_signDigestLoop target leftRoot rightRoot secretKey message
    digestAttemptLimit).toStored.bind
  intro leftSelected rightSelected hselected
  subst rightSelected
  cases leftSelected with
  | none =>
      exact (rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot none).toStored
  | some selected =>
      exact rootEncodingPermissiveRelatesStored_maskedSignAfterDigest_targetComparison parameter
        target hroot leftRoot rightRoot ftsSecret selected.1 selected.2.1 selected.2.2

theorem rootEncodingPermissiveCouples_probe
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (candidate : Probe) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (probe candidate) := by
  intro leftCache rightCache hcache state fuel table
  unfold probe LazyRevealProbe.probeQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runPermissiveFromTable_probe_query_bind, runPermissiveFromTable_probe_query_bind]
  cases fuel with
  | zero => exact relTriple_pure_pure trivial
  | succ remaining =>
      by_cases hrevealed : candidate.coordinate ∈ state.revealed
      · simp only [hrevealed, ↓reduceIte, runPermissiveFromTable,
          OracleComp.construct_pure]
        exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩
      · simp only [hrevealed, ↓reduceIte, runPermissiveFromTable,
          OracleComp.construct_pure]
        exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem rootEncodingPermissiveCouples_executeCandidate
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (candidate : Option Probe) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (executeCandidate? candidate) := by
  cases candidate with
  | none =>
      simp only [executeCandidate?]
      exact rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot ()
  | some candidate =>
      simp only [executeCandidate?]
      exact rootEncodingPermissiveCouples_probe parameter target leftRoot rightRoot candidate

theorem rootEncodingPermissiveCouples_splitHashQuery_avoids
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput)
    (havoid : RootInputAvoids parameter target leftRoot rightRoot input) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (splitHashQuery (.ordinary input)) := by
  intro leftCache rightCache hcache state fuel table
  have hlookup := hcache.lookup_avoids input havoid
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  cases hleftLookup : leftCache (.ordinary input) with
  | some output =>
      have hrightLookup : rightCache (.ordinary input) = some output := by
        rw [← hlookup]
        exact hleftLookup
      simp only [hrightLookup, runPermissiveFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩
  | none =>
      have hrightLookup : rightCache (.ordinary input) = none := by
        rw [← hlookup]
        exact hleftLookup
      simp only [hrightLookup]
      unfold LazyRevealProbe.hashOutputQuery
      rw [runPermissiveFromTable_hashOutput_query_bind,
        runPermissiveFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput houtput
      subst rightOutput
      simp only [runPermissiveFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
        hcache.update_same_avoids input havoid leftOutput⟩

theorem rootEncodingPermissiveCouples_revealCoordinateOutput
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (coordinate : Coordinate) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (revealCoordinateOutput coordinate) := by
  intro leftCache rightCache hcache state fuel table
  rw [revealCoordinateOutput_run_eq, revealCoordinateOutput_run_eq,
    LazyRevealProbe.revealQuery, runPermissiveFromTable_reveal_query_bind,
    runPermissiveFromTable_reveal_query_bind]
  have hhidden : ¬RootEncodingKey parameter target (.hidden coordinate) :=
    not_rootEncodingKey_hidden parameter target coordinate
  cases hvalue : state.values coordinate with
  | some output =>
      simp only [runPermissiveFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
        hcache.update_same_nonroot (.hidden coordinate) output hhidden⟩
  | none =>
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          simp only [runPermissiveFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
            hcache.update_same_nonroot
              (.hidden (.chainStart lay tree leafIdx chainIdx))
              (table ⟨lay, tree, leafIdx, chainIdx⟩) hhidden⟩
      | position position =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput houtput
          subst rightOutput
          simp only [runPermissiveFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
            hcache.update_same_nonroot (.hidden (.position position)) leftOutput hhidden⟩

theorem rootEncodingPermissiveCouples_modifyOrdinary_avoids
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput)
    (havoid : RootInputAvoids parameter target leftRoot rightRoot input)
    (output : HashOutput) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (modify fun cache : SplitHashCache =>
        Function.update cache (.ordinary input) (some output)) := by
  intro leftCache rightCache hcache state fuel table
  simp only [StateT.run_modify, runPermissiveFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
    hcache.update_same_avoids input havoid output⟩

theorem rootEncodingPermissiveCouples_resolvePublicKnownInput_avoids
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (publicState : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (input : HashInput)
    (havoid : RootInputAvoids parameter target leftRoot rightRoot input) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (resolvePublicKnownInput parameter publicState coordinate input) := by
  unfold resolvePublicKnownInput
  cases hknown : purePeekTableInput parameter publicState coordinate with
  | none =>
      exact rootEncodingPermissiveCouples_splitHashQuery_avoids parameter target leftRoot
        rightRoot input havoid
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        exact (rootEncodingPermissiveCouples_revealCoordinateOutput parameter target leftRoot
          rightRoot coordinate).bind fun output =>
            (rootEncodingPermissiveCouples_publishCoordinate parameter target leftRoot rightRoot
              coordinate).bind fun _ =>
                (rootEncodingPermissiveCouples_modifyOrdinary_avoids parameter target leftRoot
                  rightRoot input havoid output).bind fun _ =>
                    rootEncodingPermissiveCouples_pure parameter target leftRoot rightRoot output
      · simp only [heq, ↓reduceIte]
        exact rootEncodingPermissiveCouples_splitHashQuery_avoids parameter target leftRoot
          rightRoot input havoid

theorem rootEncodingPermissiveCouples_probingHashQueryAfterPublicPlan_avoids
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (havoid : RootInputAvoids parameter target leftRoot rightRoot input) :
    RootEncodingPermissiveCouples parameter target leftRoot rightRoot
      (probingHashQueryAfterPublicPlan parameter input publicState plan) := by
  unfold probingHashQueryAfterPublicPlan
  exact (rootEncodingPermissiveCouples_executeCandidate parameter target leftRoot rightRoot
    plan.candidate?).bind fun _ => by
      cases plan.action with
      | ordinary =>
          exact rootEncodingPermissiveCouples_splitHashQuery_avoids parameter target leftRoot
            rightRoot input havoid
      | resolve coordinate =>
          exact rootEncodingPermissiveCouples_resolvePublicKnownInput_avoids parameter target
            leftRoot rightRoot publicState coordinate input havoid

end SphincsSecurity.Concrete.OtsProbeSimulation
