import SphincsSecurity.Proof.OtsProbeInitializedRootSelection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

def RootEncodingNativeSameRel
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) :
    Option (ResolvedRunResult (α × SplitHashCache)) →
      Option (ResolvedRunResult (α × SplitHashCache)) → Prop
  | some left, some right =>
      left.context = right.context ∧ left.remaining = right.remaining ∧
        left.table = right.table ∧ left.value.1 = right.value.1 ∧
        RootEncodingCacheRel parameter target leftRoot rightRoot left.value.2 right.value.2
  | none, none => True
  | _, _ => False

def RootEncodingNativeCouples
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftCache rightCache,
    RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache →
    ∀ state fuel table,
      RelTriple
        (runResolvedFromTable state fuel table (computation.run leftCache))
        (runResolvedFromTable state fuel table (computation.run rightCache))
        (RootEncodingNativeSameRel parameter target leftRoot rightRoot)

def RootEncodingNativeRelates
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftCache rightCache,
    RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache →
    ∀ state fuel table,
      RelTriple
        (runResolvedFromTable state fuel table (left.run leftCache))
        (runResolvedFromTable state fuel table (right.run rightCache))
        (RootEncodingNativeSameRel parameter target leftRoot rightRoot)

theorem RootEncodingNativeCouples.relates
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest}
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (hcouples : RootEncodingNativeCouples parameter target leftRoot rightRoot computation) :
    RootEncodingNativeRelates parameter target leftRoot rightRoot computation computation :=
  hcouples

theorem rootEncodingNativeCouples_pure
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (value : α) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro leftCache rightCache hcache state fuel table
  simp only [StateT.run_pure, runResolvedFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem rootEncodingNativeCouples_ensureCoordinate
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (coordinate : Coordinate) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (ensureCoordinate coordinate) := by
  intro leftCache rightCache hcache state fuel table
  change RelTriple
    (runResolvedFromTable state fuel table (LazyRevealProbe.ensureQuery coordinate >>= fun value => pure (value, leftCache)))
    (runResolvedFromTable state fuel table (LazyRevealProbe.ensureQuery coordinate >>= fun value => pure (value, rightCache))) _
  rw [LazyRevealProbe.ensureQuery, runResolvedFromTable_ensure_query_bind, runResolvedFromTable_ensure_query_bind]
  simp only [runResolvedFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩


theorem RootEncodingNativeCouples.bind
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : RootEncodingNativeCouples parameter target leftRoot rightRoot left)
    (hnext : ∀ value,
      RootEncodingNativeCouples parameter target leftRoot rightRoot (next value)) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot (left >>= next) := by
  intro leftCache rightCache hcache state fuel table
  rw [StateT.run_bind, StateT.run_bind, runResolvedFromTable_bind,
    runResolvedFromTable_bind]
  apply relTriple_bind (hleft leftCache rightCache hcache state fuel table)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [RootEncodingNativeSameRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [RootEncodingNativeSameRel] at hresult
      | some rightResult =>
          rcases hresult with ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
          simp only
          rw [← hstate, ← hremaining, ← htable, ← hvalue]
          exact hnext leftResult.value.1 leftResult.value.2 rightResult.value.2 hnextCache
            leftResult.context leftResult.remaining leftResult.table


theorem RootEncodingNativeRelates.bind
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {leftNext rightNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hfirst : RootEncodingNativeRelates parameter target leftRoot rightRoot left right)
    (hnext : ∀ leftValue rightValue, leftValue = rightValue →
      RootEncodingNativeRelates parameter target leftRoot rightRoot
        (leftNext leftValue) (rightNext rightValue)) :
    RootEncodingNativeRelates parameter target leftRoot rightRoot
      (left >>= leftNext) (right >>= rightNext) := by
  intro leftCache rightCache hcache state fuel table
  rw [StateT.run_bind, StateT.run_bind, runResolvedFromTable_bind,
    runResolvedFromTable_bind]
  apply relTriple_bind (hfirst leftCache rightCache hcache state fuel table)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [RootEncodingNativeSameRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [RootEncodingNativeSameRel] at hresult
      | some rightResult =>
          rcases hresult with ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
          simp only
          rw [← hstate, ← hremaining, ← htable, ← hvalue]
          exact hnext leftResult.value.1 leftResult.value.1 rfl
            leftResult.value.2 rightResult.value.2 hnextCache
              leftResult.context leftResult.remaining leftResult.table

theorem rootEncodingNativeCouples_sequenceFin
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index,
      RootEncodingNativeCouples parameter target leftRoot rightRoot (computation index)) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact rootEncodingNativeCouples_pure parameter target leftRoot rightRoot Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun _ =>
        (ih (fun index : Fin n => computation index.succ)
          (fun index => hcomponent index.succ)).bind fun _ =>
            rootEncodingNativeCouples_pure parameter target leftRoot rightRoot _

theorem rootEncodingNativeRelates_sequenceFin
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) {n : Nat}
    (left right : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index,
      RootEncodingNativeRelates parameter target leftRoot rightRoot
        (left index) (right index)) :
    RootEncodingNativeRelates parameter target leftRoot rightRoot
      (sequenceFin left) (sequenceFin right) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact (rootEncodingNativeCouples_pure parameter target leftRoot rightRoot Fin.elim0).relates
  | succ n ih =>
      rw [sequenceFin, sequenceFin]
      exact (hcomponent 0).bind fun leftHead rightHead hhead =>
        (ih (fun index : Fin n => left index.succ) (fun index : Fin n => right index.succ)
          (fun index => hcomponent index.succ)).bind fun leftTail rightTail htail => by
            subst rightHead
            subst rightTail
            exact (rootEncodingNativeCouples_pure parameter target leftRoot rightRoot
              (Fin.cases leftHead leftTail : Fin (n + 1) → α)).relates

theorem rootEncodingNativeCouples_ensureChainPrefix
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (rootEncodingNativeCouples_sequenceFin parameter target leftRoot rightRoot _
    fun step => by
      by_cases hstep : step.val < digit.val
      · rw [if_pos hstep]
        exact rootEncodingNativeCouples_ensureCoordinate parameter target leftRoot rightRoot _
      · rw [if_neg hstep]
        exact rootEncodingNativeCouples_pure parameter target leftRoot rightRoot ()).bind fun _ =>
          rootEncodingNativeCouples_pure parameter target leftRoot rightRoot ()


theorem relTriple_native_splitHashQuery_encodingRetryInput
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (position : EncodingPosition) (counter : Nat)
    (hposition : EncodingPositionNamesRoot target position)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runResolvedFromTable state fuel table
        ((splitHashQuery (.ordinary
          (encodingRetryInput parameter position leftRoot counter))).run leftCache))
      (runResolvedFromTable state fuel table
        ((splitHashQuery (.ordinary
          (encodingRetryInput parameter position rightRoot counter))).run rightCache))
      (RootEncodingNativeSameRel parameter target leftRoot rightRoot) := by
  let leftInput := encodingRetryInput parameter position leftRoot counter
  let rightInput := encodingRetryInput parameter position rightRoot counter
  have hlookup := hcache.retry position counter hposition
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  cases hleft : leftCache (.ordinary leftInput) with
  | some output =>
      have hright : rightCache (.ordinary rightInput) = some output := by
        rw [← hlookup]
        exact hleft
      simp only [rightInput, hright]
      simp only [runResolvedFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩
  | none =>
      have hright : rightCache (.ordinary rightInput) = none := by
        rw [← hlookup]
        exact hleft
      simp only [rightInput, hright]
      unfold LazyRevealProbe.hashOutputQuery
      rw [runResolvedFromTable_hashOutput_query_bind,
        runResolvedFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput houtput
      subst rightOutput
      simp only [runResolvedFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
        hcache.update_retry position counter hposition leftOutput⟩


def RootEncodingNativeAttemptRel
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) :
    Option (ResolvedRunResult (Option Encoding × SplitHashCache)) →
      Option (ResolvedRunResult (Option Encoding × SplitHashCache)) → Prop :=
  RootEncodingNativeSameRel parameter target leftRoot rightRoot

theorem relTriple_native_rootEncodingAttemptRun
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (position : EncodingPosition) (counter : Nat)
    (hposition : EncodingPositionNamesRoot target position)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runResolvedFromTable state fuel table
        (rootEncodingAttemptRun parameter position leftRoot counter leftCache))
      (runResolvedFromTable state fuel table
        (rootEncodingAttemptRun parameter position rightRoot counter rightCache))
      (RootEncodingNativeAttemptRel parameter target leftRoot rightRoot) := by
  unfold rootEncodingAttemptRun
  rw [runResolvedFromTable_bind, runResolvedFromTable_bind]
  apply relTriple_bind
    (relTriple_native_splitHashQuery_encodingRetryInput parameter target leftRoot rightRoot position
      counter hposition leftCache rightCache hcache state fuel table)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult =>
          simp [RootEncodingNativeSameRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [RootEncodingNativeSameRel] at hresult
      | some rightResult =>
          rcases hresult with ⟨hstate, hremaining, htable, houtput, hnextCache⟩
          simp only
          rw [← hstate, ← hremaining, ← htable, ← houtput]
          simp only [runResolvedFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hnextCache⟩

theorem relTriple_native_simulateQ_encode_roots
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (position : EncodingPosition) (counter : Nat)
    (hposition : EncodingPositionNamesRoot target position)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runResolvedFromTable state fuel table
        ((simulateQ ordinaryHashImpl
          (encode parameter position.lay position.tree position.leafIdx leftRoot
            (BitVec.ofNat counterBits counter))).run leftCache))
      (runResolvedFromTable state fuel table
        ((simulateQ ordinaryHashImpl
          (encode parameter position.lay position.tree position.leafIdx rightRoot
            (BitVec.ofNat counterBits counter))).run rightCache))
      (RootEncodingNativeSameRel parameter target leftRoot rightRoot) := by
  rw [← rootEncodingAttemptRun_eq_encode parameter position leftRoot counter leftCache,
    ← rootEncodingAttemptRun_eq_encode parameter position rightRoot counter rightCache]
  simpa [RootEncodingNativeAttemptRel, RootEncodingNativeSameRel] using
    (relTriple_native_rootEncodingAttemptRun parameter target leftRoot rightRoot position counter
      hposition leftCache rightCache hcache state fuel table)

theorem rootEncodingNativeRelates_encode
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (position : EncodingPosition) (counter : Nat)
    (hposition : EncodingPositionNamesRoot target position) :
    RootEncodingNativeRelates parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl
        (encode parameter position.lay position.tree position.leafIdx leftRoot
          (BitVec.ofNat counterBits counter)))
      (simulateQ ordinaryHashImpl
        (encode parameter position.lay position.tree position.leafIdx rightRoot
          (BitVec.ofNat counterBits counter))) := by
  intro leftCache rightCache hcache state fuel table
  exact relTriple_native_simulateQ_encode_roots parameter target leftRoot rightRoot position counter
    hposition leftCache rightCache hcache state fuel table

theorem rootEncodingNativeRelates_maskedOtsSignFrom
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex)
    (hposition : EncodingPositionNamesRoot target ⟨lay, tree, leafIdx⟩) :
    ∀ attempts counter,
      RootEncodingNativeRelates parameter target leftRoot rightRoot
        (maskedOtsSignFrom parameter lay tree leafIdx leftRoot attempts counter)
        (maskedOtsSignFrom parameter lay tree leafIdx rightRoot attempts counter)
  | 0, counter => by
      rw [maskedOtsSignFrom, maskedOtsSignFrom]
      exact (rootEncodingNativeCouples_pure parameter target leftRoot rightRoot none).relates
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom, maskedOtsSignFrom]
      apply (rootEncodingNativeRelates_encode parameter target leftRoot rightRoot
        ⟨lay, tree, leafIdx⟩ counter hposition).bind
      intro leftEncoded rightEncoded hencoded
      subst rightEncoded
      cases leftEncoded with
      | none =>
          exact rootEncodingNativeRelates_maskedOtsSignFrom parameter target leftRoot rightRoot
            lay tree leafIdx hposition attempts (counter + 1)
      | some encoding =>
          exact ((rootEncodingNativeCouples_sequenceFin parameter target leftRoot rightRoot
            (fun chainIdx => ensureChainPrefix lay tree leafIdx chainIdx (encoding chainIdx))
            (fun chainIdx => rootEncodingNativeCouples_ensureChainPrefix parameter target
              leftRoot rightRoot lay tree leafIdx chainIdx (encoding chainIdx))).bind fun _ =>
                rootEncodingNativeCouples_pure parameter target leftRoot rightRoot
                  (some (BitVec.ofNat counterBits counter, encoding))).relates

theorem rootEncodingNativeRelates_maskedOtsSign
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex)
    (hposition : EncodingPositionNamesRoot target ⟨lay, tree, leafIdx⟩) :
    RootEncodingNativeRelates parameter target leftRoot rightRoot
      (maskedOtsSign parameter lay tree leafIdx leftRoot)
      (maskedOtsSign parameter lay tree leafIdx rightRoot) :=
  rootEncodingNativeRelates_maskedOtsSignFrom parameter target leftRoot rightRoot lay tree leafIdx
    hposition encodingAttemptLimit 0


end SphincsSecurity.Concrete.OtsProbeSimulation
