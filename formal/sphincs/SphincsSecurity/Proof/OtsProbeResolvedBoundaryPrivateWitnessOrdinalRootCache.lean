import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootEvent

/-!
# Hidden layer-root cache quotient

For one structural layer root, encoding inputs carrying that root are opaque until an outer query
guesses the root. The root-aware probe records exactly that attempt. This module defines the cache
quotient that forgets those opaque ordinary entries and proves its elementary update laws.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def EncodingInputNamesRoot
    (parameter : PublicParameter) (target : Position) (input : HashInput) : Prop :=
  ∃ candidate,
    decodeEncodingLayerRootCandidate? parameter input = some candidate ∧
      candidate.coordinate = .position target

noncomputable instance encodingInputNamesRootDecidable
    (parameter : PublicParameter) (target : Position) :
    DecidablePred (EncodingInputNamesRoot parameter target) :=
  Classical.decPred _

def RootEncodingKey
    (parameter : PublicParameter) (target : Position) : SplitHashKey → Prop
  | .ordinary input => EncodingInputNamesRoot parameter target input
  | .hidden _ => False

noncomputable instance rootEncodingKeyDecidable
    (parameter : PublicParameter) (target : Position) :
    DecidablePred (RootEncodingKey parameter target) :=
  Classical.decPred _

noncomputable def eraseRootEncodingCache
    (parameter : PublicParameter) (target : Position)
    (cache : SplitHashCache) : SplitHashCache :=
  fun key => if RootEncodingKey parameter target key then none else cache key

def RootEncodingCacheEq
    (parameter : PublicParameter) (target : Position)
    (left right : SplitHashCache) : Prop :=
  eraseRootEncodingCache parameter target left =
    eraseRootEncodingCache parameter target right

theorem RootEncodingCacheEq.refl
    (parameter : PublicParameter) (target : Position) (cache : SplitHashCache) :
    RootEncodingCacheEq parameter target cache cache :=
  rfl

theorem RootEncodingCacheEq.symm
    {parameter : PublicParameter} {target : Position} {left right : SplitHashCache}
    (heq : RootEncodingCacheEq parameter target left right) :
    RootEncodingCacheEq parameter target right left :=
  Eq.symm heq

theorem RootEncodingCacheEq.trans
    {parameter : PublicParameter} {target : Position} {left middle right : SplitHashCache}
    (hleft : RootEncodingCacheEq parameter target left middle)
    (hright : RootEncodingCacheEq parameter target middle right) :
    RootEncodingCacheEq parameter target left right :=
  Eq.trans hleft hright

theorem RootEncodingCacheEq.lookup_of_not_root
    {parameter : PublicParameter} {target : Position} {left right : SplitHashCache}
    (heq : RootEncodingCacheEq parameter target left right)
    (key : SplitHashKey) (hkey : ¬RootEncodingKey parameter target key) :
    left key = right key := by
  have hvalue := congrFun heq key
  simpa [eraseRootEncodingCache, hkey] using hvalue

theorem rootEncodingKey_ordinary_iff
    (parameter : PublicParameter) (target : Position) (input : HashInput) :
    RootEncodingKey parameter target (.ordinary input) ↔
      EncodingInputNamesRoot parameter target input := by
  rfl

theorem not_rootEncodingKey_hidden
    (parameter : PublicParameter) (target : Position) (coordinate : Coordinate) :
    ¬RootEncodingKey parameter target (.hidden coordinate) := by
  simp [RootEncodingKey]

theorem eraseRootEncodingCache_update_root
    (parameter : PublicParameter) (target : Position)
    (cache : SplitHashCache) (key : SplitHashKey) (value : Option HashOutput)
    (hkey : RootEncodingKey parameter target key) :
    eraseRootEncodingCache parameter target (Function.update cache key value) =
      eraseRootEncodingCache parameter target cache := by
  funext other
  by_cases hother : other = key
  · subst other
    simp [eraseRootEncodingCache, hkey]
  · by_cases hotherRoot : RootEncodingKey parameter target other
    · simp [eraseRootEncodingCache, hotherRoot]
    · simp [eraseRootEncodingCache, hotherRoot, Function.update_of_ne hother]

theorem RootEncodingCacheEq.update_root_left
    {parameter : PublicParameter} {target : Position} {left right : SplitHashCache}
    (heq : RootEncodingCacheEq parameter target left right)
    (key : SplitHashKey) (value : Option HashOutput)
    (hkey : RootEncodingKey parameter target key) :
    RootEncodingCacheEq parameter target (Function.update left key value) right := by
  unfold RootEncodingCacheEq
  rw [eraseRootEncodingCache_update_root parameter target left key value hkey]
  exact heq

theorem RootEncodingCacheEq.update_root_right
    {parameter : PublicParameter} {target : Position} {left right : SplitHashCache}
    (heq : RootEncodingCacheEq parameter target left right)
    (key : SplitHashKey) (value : Option HashOutput)
    (hkey : RootEncodingKey parameter target key) :
    RootEncodingCacheEq parameter target left (Function.update right key value) :=
  (heq.symm.update_root_left key value hkey).symm

theorem eraseRootEncodingCache_update_nonroot
    (parameter : PublicParameter) (target : Position)
    (cache : SplitHashCache) (key : SplitHashKey) (value : Option HashOutput)
    (hkey : ¬RootEncodingKey parameter target key) :
    eraseRootEncodingCache parameter target (Function.update cache key value) =
      Function.update (eraseRootEncodingCache parameter target cache) key value := by
  funext other
  by_cases hother : other = key
  · subst other
    simp [eraseRootEncodingCache, hkey]
  · by_cases hotherRoot : RootEncodingKey parameter target other
    · simp [eraseRootEncodingCache, hotherRoot, Function.update_of_ne hother]
    · simp [eraseRootEncodingCache, hotherRoot, Function.update_of_ne hother]

theorem RootEncodingCacheEq.update_nonroot
    {parameter : PublicParameter} {target : Position} {left right : SplitHashCache}
    (heq : RootEncodingCacheEq parameter target left right)
    (key : SplitHashKey) (value : Option HashOutput)
    (hkey : ¬RootEncodingKey parameter target key) :
    RootEncodingCacheEq parameter target
      (Function.update left key value) (Function.update right key value) := by
  unfold RootEncodingCacheEq at heq ⊢
  rw [eraseRootEncodingCache_update_nonroot parameter target left key value hkey,
    eraseRootEncodingCache_update_nonroot parameter target right key value hkey, heq]

theorem encodingInputNamesRoot_of_decode
    {parameter : PublicParameter} {target : Position} {input : HashInput}
    {candidate : Probe}
    (hdecode : decodeEncodingLayerRootCandidate? parameter input = some candidate)
    (hcoordinate : candidate.coordinate = .position target) :
    EncodingInputNamesRoot parameter target input :=
  ⟨candidate, hdecode, hcoordinate⟩

theorem rootEncodingKey_of_decode
    {parameter : PublicParameter} {target : Position} {input : HashInput}
    {candidate : Probe}
    (hdecode : decodeEncodingLayerRootCandidate? parameter input = some candidate)
    (hcoordinate : candidate.coordinate = .position target) :
    RootEncodingKey parameter target (.ordinary input) :=
  encodingInputNamesRoot_of_decode hdecode hcoordinate

theorem encodingInputNamesRoot_target_unique
    {parameter : PublicParameter} {input : HashInput} {left right : Position}
    (hleft : EncodingInputNamesRoot parameter left input)
    (hright : EncodingInputNamesRoot parameter right input) :
    left = right := by
  obtain ⟨leftCandidate, hleftDecode, hleftCoordinate⟩ := hleft
  obtain ⟨rightCandidate, hrightDecode, hrightCoordinate⟩ := hright
  have hcandidate : leftCandidate = rightCandidate := by
    rw [hleftDecode] at hrightDecode
    exact Option.some.inj hrightDecode
  subst rightCandidate
  rw [hleftCoordinate] at hrightCoordinate
  exact Coordinate.position.inj hrightCoordinate

theorem encodingInputNamesRoot_isLayerRoot
    {parameter : PublicParameter} {target : Position} {input : HashInput}
    (hnames : EncodingInputNamesRoot parameter target input) :
    IsLayerRoot target := by
  obtain ⟨candidate, hdecode, hcoordinate⟩ := hnames
  obtain ⟨position, hcandidateCoordinate, hroot⟩ :=
    decodeEncodingLayerRootCandidate?_some_isLayerRoot hdecode
  rw [hcoordinate] at hcandidateCoordinate
  have hposition : target = position := Coordinate.position.inj hcandidateCoordinate
  rwa [hposition]

theorem not_encodingInputNamesRoot_of_rootAwareCandidate_ne
    {parameter : PublicParameter} {target : Position} {input : HashInput}
    {plan : PlannedHashQuery} {candidate : Probe}
    (hplan : plan.candidate? = none)
    (hrootAware : rootAwareCandidateForPlan? parameter input plan = some candidate)
    (hne : candidate.coordinate ≠ .position target) :
    ¬EncodingInputNamesRoot parameter target input := by
  intro hnames
  obtain ⟨other, hdecode, hcoordinate⟩ := hnames
  unfold rootAwareCandidateForPlan? at hrootAware
  rw [hplan, hdecode] at hrootAware
  have hcandidate : candidate = other := Option.some.inj hrootAware.symm
  apply hne
  rw [hcandidate, hcoordinate]

def EncodingPositionNamesRoot
    (target : Position) (position : EncodingPosition) : Prop :=
  ∃ index : Index,
    treeIndexAt index position.lay = position.tree ∧
      leafIndexAt index position.lay = position.leafIdx ∧
      position.lay ≠ bottomLayer ∧
      target = layerMessagePosition index position.lay

theorem encodingRetryInput_namesRoot
    {parameter : PublicParameter} {target : Position}
    {position : EncodingPosition} (hposition : EncodingPositionNamesRoot target position)
    (root : Digest) (counter : Nat) :
    EncodingInputNamesRoot parameter target
      (encodingRetryInput parameter position root counter) := by
  obtain ⟨index, htree, hleaf, hnotBottom, htarget⟩ := hposition
  let candidate : Probe := ⟨.position target, root⟩
  refine ⟨candidate, ?_, rfl⟩
  rw [decodeEncodingLayerRootCandidate?_eq_some_iff]
  refine ⟨position, index, ?_, htree, hleaf, hnotBottom, ?_⟩
  · exact ⟨digestBytes root ++ counterBytes (BitVec.ofNat counterBits counter), rfl⟩
  · subst target
    simp [candidate, encodingRetryInput, slotDigest_zero_encodingInput]

def RootEncodingCacheRel
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (left right : SplitHashCache) : Prop :=
  (∀ input, ¬EncodingInputNamesRoot parameter target input →
      left (.ordinary input) = right (.ordinary input)) ∧
  (∀ position counter, EncodingPositionNamesRoot target position →
      left (.ordinary (encodingRetryInput parameter position leftRoot counter)) =
        right (.ordinary (encodingRetryInput parameter position rightRoot counter))) ∧
  ∀ coordinate, left (.hidden coordinate) = right (.hidden coordinate)

theorem RootEncodingCacheRel.refl
    (parameter : PublicParameter) (target : Position) (root : Digest)
    (cache : SplitHashCache) :
    RootEncodingCacheRel parameter target root root cache cache := by
  exact ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

theorem RootEncodingCacheRel.hidden
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingCacheRel parameter target leftRoot rightRoot left right)
    (coordinate : Coordinate) :
    left (.hidden coordinate) = right (.hidden coordinate) :=
  hrel.2.2 coordinate

theorem RootEncodingCacheRel.nonroot
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingCacheRel parameter target leftRoot rightRoot left right)
    (input : HashInput) (hinput : ¬EncodingInputNamesRoot parameter target input) :
    left (.ordinary input) = right (.ordinary input) :=
  hrel.1 input hinput

theorem RootEncodingCacheRel.retry
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingCacheRel parameter target leftRoot rightRoot left right)
    (position : EncodingPosition) (counter : Nat)
    (hposition : EncodingPositionNamesRoot target position) :
    left (.ordinary (encodingRetryInput parameter position leftRoot counter)) =
      right (.ordinary (encodingRetryInput parameter position rightRoot counter)) :=
  hrel.2.1 position counter hposition

theorem encodingRetryInput_corresponding_eq
    {parameter : PublicParameter} {leftRoot rightRoot : Digest}
    {leftPosition rightPosition : EncodingPosition} {leftCounter rightCounter : Nat}
    (heq : encodingRetryInput parameter leftPosition leftRoot leftCounter =
      encodingRetryInput parameter rightPosition leftRoot rightCounter) :
    encodingRetryInput parameter leftPosition rightRoot leftCounter =
      encodingRetryInput parameter rightPosition rightRoot rightCounter := by
  unfold encodingRetryInput at heq ⊢
  have hparts := tweakableHashInput_injective parameter (by trivial) (by trivial) heq
  have hposition : leftPosition = rightPosition := by
    obtain ⟨leftLay, leftTree, leftLeaf⟩ := leftPosition
    obtain ⟨rightLay, rightTree, rightLeaf⟩ := rightPosition
    simp only [EncodingPosition.domain, HashDomain.encoding.injEq] at hparts
    obtain ⟨rfl, rfl, rfl⟩ := hparts.1
    rfl
  subst rightPosition
  have hcounter : counterBytes (BitVec.ofNat counterBits leftCounter) =
      counterBytes (BitVec.ofNat counterBits rightCounter) := by
    obtain ⟨_hroot, hcounter⟩ := List.append_inj hparts.2
      (by simp [digestBytes_length])
    exact hcounter
  rw [hcounter]

theorem RootEncodingCacheRel.update_retry
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingCacheRel parameter target leftRoot rightRoot left right)
    (position : EncodingPosition) (counter : Nat)
    (hposition : EncodingPositionNamesRoot target position)
    (output : HashOutput) :
    RootEncodingCacheRel parameter target leftRoot rightRoot
      (Function.update left
        (.ordinary (encodingRetryInput parameter position leftRoot counter)) (some output))
      (Function.update right
        (.ordinary (encodingRetryInput parameter position rightRoot counter)) (some output)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro input hinput
    have hleftNe : SplitHashKey.ordinary input ≠
        .ordinary (encodingRetryInput parameter position leftRoot counter) := by
      intro heq
      apply hinput
      have hinputEq := SplitHashKey.ordinary.inj heq
      rw [hinputEq]
      exact encodingRetryInput_namesRoot (parameter := parameter) hposition leftRoot counter
    have hrightNe : SplitHashKey.ordinary input ≠
        .ordinary (encodingRetryInput parameter position rightRoot counter) := by
      intro heq
      apply hinput
      have hinputEq := SplitHashKey.ordinary.inj heq
      rw [hinputEq]
      exact encodingRetryInput_namesRoot (parameter := parameter) hposition rightRoot counter
    simp [Function.update_of_ne hleftNe, Function.update_of_ne hrightNe,
      hrel.nonroot input hinput]
  · intro otherPosition otherCounter hotherPosition
    let leftInput := encodingRetryInput parameter otherPosition leftRoot otherCounter
    let rightInput := encodingRetryInput parameter otherPosition rightRoot otherCounter
    let updatedLeft := encodingRetryInput parameter position leftRoot counter
    let updatedRight := encodingRetryInput parameter position rightRoot counter
    by_cases heq : leftInput = updatedLeft
    · have hrightEq : rightInput = updatedRight :=
        encodingRetryInput_corresponding_eq heq
      simp [leftInput, rightInput, updatedLeft, updatedRight, heq, hrightEq]
    · have hrightNe : rightInput ≠ updatedRight := by
        intro hrightEq
        have := encodingRetryInput_corresponding_eq
          (leftRoot := rightRoot) (rightRoot := leftRoot) hrightEq
        exact heq this
      have hold := hrel.retry otherPosition otherCounter hotherPosition
      simp [leftInput, rightInput, updatedLeft, updatedRight,
        Function.update_of_ne, heq, hrightNe, hold]
  · intro coordinate
    simpa using hrel.hidden coordinate

def RootEncodingCleanSameRel
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

def RootEncodingCacheCouples
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftCache rightCache,
    RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache →
    ∀ state fuel table,
      RelTriple
        (runCleanFromTable state fuel table (computation.run leftCache))
        (runCleanFromTable state fuel table (computation.run rightCache))
        (RootEncodingCleanSameRel parameter target leftRoot rightRoot)

def RootEncodingCacheRelates
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftCache rightCache,
    RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache →
    ∀ state fuel table,
      RelTriple
        (runCleanFromTable state fuel table (left.run leftCache))
        (runCleanFromTable state fuel table (right.run rightCache))
        (RootEncodingCleanSameRel parameter target leftRoot rightRoot)

theorem RootEncodingCacheCouples.relates
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest}
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (hcouples : RootEncodingCacheCouples parameter target leftRoot rightRoot computation) :
    RootEncodingCacheRelates parameter target leftRoot rightRoot computation computation :=
  hcouples

theorem rootEncodingCacheCouples_pure
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (value : α) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro leftCache rightCache hcache state fuel table
  simp only [StateT.run_pure, runCleanFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem rootEncodingCacheCouples_ensureCoordinate
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (coordinate : Coordinate) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (ensureCoordinate coordinate) := by
  intro leftCache rightCache hcache state fuel table
  rw [runCleanFromTable_ensureCoordinate, runCleanFromTable_ensureCoordinate]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem RootEncodingCacheCouples.bind
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : RootEncodingCacheCouples parameter target leftRoot rightRoot left)
    (hnext : ∀ value,
      RootEncodingCacheCouples parameter target leftRoot rightRoot (next value)) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot (left >>= next) := by
  intro leftCache rightCache hcache state fuel table
  rw [StateT.run_bind, StateT.run_bind, runCleanFromTable_bind,
    runCleanFromTable_bind]
  apply relTriple_bind (hleft leftCache rightCache hcache state fuel table)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [RootEncodingCleanSameRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [RootEncodingCleanSameRel] at hresult
      | some rightResult =>
          rcases hresult with ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
          simp only
          rw [← hstate, ← hremaining, ← htable, ← hvalue]
          exact hnext leftResult.value.1 leftResult.value.2 rightResult.value.2 hnextCache
            leftResult.state leftResult.remaining leftResult.table

theorem RootEncodingCacheRelates.bind
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {leftNext rightNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hfirst : RootEncodingCacheRelates parameter target leftRoot rightRoot left right)
    (hnext : ∀ leftValue rightValue, leftValue = rightValue →
      RootEncodingCacheRelates parameter target leftRoot rightRoot
        (leftNext leftValue) (rightNext rightValue)) :
    RootEncodingCacheRelates parameter target leftRoot rightRoot
      (left >>= leftNext) (right >>= rightNext) := by
  intro leftCache rightCache hcache state fuel table
  rw [StateT.run_bind, StateT.run_bind, runCleanFromTable_bind,
    runCleanFromTable_bind]
  apply relTriple_bind (hfirst leftCache rightCache hcache state fuel table)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [RootEncodingCleanSameRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [RootEncodingCleanSameRel] at hresult
      | some rightResult =>
          rcases hresult with ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
          simp only
          rw [← hstate, ← hremaining, ← htable, ← hvalue]
          exact hnext leftResult.value.1 leftResult.value.1 rfl
            leftResult.value.2 rightResult.value.2 hnextCache
              leftResult.state leftResult.remaining leftResult.table

theorem rootEncodingCacheCouples_sequenceFin
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index,
      RootEncodingCacheCouples parameter target leftRoot rightRoot (computation index)) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun _ =>
        (ih (fun index : Fin n => computation index.succ)
          (fun index => hcomponent index.succ)).bind fun _ =>
            rootEncodingCacheCouples_pure parameter target leftRoot rightRoot _

theorem rootEncodingCacheCouples_ensureChainPrefix
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (rootEncodingCacheCouples_sequenceFin parameter target leftRoot rightRoot _
    fun step => by
      by_cases hstep : step.val < digit.val
      · rw [if_pos hstep]
        exact rootEncodingCacheCouples_ensureCoordinate parameter target leftRoot rightRoot _
      · rw [if_neg hstep]
        exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot ()).bind fun _ =>
          rootEncodingCacheCouples_pure parameter target leftRoot rightRoot ()

def RootEncodingCleanQueryRel
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) :
    Option (CleanRunResult (HashOutput × SplitHashCache)) →
      Option (CleanRunResult (HashOutput × SplitHashCache)) → Prop
  | some left, some right =>
      left.state = right.state ∧ left.remaining = right.remaining ∧
        left.table = right.table ∧ left.value.1 = right.value.1 ∧
        RootEncodingCacheRel parameter target leftRoot rightRoot left.value.2 right.value.2
  | none, none => True
  | _, _ => False

theorem relTriple_splitHashQuery_encodingRetryInput
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (position : EncodingPosition) (counter : Nat)
    (hposition : EncodingPositionNamesRoot target position)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runCleanFromTable state fuel table
        ((splitHashQuery (.ordinary
          (encodingRetryInput parameter position leftRoot counter))).run leftCache))
      (runCleanFromTable state fuel table
        ((splitHashQuery (.ordinary
          (encodingRetryInput parameter position rightRoot counter))).run rightCache))
      (RootEncodingCleanQueryRel parameter target leftRoot rightRoot) := by
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
      simp only [runCleanFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩
  | none =>
      have hright : rightCache (.ordinary rightInput) = none := by
        rw [← hlookup]
        exact hleft
      simp only [rightInput, hright]
      unfold LazyRevealProbe.hashOutputQuery
      rw [runCleanFromTable_hashOutput_query_bind,
        runCleanFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput houtput
      subst rightOutput
      simp only [runCleanFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
        hcache.update_retry position counter hposition leftOutput⟩

noncomputable def rootEncodingAttemptRun
    (parameter : PublicParameter) (position : EncodingPosition)
    (message : Digest) (counter : Nat) (cache : SplitHashCache) :
    OracleComp (LazyRevealProbe.World Coordinate)
      (Option Encoding × SplitHashCache) := do
  let result ← (splitHashQuery (.ordinary
    (encodingRetryInput parameter position message counter))).run cache
  pure (TargetSum.decodeDigest (truncateHash result.1), result.2)

theorem rootEncodingAttemptRun_eq_encode
    (parameter : PublicParameter) (position : EncodingPosition)
    (message : Digest) (counter : Nat) (cache : SplitHashCache) :
    rootEncodingAttemptRun parameter position message counter cache =
      (simulateQ ordinaryHashImpl
        (encode parameter position.lay position.tree position.leafIdx message
          (BitVec.ofNat counterBits counter))).run cache := by
  unfold rootEncodingAttemptRun encode tweakableHash oracleHash
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    HasQuery.instOfMonadLift_query, simulateQ_spec_query, ordinaryHashImpl,
    encodingRetryInput, EncodingPosition.domain, bind_assoc, pure_bind]

def RootEncodingAttemptRel
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) :
    Option (CleanRunResult (Option Encoding × SplitHashCache)) →
      Option (CleanRunResult (Option Encoding × SplitHashCache)) → Prop :=
  RootEncodingCleanSameRel parameter target leftRoot rightRoot

theorem relTriple_rootEncodingAttemptRun
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (position : EncodingPosition) (counter : Nat)
    (hposition : EncodingPositionNamesRoot target position)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runCleanFromTable state fuel table
        (rootEncodingAttemptRun parameter position leftRoot counter leftCache))
      (runCleanFromTable state fuel table
        (rootEncodingAttemptRun parameter position rightRoot counter rightCache))
      (RootEncodingAttemptRel parameter target leftRoot rightRoot) := by
  unfold rootEncodingAttemptRun
  rw [runCleanFromTable_bind, runCleanFromTable_bind]
  apply relTriple_bind
    (relTriple_splitHashQuery_encodingRetryInput parameter target leftRoot rightRoot position
      counter hposition leftCache rightCache hcache state fuel table)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [RootEncodingCleanQueryRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [RootEncodingCleanQueryRel] at hresult
      | some rightResult =>
          rcases hresult with ⟨hstate, hremaining, htable, houtput, hnextCache⟩
          simp only
          rw [← hstate, ← hremaining, ← htable, ← houtput]
          simp only [runCleanFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hnextCache⟩

theorem relTriple_simulateQ_encode_roots
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (position : EncodingPosition) (counter : Nat)
    (hposition : EncodingPositionNamesRoot target position)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runCleanFromTable state fuel table
        ((simulateQ ordinaryHashImpl
          (encode parameter position.lay position.tree position.leafIdx leftRoot
            (BitVec.ofNat counterBits counter))).run leftCache))
      (runCleanFromTable state fuel table
        ((simulateQ ordinaryHashImpl
          (encode parameter position.lay position.tree position.leafIdx rightRoot
            (BitVec.ofNat counterBits counter))).run rightCache))
      (RootEncodingCleanSameRel parameter target leftRoot rightRoot) := by
  rw [← rootEncodingAttemptRun_eq_encode parameter position leftRoot counter leftCache,
    ← rootEncodingAttemptRun_eq_encode parameter position rightRoot counter rightCache]
  simpa [RootEncodingAttemptRel, RootEncodingCleanSameRel] using
    (relTriple_rootEncodingAttemptRun parameter target leftRoot rightRoot position counter
      hposition leftCache rightCache hcache state fuel table)

theorem rootEncodingCacheRelates_encode
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (position : EncodingPosition) (counter : Nat)
    (hposition : EncodingPositionNamesRoot target position) :
    RootEncodingCacheRelates parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl
        (encode parameter position.lay position.tree position.leafIdx leftRoot
          (BitVec.ofNat counterBits counter)))
      (simulateQ ordinaryHashImpl
        (encode parameter position.lay position.tree position.leafIdx rightRoot
          (BitVec.ofNat counterBits counter))) := by
  intro leftCache rightCache hcache state fuel table
  exact relTriple_simulateQ_encode_roots parameter target leftRoot rightRoot position counter
    hposition leftCache rightCache hcache state fuel table

theorem rootEncodingCacheRelates_maskedOtsSignFrom
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex)
    (hposition : EncodingPositionNamesRoot target ⟨lay, tree, leafIdx⟩) :
    ∀ attempts counter,
      RootEncodingCacheRelates parameter target leftRoot rightRoot
        (maskedOtsSignFrom parameter lay tree leafIdx leftRoot attempts counter)
        (maskedOtsSignFrom parameter lay tree leafIdx rightRoot attempts counter)
  | 0, counter => by
      rw [maskedOtsSignFrom, maskedOtsSignFrom]
      exact (rootEncodingCacheCouples_pure parameter target leftRoot rightRoot none).relates
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom, maskedOtsSignFrom]
      apply (rootEncodingCacheRelates_encode parameter target leftRoot rightRoot
        ⟨lay, tree, leafIdx⟩ counter hposition).bind
      intro leftEncoded rightEncoded hencoded
      subst rightEncoded
      cases leftEncoded with
      | none =>
          exact rootEncodingCacheRelates_maskedOtsSignFrom parameter target leftRoot rightRoot
            lay tree leafIdx hposition attempts (counter + 1)
      | some encoding =>
          exact ((rootEncodingCacheCouples_sequenceFin parameter target leftRoot rightRoot
            (fun chainIdx => ensureChainPrefix lay tree leafIdx chainIdx (encoding chainIdx))
            (fun chainIdx => rootEncodingCacheCouples_ensureChainPrefix parameter target
              leftRoot rightRoot lay tree leafIdx chainIdx (encoding chainIdx))).bind fun _ =>
                rootEncodingCacheCouples_pure parameter target leftRoot rightRoot
                  (some (BitVec.ofNat counterBits counter, encoding))).relates

theorem rootEncodingCacheRelates_maskedOtsSign
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex)
    (hposition : EncodingPositionNamesRoot target ⟨lay, tree, leafIdx⟩) :
    RootEncodingCacheRelates parameter target leftRoot rightRoot
      (maskedOtsSign parameter lay tree leafIdx leftRoot)
      (maskedOtsSign parameter lay tree leafIdx rightRoot) :=
  rootEncodingCacheRelates_maskedOtsSignFrom parameter target leftRoot rightRoot lay tree leafIdx
    hposition encodingAttemptLimit 0

end SphincsSecurity.Concrete.OtsProbeSimulation
