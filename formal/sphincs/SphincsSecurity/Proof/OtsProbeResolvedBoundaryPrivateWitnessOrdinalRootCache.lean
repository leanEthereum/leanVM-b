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

theorem not_encodingInputNamesRoot_tweakableHashInput_of_not_encoding
    (parameter : PublicParameter) (target : Position) (domain : HashDomain)
    (payload : HashInput) (hinRange : domain.InRange)
    (hnotEncoding : ∀ lay tree leafIdx, domain ≠ .encoding lay tree leafIdx) :
    ¬EncodingInputNamesRoot parameter target
      (tweakableHashInput parameter domain payload) := by
  intro hnames
  obtain ⟨candidate, hdecode, _hcoordinate⟩ := hnames
  obtain ⟨position, _index, hat, _htree, _hleaf, _hnotBottom, _hcandidate⟩ :=
    (decodeEncodingLayerRootCandidate?_eq_some_iff parameter _ candidate).mp hdecode
  obtain ⟨otherPayload, hinput⟩ := hat
  have hdomain := (tweakableHashInput_injective parameter hinRange
    (by trivial) hinput).1
  exact hnotEncoding position.lay position.tree position.leafIdx hdomain

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

theorem not_encodingInputNamesRoot_encodingRetryInput_of_not_positionNames
    {parameter : PublicParameter} {target : Position}
    {position : EncodingPosition}
    (hnotPosition : ¬EncodingPositionNamesRoot target position)
    (message : Digest) (counter : Nat) :
    ¬EncodingInputNamesRoot parameter target
      (encodingRetryInput parameter position message counter) := by
  intro hnames
  obtain ⟨candidate, hdecode, hcoordinate⟩ := hnames
  obtain ⟨queriedPosition, index, hat, htree, hleaf, hnotBottom, hcandidate⟩ :=
    (decodeEncodingLayerRootCandidate?_eq_some_iff parameter _ candidate).mp hdecode
  have hcurrentAt : AtEncodingPosition parameter
      (encodingRetryInput parameter position message counter) position := by
    exact ⟨digestBytes message ++ counterBytes (BitVec.ofNat counterBits counter), rfl⟩
  have hposition : queriedPosition = position := atEncodingPosition_unique hat hcurrentAt
  subst queriedPosition
  apply hnotPosition
  refine ⟨index, htree, hleaf, hnotBottom, ?_⟩
  subst candidate
  simp only at hcoordinate
  exact Coordinate.position.inj hcoordinate.symm

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

theorem RootEncodingCacheRel.lookup_nonroot
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingCacheRel parameter target leftRoot rightRoot left right)
    (key : SplitHashKey) (hkey : ¬RootEncodingKey parameter target key) :
    left key = right key := by
  cases key with
  | ordinary input => exact hrel.1 input hkey
  | hidden coordinate => exact hrel.2.2 coordinate

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

theorem RootEncodingCacheRel.update_same_nonroot
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingCacheRel parameter target leftRoot rightRoot left right)
    (key : SplitHashKey) (output : HashOutput)
    (hkey : ¬RootEncodingKey parameter target key) :
    RootEncodingCacheRel parameter target leftRoot rightRoot
      (Function.update left key (some output))
      (Function.update right key (some output)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro input hinput
    by_cases heq : SplitHashKey.ordinary input = key
    · simp [heq]
    · simp [Function.update_of_ne heq, hrel.nonroot input hinput]
  · intro position counter hposition
    have hleftRoot : RootEncodingKey parameter target
        (.ordinary (encodingRetryInput parameter position leftRoot counter)) :=
      encodingRetryInput_namesRoot (parameter := parameter) hposition leftRoot counter
    have hrightRoot : RootEncodingKey parameter target
        (.ordinary (encodingRetryInput parameter position rightRoot counter)) :=
      encodingRetryInput_namesRoot (parameter := parameter) hposition rightRoot counter
    have hleftNe : SplitHashKey.ordinary
        (encodingRetryInput parameter position leftRoot counter) ≠ key := by
      intro heq
      exact hkey (heq ▸ hleftRoot)
    have hrightNe : SplitHashKey.ordinary
        (encodingRetryInput parameter position rightRoot counter) ≠ key := by
      intro heq
      exact hkey (heq ▸ hrightRoot)
    simp [Function.update_of_ne hleftNe, Function.update_of_ne hrightNe,
      hrel.retry position counter hposition]
  · intro coordinate
    by_cases heq : SplitHashKey.hidden coordinate = key
    · simp [heq]
    · simp [Function.update_of_ne heq, hrel.hidden coordinate]

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

theorem rootEncodingCacheRelates_sequenceFin
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) {n : Nat}
    (left right : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index,
      RootEncodingCacheRelates parameter target leftRoot rightRoot
        (left index) (right index)) :
    RootEncodingCacheRelates parameter target leftRoot rightRoot
      (sequenceFin left) (sequenceFin right) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact (rootEncodingCacheCouples_pure parameter target leftRoot rightRoot Fin.elim0).relates
  | succ n ih =>
      rw [sequenceFin, sequenceFin]
      exact (hcomponent 0).bind fun leftHead rightHead hhead =>
        (ih (fun index : Fin n => left index.succ) (fun index : Fin n => right index.succ)
          (fun index => hcomponent index.succ)).bind fun leftTail rightTail htail => by
            subst rightHead
            subst rightTail
            exact (rootEncodingCacheCouples_pure parameter target leftRoot rightRoot
              (Fin.cases leftHead leftTail : Fin (n + 1) → α)).relates

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

theorem rootEncodingCacheCouples_ensureFullChain
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (rootEncodingCacheCouples_sequenceFin parameter target leftRoot rightRoot _
    fun step => rootEncodingCacheCouples_ensureCoordinate parameter target leftRoot rightRoot
      (.position (.chain lay tree leafIdx chainIdx step))).bind fun _ =>
        rootEncodingCacheCouples_pure parameter target leftRoot rightRoot ()

theorem rootEncodingCacheCouples_ensureOtsLeaf
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (rootEncodingCacheCouples_sequenceFin parameter target leftRoot rightRoot _
    fun chainIdx => rootEncodingCacheCouples_ensureFullChain parameter target leftRoot rightRoot
      lay tree leafIdx chainIdx).bind fun _ =>
        rootEncodingCacheCouples_ensureCoordinate parameter target leftRoot rightRoot
          (.position (.leaf lay tree leafIdx))

theorem rootEncodingCacheCouples_ensureTreeNode
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx,
      RootEncodingCacheCouples parameter target leftRoot rightRoot
        (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => by
      rw [ensureTreeNode]
      exact rootEncodingCacheCouples_ensureOtsLeaf parameter target leftRoot rightRoot lay tree
        (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (rootEncodingCacheCouples_ensureTreeNode parameter target leftRoot rightRoot lay tree
        level (2 * nodeIdx)).bind fun _ =>
          (rootEncodingCacheCouples_ensureTreeNode parameter target leftRoot rightRoot lay tree
            level (2 * nodeIdx + 1)).bind fun _ => by
              by_cases hlevel : level < maxLayerHeight
              · rw [dif_pos hlevel]
                exact rootEncodingCacheCouples_ensureCoordinate parameter target leftRoot
                  rightRoot (.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)))
              · rw [dif_neg hlevel]
                exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot ()

theorem rootEncodingCacheCouples_ensureTreePath
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (rootEncodingCacheCouples_sequenceFin parameter target leftRoot rightRoot _
    fun level => by
      by_cases hlevel : level.val < layerHeight lay
      · rw [if_pos hlevel]
        exact rootEncodingCacheCouples_ensureTreeNode parameter target leftRoot rightRoot lay tree
          level.val (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
      · rw [if_neg hlevel]
        exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot ()).bind fun _ =>
          rootEncodingCacheCouples_pure parameter target leftRoot rightRoot ()

def RootEncodingCleanQueryRel
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) :
    Option (CleanRunResult (HashOutput × SplitHashCache)) →
      Option (CleanRunResult (HashOutput × SplitHashCache)) → Prop :=
  RootEncodingCleanSameRel parameter target leftRoot rightRoot

theorem relTriple_splitHashQuery_same_nonroot
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (key : SplitHashKey)
    (hkey : ¬RootEncodingKey parameter target key)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runCleanFromTable state fuel table ((splitHashQuery key).run leftCache))
      (runCleanFromTable state fuel table ((splitHashQuery key).run rightCache))
      (RootEncodingCleanSameRel parameter target leftRoot rightRoot) := by
  have hlookup := hcache.lookup_nonroot key hkey
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  cases hleft : leftCache key with
  | some output =>
      have hright : rightCache key = some output := by
        rw [← hlookup]
        exact hleft
      simp only [hright, runCleanFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩
  | none =>
      have hright : rightCache key = none := by
        rw [← hlookup]
        exact hleft
      simp only [hright]
      unfold LazyRevealProbe.hashOutputQuery
      rw [runCleanFromTable_hashOutput_query_bind,
        runCleanFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput houtput
      subst rightOutput
      simp only [runCleanFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
        hcache.update_same_nonroot key leftOutput hkey⟩

theorem rootEncodingCacheCouples_splitHashQuery_same_nonroot
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (key : SplitHashKey)
    (hkey : ¬RootEncodingKey parameter target key) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (splitHashQuery key) := by
  intro leftCache rightCache hcache state fuel table
  exact relTriple_splitHashQuery_same_nonroot parameter target leftRoot rightRoot key hkey
    leftCache rightCache hcache state fuel table

theorem rootEncodingCacheCouples_tweakableHash_of_not_encoding
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (domain : HashDomain) (payload : HashInput)
    (hinRange : domain.InRange)
    (hnotEncoding : ∀ lay tree leafIdx, domain ≠ .encoding lay tree leafIdx) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl (tweakableHash parameter domain payload)) := by
  unfold tweakableHash oracleHash
  simp only [simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_spec_query,
    simulateQ_pure]
  exact (rootEncodingCacheCouples_splitHashQuery_same_nonroot parameter target leftRoot
    rightRoot (.ordinary (tweakableHashInput parameter domain payload))
    (not_encodingInputNamesRoot_tweakableHashInput_of_not_encoding parameter target domain
      payload hinRange hnotEncoding)).bind fun _ =>
        rootEncodingCacheCouples_pure parameter target leftRoot rightRoot _

theorem rootEncodingCacheCouples_ftsLeafHash
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index) (tree : FtsTree)
    (leafIdx : FtsLeaf) (secret : Digest) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl
        (ftsLeafHash parameter index tree leafIdx secret)) := by
  unfold ftsLeafHash
  exact rootEncodingCacheCouples_tweakableHash_of_not_encoding parameter target leftRoot
    rightRoot (.ftsLeaf index tree leafIdx) (digestBytes secret) (by trivial) (by simp)

theorem rootEncodingCacheCouples_ftsNode
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) : ∀ level nodeIdx,
    level ≤ ftsTreeHeight →
    2 ^ level * (nodeIdx + 1) ≤ 2 ^ ftsTreeHeight →
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl
        (ftsNode parameter index tree secret level nodeIdx))
  | 0, nodeIdx, _hlevel, _hspan => by
      rw [ftsNode_zero_eq]
      exact rootEncodingCacheCouples_ftsLeafHash parameter target leftRoot rightRoot index tree
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
      exact (rootEncodingCacheCouples_ftsNode parameter target leftRoot rightRoot index tree
        secret level (2 * nodeIdx) (by omega) hleftSpan).bind fun left =>
          (rootEncodingCacheCouples_ftsNode parameter target leftRoot rightRoot index tree
            secret level (2 * nodeIdx + 1) (by omega) hrightSpan).bind fun right =>
              rootEncodingCacheCouples_tweakableHash_of_not_encoding parameter target leftRoot
                rightRoot (.ftsNode index tree (level + 1) nodeIdx) (nodePayload left right)
                hinRange (by simp)

theorem rootEncodingCacheCouples_ftsKey
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index)
    (secret : FtsTree → FtsLeaf → Digest) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl (ftsKey parameter index secret)) := by
  unfold ftsKey
  rw [simulateQ_bind, simulateQ_ordinaryHashImpl_sequenceFin]
  exact (rootEncodingCacheCouples_sequenceFin parameter target leftRoot rightRoot _
    fun tree => rootEncodingCacheCouples_ftsNode parameter target leftRoot rightRoot index tree
      (secret tree) ftsTreeHeight 0 le_rfl (by simp)).bind fun roots =>
        rootEncodingCacheCouples_tweakableHash_of_not_encoding parameter target leftRoot
          rightRoot (.ftsRoots index) (ftsRootsPayload roots) (by trivial) (by simp)

theorem rootEncodingCacheCouples_revealCoordinate
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (coordinate : Coordinate) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (revealCoordinate coordinate) := by
  intro leftCache rightCache hcache state fuel table
  rw [revealCoordinate_run, revealCoordinate_run, LazyRevealProbe.revealQuery,
    runCleanFromTable_reveal_query_bind, runCleanFromTable_reveal_query_bind]
  have hhidden : ¬RootEncodingKey parameter target (.hidden coordinate) :=
    not_rootEncodingKey_hidden parameter target coordinate
  cases hvalue : state.values coordinate with
  | some output =>
      simp only [runCleanFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
        hcache.update_same_nonroot (.hidden coordinate) output hhidden⟩
  | none =>
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          by_cases hhit : state.hitAt (.chainStart lay tree leafIdx chainIdx)
              (table ⟨lay, tree, leafIdx, chainIdx⟩)
          · simp [hhit, RootEncodingCleanSameRel]
          · simp only [hhit, ↓reduceIte, runCleanFromTable, OracleComp.construct_pure]
            exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
              hcache.update_same_nonroot
                (.hidden (.chainStart lay tree leafIdx chainIdx))
                (table ⟨lay, tree, leafIdx, chainIdx⟩) hhidden⟩
      | position position =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput houtput
          subst rightOutput
          by_cases hhit : state.hitAt (.position position) leftOutput
          · simp [hhit, RootEncodingCleanSameRel]
          · simp only [hhit, ↓reduceIte, runCleanFromTable, OracleComp.construct_pure]
            exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
              hcache.update_same_nonroot (.hidden (.position position)) leftOutput hhidden⟩

theorem rootEncodingCacheCouples_revealPosition
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (position : Position) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (revealPosition position) :=
  rootEncodingCacheCouples_revealCoordinate parameter target leftRoot rightRoot
    (.position position)

theorem rootEncodingCacheCouples_maskedTreeNode
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx,
      RootEncodingCacheCouples parameter target leftRoot rightRoot
        (maskedTreeNode lay tree level nodeIdx)
  | level, nodeIdx => by
      unfold maskedTreeNode
      apply (rootEncodingCacheCouples_ensureTreeNode parameter target leftRoot rightRoot lay tree
        level nodeIdx).bind
      intro _
      cases level with
      | zero =>
          exact rootEncodingCacheCouples_revealPosition parameter target leftRoot rightRoot
            (.leaf lay tree (leafOfNat nodeIdx))
      | succ current =>
          rw [Nat.add_one]
          simp only
          by_cases hlevel : current < maxLayerHeight
          · rw [dif_pos hlevel]
            exact rootEncodingCacheCouples_revealPosition parameter target leftRoot rightRoot
              (.node lay tree ⟨current, hlevel⟩ (leafOfNat nodeIdx))
          · rw [dif_neg hlevel]
            exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot 0

theorem rootEncodingCacheCouples_maskedTreeRoot
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (maskedTreeRoot lay tree) :=
  rootEncodingCacheCouples_maskedTreeNode parameter target leftRoot rightRoot lay tree
    (layerHeight lay) 0

theorem rootEncodingCacheCouples_maskedLayerMessage
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  by_cases hbelow : lay.val + 1 < numLayers
  · rw [dif_pos hbelow]
    exact rootEncodingCacheCouples_maskedTreeRoot parameter target leftRoot rightRoot
      ⟨lay.val + 1, hbelow⟩ (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
  · rw [dif_neg hbelow]
    exact rootEncodingCacheCouples_ftsKey parameter target leftRoot rightRoot index
      (ftsSecret index)

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
      | some rightResult =>
          simp [RootEncodingCleanQueryRel, RootEncodingCleanSameRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [RootEncodingCleanQueryRel, RootEncodingCleanSameRel] at hresult
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

set_option maxHeartbeats 1000000 in
theorem rootEncodingCacheCouples_encode_of_not_positionNames
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (position : EncodingPosition)
    (message : Digest) (counter : Nat)
    (hnotPosition : ¬EncodingPositionNamesRoot target position) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (simulateQ ordinaryHashImpl
        (encode parameter position.lay position.tree position.leafIdx message
          (BitVec.ofNat counterBits counter))) := by
  unfold encode tweakableHash oracleHash
  simp only [simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_spec_query,
    simulateQ_pure, ordinaryHashImpl, bind_assoc, pure_bind]
  exact (rootEncodingCacheCouples_splitHashQuery_same_nonroot parameter target leftRoot
    rightRoot (.ordinary (encodingRetryInput parameter position message counter))
    (not_encodingInputNamesRoot_encodingRetryInput_of_not_positionNames hnotPosition message
      counter)).bind fun output =>
        rootEncodingCacheCouples_pure parameter target leftRoot rightRoot
          (TargetSum.decodeDigest (truncateHash output))

set_option maxHeartbeats 1000000 in
theorem rootEncodingCacheCouples_maskedOtsSignFrom_of_not_positionNames
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest)
    (hnotPosition : ¬EncodingPositionNamesRoot target ⟨lay, tree, leafIdx⟩) :
    ∀ attempts counter,
      RootEncodingCacheCouples parameter target leftRoot rightRoot
        (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => by
      rw [maskedOtsSignFrom]
      exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      apply (rootEncodingCacheCouples_encode_of_not_positionNames parameter target leftRoot
        rightRoot ⟨lay, tree, leafIdx⟩ message counter hnotPosition).bind
      intro encoded
      cases encoded with
      | none =>
          exact rootEncodingCacheCouples_maskedOtsSignFrom_of_not_positionNames parameter target
            leftRoot rightRoot lay tree leafIdx message hnotPosition attempts (counter + 1)
      | some encoding =>
          exact (rootEncodingCacheCouples_sequenceFin parameter target leftRoot rightRoot
            (fun chainIdx => ensureChainPrefix lay tree leafIdx chainIdx (encoding chainIdx))
            (fun chainIdx => rootEncodingCacheCouples_ensureChainPrefix parameter target
              leftRoot rightRoot lay tree leafIdx chainIdx (encoding chainIdx))).bind fun _ =>
                rootEncodingCacheCouples_pure parameter target leftRoot rightRoot
                  (some (BitVec.ofNat counterBits counter, encoding))

theorem rootEncodingCacheCouples_maskedOtsSign_of_not_positionNames
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest)
    (hnotPosition : ¬EncodingPositionNamesRoot target ⟨lay, tree, leafIdx⟩) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (maskedOtsSign parameter lay tree leafIdx message) :=
  rootEncodingCacheCouples_maskedOtsSignFrom_of_not_positionNames parameter target leftRoot
    rightRoot lay tree leafIdx message hnotPosition encodingAttemptLimit 0

theorem rootEncodingCacheCouples_maskedOtsLayerAfterMessage_of_not_positionNames
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index) (lay : Layer)
    (message : Digest)
    (hnotPosition : ¬EncodingPositionNamesRoot target
      ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (maskedOtsLayerAfterMessage parameter index lay message) := by
  unfold maskedOtsLayerAfterMessage
  apply (rootEncodingCacheCouples_maskedOtsSign_of_not_positionNames parameter target leftRoot
    rightRoot lay (treeIndexAt index lay) (leafIndexAt index lay) message hnotPosition).bind
  intro selected
  cases selected with
  | none => exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot none
  | some selected =>
      exact (rootEncodingCacheCouples_ensureTreePath parameter target leftRoot rightRoot lay
        (treeIndexAt index lay) (leafIndexAt index lay)).bind fun _ =>
          rootEncodingCacheCouples_pure parameter target leftRoot rightRoot (some selected)

theorem rootEncodingCacheRelates_maskedOtsLayerAfterMessage
    (parameter : PublicParameter) (index : Index) (lay : Layer)
    (hnotBottom : lay ≠ bottomLayer) (leftRoot rightRoot : Digest) :
    RootEncodingCacheRelates parameter (layerMessagePosition index lay) leftRoot rightRoot
      (maskedOtsLayerAfterMessage parameter index lay leftRoot)
      (maskedOtsLayerAfterMessage parameter index lay rightRoot) := by
  have hposition : EncodingPositionNamesRoot (layerMessagePosition index lay)
      ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ :=
    ⟨index, rfl, rfl, hnotBottom, rfl⟩
  unfold maskedOtsLayerAfterMessage
  apply (rootEncodingCacheRelates_maskedOtsSign parameter (layerMessagePosition index lay)
    leftRoot rightRoot lay (treeIndexAt index lay) (leafIndexAt index lay) hposition).bind
  intro leftSelected rightSelected hselected
  subst rightSelected
  cases leftSelected with
  | none =>
      exact (rootEncodingCacheCouples_pure parameter (layerMessagePosition index lay)
        leftRoot rightRoot none).relates
  | some selected =>
      exact ((rootEncodingCacheCouples_ensureTreePath parameter
        (layerMessagePosition index lay) leftRoot rightRoot lay (treeIndexAt index lay)
        (leafIndexAt index lay)).bind fun _ =>
          rootEncodingCacheCouples_pure parameter (layerMessagePosition index lay)
            leftRoot rightRoot (some selected)).relates

end SphincsSecurity.Concrete.OtsProbeSimulation
