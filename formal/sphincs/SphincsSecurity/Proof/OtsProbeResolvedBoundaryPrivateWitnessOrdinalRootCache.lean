import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.EncodingSelectionCache
import SphincsSecurity.Proof.FtsProbeSimulation
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateRootCandidate

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

theorem not_rootEncodingKey_hidden
    (parameter : PublicParameter) (target : Position) (coordinate : Coordinate) :
    ¬RootEncodingKey parameter target (.hidden coordinate) := by
  simp [RootEncodingKey]

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

theorem decodeEncodingLayerRootCandidate?_encodingRetryInput
    {parameter : PublicParameter} {target : Position}
    {position : EncodingPosition} (hposition : EncodingPositionNamesRoot target position)
    (root : Digest) (counter : Nat) :
    decodeEncodingLayerRootCandidate? parameter
        (encodingRetryInput parameter position root counter) =
      some ⟨.position target, root⟩ := by
  rw [decodeEncodingLayerRootCandidate?_eq_some_iff]
  obtain ⟨index, htree, hleaf, hnotBottom, htarget⟩ := hposition
  refine ⟨position, index, ?_, htree, hleaf, hnotBottom, ?_⟩
  · exact ⟨digestBytes root ++ counterBytes (BitVec.ofNat counterBits counter), rfl⟩
  · subst target
    simp [encodingRetryInput, slotDigest_zero_encodingInput]

def EncodingInputGuessesRoot
    (parameter : PublicParameter) (target : Position)
    (guess : Digest) (input : HashInput) : Prop :=
  decodeEncodingLayerRootCandidate? parameter input =
    some ⟨.position target, guess⟩

theorem guess_eq_of_encodingRetryInput_eq
    {parameter : PublicParameter} {target : Position}
    {position : EncodingPosition} (hposition : EncodingPositionNamesRoot target position)
    {root guess : Digest} {counter : Nat} {input : HashInput}
    (hinput : input = encodingRetryInput parameter position root counter)
    (hguess : EncodingInputGuessesRoot parameter target guess input) :
    guess = root := by
  unfold EncodingInputGuessesRoot at hguess
  rw [hinput, decodeEncodingLayerRootCandidate?_encodingRetryInput hposition root counter]
    at hguess
  exact congrArg Probe.candidate (Option.some.inj hguess.symm)

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

structure RootEncodingCacheRel
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (left right : SplitHashCache) : Prop where
  nonroot : ∀ input, ¬EncodingInputNamesRoot parameter target input →
    left (.ordinary input) = right (.ordinary input)
  retry : ∀ position counter, EncodingPositionNamesRoot target position →
    left (.ordinary (encodingRetryInput parameter position leftRoot counter)) =
      right (.ordinary (encodingRetryInput parameter position rightRoot counter))
  hidden : ∀ coordinate, left (.hidden coordinate) = right (.hidden coordinate)
  wrong : ∀ input guess, EncodingInputGuessesRoot parameter target guess input →
    guess ≠ leftRoot → guess ≠ rightRoot →
      left (.ordinary input) = right (.ordinary input)

theorem RootEncodingCacheRel.lookup_nonroot
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingCacheRel parameter target leftRoot rightRoot left right)
    (key : SplitHashKey) (hkey : ¬RootEncodingKey parameter target key) :
    left key = right key := by
  cases key with
  | ordinary input => exact hrel.nonroot input hkey
  | hidden coordinate => exact hrel.hidden coordinate

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
  refine ⟨?_, ?_, ?_, ?_⟩
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
  · intro input guess hguess hleft hright
    have hleftNe : SplitHashKey.ordinary input ≠
        .ordinary (encodingRetryInput parameter position leftRoot counter) := by
      intro heq
      have hinput := SplitHashKey.ordinary.inj heq
      exact hleft (guess_eq_of_encodingRetryInput_eq hposition hinput hguess)
    have hrightNe : SplitHashKey.ordinary input ≠
        .ordinary (encodingRetryInput parameter position rightRoot counter) := by
      intro heq
      have hinput := SplitHashKey.ordinary.inj heq
      exact hright (guess_eq_of_encodingRetryInput_eq hposition hinput hguess)
    simp [Function.update_of_ne hleftNe, Function.update_of_ne hrightNe,
      hrel.wrong input guess hguess hleft hright]

theorem RootEncodingCacheRel.update_same_nonroot
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingCacheRel parameter target leftRoot rightRoot left right)
    (key : SplitHashKey) (output : HashOutput)
    (hkey : ¬RootEncodingKey parameter target key) :
    RootEncodingCacheRel parameter target leftRoot rightRoot
      (Function.update left key (some output))
      (Function.update right key (some output)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
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
  · intro input guess hguess hleft hright
    by_cases heq : SplitHashKey.ordinary input = key
    · simp [heq]
    · simp [Function.update_of_ne heq, hrel.wrong input guess hguess hleft hright]

theorem peekCoordinate_run_eq
    (coordinate : Coordinate) (cache : SplitHashCache) :
    (peekCoordinate coordinate).run cache = (do
      let output ← LazyRevealProbe.peekQuery coordinate
      pure (truncateHash <$> output, cache)) := by
  simp [peekCoordinate]

theorem revealCoordinateOutput_run_eq
    (coordinate : Coordinate) (cache : SplitHashCache) :
    (revealCoordinateOutput coordinate).run cache = (do
      let output ← LazyRevealProbe.revealQuery coordinate
      pure (output, Function.update cache (.hidden coordinate) (some output))) := by
  simp [revealCoordinateOutput, StateT.run_modify]

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

end SphincsSecurity.Concrete.OtsProbeSimulation
