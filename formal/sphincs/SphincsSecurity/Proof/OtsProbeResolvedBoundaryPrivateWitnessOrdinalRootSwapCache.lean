import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootFiber

/-!
# Swapping delayed-root cache keys

At the moment a hidden layer root is selected in hindsight, the existing cache may already contain
encoding inputs carrying an arbitrary comparison root. Swapping the two families of canonical retry
keys constructs the comparison cache directly, so the cache quotient needs no earlier-miss premise
for the comparison root.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

structure RootRetryAddress (target : Position) where
  position : EncodingPosition
  counter : Fin encodingAttemptLimit
  names : EncodingPositionNamesRoot target position

def RootRetryAddress.input
    (parameter : PublicParameter) (root : Digest)
    (address : RootRetryAddress target) : HashInput :=
  encodingRetryInput parameter address.position root address.counter.val

theorem rootRetryAddress_unique
    {parameter : PublicParameter} {target : Position} {root : Digest}
    {left right : RootRetryAddress target}
    (heq : left.input parameter root = right.input parameter root) :
    left = right := by
  rcases left with ⟨leftPosition, leftCounter, leftNames⟩
  rcases right with ⟨rightPosition, rightCounter, rightNames⟩
  change encodingRetryInput parameter leftPosition root leftCounter.val =
    encodingRetryInput parameter rightPosition root rightCounter.val at heq
  have hposition : leftPosition = rightPosition := by
    exact atEncodingPosition_unique
      (parameter := parameter)
      (input := encodingRetryInput parameter leftPosition root leftCounter.val)
      ⟨digestBytes root ++ counterBytes
        (BitVec.ofNat counterBits leftCounter.val), rfl⟩
      ⟨digestBytes root ++ counterBytes
        (BitVec.ofNat counterBits rightCounter.val), heq⟩
  subst rightPosition
  have hcounter : leftCounter.val = rightCounter.val :=
    encodingRetryInput_injective_of_lt leftCounter.isLt rightCounter.isLt heq
  have hcounterEq : leftCounter = rightCounter := Fin.ext hcounter
  subst rightCounter
  rfl

noncomputable def rootRetryAddress?
    (parameter : PublicParameter) (target : Position)
    (root : Digest) (input : HashInput) : Option (RootRetryAddress target) := by
  classical
  exact if h : ∃ address : RootRetryAddress target,
      address.input parameter root = input then
    some (Classical.choose h)
  else none

theorem rootRetryAddress?_eq_some_of_input
    (parameter : PublicParameter) (root : Digest)
    (address : RootRetryAddress target) :
    rootRetryAddress? parameter target root (address.input parameter root) = some address := by
  classical
  unfold rootRetryAddress?
  let hexists : ∃ other : RootRetryAddress target,
      other.input parameter root = address.input parameter root := ⟨address, rfl⟩
  rw [dif_pos hexists]
  congr 1
  exact rootRetryAddress_unique (Classical.choose_spec hexists)

theorem rootRetryAddress?_eq_some_spec
    {parameter : PublicParameter} {target : Position}
    {root : Digest} {input : HashInput} {address : RootRetryAddress target}
    (haddress : rootRetryAddress? parameter target root input = some address) :
    address.input parameter root = input := by
  classical
  unfold rootRetryAddress? at haddress
  split at haddress
  next hexists =>
    have heq : Classical.choose hexists = address := Option.some.inj haddress
    rw [← heq]
    exact Classical.choose_spec hexists
  next hnone => simp at haddress

theorem rootRetryAddress?_eq_none_of_not_names
    {parameter : PublicParameter} {target : Position}
    {root : Digest} {input : HashInput}
    (hnot : ¬EncodingInputNamesRoot parameter target input) :
    rootRetryAddress? parameter target root input = none := by
  classical
  unfold rootRetryAddress?
  rw [dif_neg]
  rintro ⟨address, hinput⟩
  apply hnot
  rw [← hinput]
  exact encodingRetryInput_namesRoot address.names root address.counter.val

theorem rootRetryAddress?_eq_none_of_guess_ne
    {parameter : PublicParameter} {target : Position}
    {root guess : Digest} {input : HashInput}
    (hguess : EncodingInputGuessesRoot parameter target guess input)
    (hne : guess ≠ root) :
    rootRetryAddress? parameter target root input = none := by
  classical
  unfold rootRetryAddress?
  rw [dif_neg]
  rintro ⟨address, hinput⟩
  apply hne
  exact guess_eq_of_encodingRetryInput_eq address.names hinput.symm hguess

noncomputable def swapCanonicalRootEncodingInput
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput) : HashInput :=
  match rootRetryAddress? parameter target leftRoot input with
  | some address => address.input parameter rightRoot
  | none =>
      match rootRetryAddress? parameter target rightRoot input with
      | some address => address.input parameter leftRoot
      | none => input

theorem swapCanonicalRootEncodingInput_left
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (address : RootRetryAddress target) :
    swapCanonicalRootEncodingInput parameter target leftRoot rightRoot
        (address.input parameter leftRoot) =
      address.input parameter rightRoot := by
  unfold swapCanonicalRootEncodingInput
  rw [rootRetryAddress?_eq_some_of_input]

theorem swapCanonicalRootEncodingInput_right
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (address : RootRetryAddress target) :
    swapCanonicalRootEncodingInput parameter target leftRoot rightRoot
        (address.input parameter rightRoot) =
      address.input parameter leftRoot := by
  by_cases heq : leftRoot = rightRoot
  · subst rightRoot
    exact swapCanonicalRootEncodingInput_left parameter target leftRoot leftRoot address
  · unfold swapCanonicalRootEncodingInput
    have hguess : EncodingInputGuessesRoot parameter target rightRoot
        (address.input parameter rightRoot) :=
      decodeEncodingLayerRootCandidate?_encodingRetryInput address.names rightRoot
        address.counter.val
    rw [rootRetryAddress?_eq_none_of_guess_ne hguess (Ne.symm heq),
      rootRetryAddress?_eq_some_of_input]

theorem swapCanonicalRootEncodingInput_nonroot
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest} {input : HashInput}
    (hnot : ¬EncodingInputNamesRoot parameter target input) :
    swapCanonicalRootEncodingInput parameter target leftRoot rightRoot input = input := by
  unfold swapCanonicalRootEncodingInput
  rw [rootRetryAddress?_eq_none_of_not_names hnot,
    rootRetryAddress?_eq_none_of_not_names hnot]

theorem swapCanonicalRootEncodingInput_wrong
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot guess : Digest} {input : HashInput}
    (hguess : EncodingInputGuessesRoot parameter target guess input)
    (hleft : guess ≠ leftRoot) (hright : guess ≠ rightRoot) :
    swapCanonicalRootEncodingInput parameter target leftRoot rightRoot input = input := by
  unfold swapCanonicalRootEncodingInput
  rw [rootRetryAddress?_eq_none_of_guess_ne hguess hleft,
    rootRetryAddress?_eq_none_of_guess_ne hguess hright]

theorem swapCanonicalRootEncodingInput_involutive
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput) :
    swapCanonicalRootEncodingInput parameter target rightRoot leftRoot
        (swapCanonicalRootEncodingInput parameter target leftRoot rightRoot input) = input := by
  cases hleft : rootRetryAddress? parameter target leftRoot input with
  | some address =>
      have hinput := rootRetryAddress?_eq_some_spec hleft
      have hfirst : swapCanonicalRootEncodingInput parameter target leftRoot rightRoot input =
          address.input parameter rightRoot := by
        unfold swapCanonicalRootEncodingInput
        rw [hleft]
      rw [hfirst,
        swapCanonicalRootEncodingInput_left parameter target rightRoot leftRoot address]
      exact hinput
  | none =>
      cases hright : rootRetryAddress? parameter target rightRoot input with
      | some address =>
          have hinput := rootRetryAddress?_eq_some_spec hright
          have hfirst : swapCanonicalRootEncodingInput parameter target leftRoot rightRoot input =
              address.input parameter leftRoot := by
            unfold swapCanonicalRootEncodingInput
            rw [hleft, hright]
          rw [hfirst,
            swapCanonicalRootEncodingInput_right parameter target rightRoot leftRoot address]
          exact hinput
      | none =>
          unfold swapCanonicalRootEncodingInput
          rw [hleft, hright, hright, hleft]

noncomputable def swapCanonicalRootEncodingCache
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (cache : SplitHashCache) : SplitHashCache
  | .ordinary input =>
      cache (.ordinary
        (swapCanonicalRootEncodingInput parameter target leftRoot rightRoot input))
  | .hidden coordinate => cache (.hidden coordinate)

theorem swapCanonicalRootEncodingCache_involutive
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (cache : SplitHashCache) :
    swapCanonicalRootEncodingCache parameter target rightRoot leftRoot
        (swapCanonicalRootEncodingCache parameter target leftRoot rightRoot cache) = cache := by
  funext key
  cases key with
  | ordinary input =>
      simp [swapCanonicalRootEncodingCache,
        swapCanonicalRootEncodingInput_involutive]
  | hidden coordinate => rfl

theorem rootEncodingCacheRel_swapCanonical
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (cache : SplitHashCache) :
    RootEncodingCacheRel parameter target leftRoot rightRoot cache
      (swapCanonicalRootEncodingCache parameter target leftRoot rightRoot cache) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro input hnot
    simp [swapCanonicalRootEncodingCache,
      swapCanonicalRootEncodingInput_nonroot hnot]
  · intro position counter hposition
    let reduced : Counter := BitVec.ofNat counterBits counter
    have hreduced : reduced.toNat < encodingAttemptLimit := by
      change reduced.toNat < 2 ^ counterBits
      exact reduced.isLt
    let address : RootRetryAddress target :=
      ⟨position, ⟨reduced.toNat, hreduced⟩, hposition⟩
    have hmod : BitVec.ofNat counterBits reduced.toNat = reduced := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    change cache (.ordinary (encodingRetryInput parameter position leftRoot counter)) =
      cache (.ordinary (swapCanonicalRootEncodingInput parameter target leftRoot rightRoot
        (encodingRetryInput parameter position rightRoot counter)))
    have hleftInput : encodingRetryInput parameter position leftRoot counter =
        address.input parameter leftRoot := by
      unfold RootRetryAddress.input address encodingRetryInput
      rw [hmod]
    have hrightInput : encodingRetryInput parameter position rightRoot counter =
        address.input parameter rightRoot := by
      unfold RootRetryAddress.input address encodingRetryInput
      rw [hmod]
    rw [hleftInput, hrightInput, swapCanonicalRootEncodingInput_right]
  · intro coordinate
    rfl
  · intro input guess hguess hleft hright
    simp [swapCanonicalRootEncodingCache,
      swapCanonicalRootEncodingInput_wrong hguess hleft hright]

end SphincsSecurity.Concrete.OtsProbeSimulation
