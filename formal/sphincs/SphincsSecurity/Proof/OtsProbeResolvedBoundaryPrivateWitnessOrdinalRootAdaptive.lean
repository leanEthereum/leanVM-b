import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSigner

/-!
# Adaptive layer-root cache relation

The root cache quotient pairs signer inputs carrying the actual and comparison roots. Earlier
adversarial inputs carrying any other digest remain equal at their exact keys. If an earlier input
carries either distinguished root, it is the corresponding first-hit event instead.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def EncodingInputGuessesRoot
    (parameter : PublicParameter) (target : Position)
    (guess : Digest) (input : HashInput) : Prop :=
  decodeEncodingLayerRootCandidate? parameter input =
    some ⟨.position target, guess⟩

def RootEncodingWrongCacheRel
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (left right : SplitHashCache) : Prop :=
  ∀ input guess, EncodingInputGuessesRoot parameter target guess input →
    guess ≠ leftRoot → guess ≠ rightRoot →
      left (.ordinary input) = right (.ordinary input)

theorem RootEncodingWrongCacheRel.refl
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (cache : SplitHashCache) :
    RootEncodingWrongCacheRel parameter target leftRoot rightRoot cache cache := by
  intro input guess hguess hleft hright
  rfl

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

theorem RootEncodingWrongCacheRel.update_retry
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingWrongCacheRel parameter target leftRoot rightRoot left right)
    (position : EncodingPosition) (counter : Nat)
    (hposition : EncodingPositionNamesRoot target position)
    (output : HashOutput) :
    RootEncodingWrongCacheRel parameter target leftRoot rightRoot
      (Function.update left
        (.ordinary (encodingRetryInput parameter position leftRoot counter)) (some output))
      (Function.update right
        (.ordinary (encodingRetryInput parameter position rightRoot counter)) (some output)) := by
  intro input guess hguess hleft hright
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
    hrel input guess hguess hleft hright]

theorem RootEncodingWrongCacheRel.update_same
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingWrongCacheRel parameter target leftRoot rightRoot left right)
    (key : SplitHashKey) (output : HashOutput) :
    RootEncodingWrongCacheRel parameter target leftRoot rightRoot
      (Function.update left key (some output))
      (Function.update right key (some output)) := by
  intro input guess hguess hleft hright
  by_cases heq : SplitHashKey.ordinary input = key
  · simp [heq]
  · simp [Function.update_of_ne heq, hrel input guess hguess hleft hright]

def RootEncodingFullCacheRel
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (left right : SplitHashCache) : Prop :=
  RootEncodingCacheRel parameter target leftRoot rightRoot left right ∧
    RootEncodingWrongCacheRel parameter target leftRoot rightRoot left right

theorem RootEncodingFullCacheRel.refl
    (parameter : PublicParameter) (target : Position)
    (root : Digest) (cache : SplitHashCache) :
    RootEncodingFullCacheRel parameter target root root cache cache :=
  ⟨RootEncodingCacheRel.refl parameter target root cache,
    RootEncodingWrongCacheRel.refl parameter target root root cache⟩

theorem RootEncodingFullCacheRel.update_retry
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingFullCacheRel parameter target leftRoot rightRoot left right)
    (position : EncodingPosition) (counter : Nat)
    (hposition : EncodingPositionNamesRoot target position)
    (output : HashOutput) :
    RootEncodingFullCacheRel parameter target leftRoot rightRoot
      (Function.update left
        (.ordinary (encodingRetryInput parameter position leftRoot counter)) (some output))
      (Function.update right
        (.ordinary (encodingRetryInput parameter position rightRoot counter)) (some output)) :=
  ⟨hrel.1.update_retry position counter hposition output,
    hrel.2.update_retry position counter hposition output⟩

theorem RootEncodingFullCacheRel.update_same_nonroot
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingFullCacheRel parameter target leftRoot rightRoot left right)
    (key : SplitHashKey) (output : HashOutput)
    (hkey : ¬RootEncodingKey parameter target key) :
    RootEncodingFullCacheRel parameter target leftRoot rightRoot
      (Function.update left key (some output))
      (Function.update right key (some output)) :=
  ⟨hrel.1.update_same_nonroot key output hkey, hrel.2.update_same key output⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
