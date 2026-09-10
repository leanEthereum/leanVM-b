import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootCache

/-!
# Adaptive layer-root cache relation

The root cache quotient pairs signer inputs carrying the actual and comparison roots. Earlier
adversarial inputs carrying any other digest remain equal at their exact keys. If an earlier input
carries either distinguished root, it is the corresponding first-hit event instead.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem encodingInputNamesRoot_of_guessesRoot
    {parameter : PublicParameter} {target : Position}
    {guess : Digest} {input : HashInput}
    (hguess : EncodingInputGuessesRoot parameter target guess input) :
    EncodingInputNamesRoot parameter target input :=
  ⟨⟨.position target, guess⟩, hguess, rfl⟩

theorem RootEncodingCacheRel.update_same_wrong
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingCacheRel parameter target leftRoot rightRoot left right)
    (input : HashInput) (guess : Digest)
    (hguess : EncodingInputGuessesRoot parameter target guess input)
    (hleft : guess ≠ leftRoot) (hright : guess ≠ rightRoot)
    (output : HashOutput) :
    RootEncodingCacheRel parameter target leftRoot rightRoot
      (Function.update left (.ordinary input) (some output))
      (Function.update right (.ordinary input) (some output)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro other hother
    have hne : SplitHashKey.ordinary other ≠ .ordinary input := by
      intro heq
      apply hother
      have hinput := SplitHashKey.ordinary.inj heq
      rw [hinput]
      exact encodingInputNamesRoot_of_guessesRoot hguess
    simp [Function.update_of_ne hne, hrel.nonroot other hother]
  · intro position counter hposition
    have hleftNe : SplitHashKey.ordinary
        (encodingRetryInput parameter position leftRoot counter) ≠ .ordinary input := by
      intro heq
      have hinput := (SplitHashKey.ordinary.inj heq).symm
      exact hleft (guess_eq_of_encodingRetryInput_eq hposition hinput hguess)
    have hrightNe : SplitHashKey.ordinary
        (encodingRetryInput parameter position rightRoot counter) ≠ .ordinary input := by
      intro heq
      have hinput := (SplitHashKey.ordinary.inj heq).symm
      exact hright (guess_eq_of_encodingRetryInput_eq hposition hinput hguess)
    simp [Function.update_of_ne hleftNe, Function.update_of_ne hrightNe,
      hrel.retry position counter hposition]
  · intro coordinate
    simp [hrel.hidden coordinate]
  · intro other otherGuess hotherGuess hotherLeft hotherRight
    by_cases heq : SplitHashKey.ordinary other = .ordinary input
    · simp [heq]
    · simp [Function.update_of_ne heq,
        hrel.wrong other otherGuess hotherGuess hotherLeft hotherRight]

def RootInputAvoids
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput) : Prop :=
  ¬EncodingInputGuessesRoot parameter target leftRoot input ∧
    ¬EncodingInputGuessesRoot parameter target rightRoot input

def NoEncodingRootGuessCached
    (parameter : PublicParameter) (target : Position)
    (root : Digest) (cache : SplitHashCache) : Prop :=
  ∀ input, EncodingInputGuessesRoot parameter target root input →
    cache (.ordinary input) = none

theorem RootEncodingCacheRel.of_same_of_no_guesses
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (cache : SplitHashCache)
    (hleft : NoEncodingRootGuessCached parameter target leftRoot cache)
    (hright : NoEncodingRootGuessCached parameter target rightRoot cache) :
    RootEncodingCacheRel parameter target leftRoot rightRoot cache cache := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro input hinput
    rfl
  · intro position counter hposition
    rw [hleft (encodingRetryInput parameter position leftRoot counter)
      (decodeEncodingLayerRootCandidate?_encodingRetryInput hposition leftRoot counter)]
    rw [hright (encodingRetryInput parameter position rightRoot counter)
      (decodeEncodingLayerRootCandidate?_encodingRetryInput hposition rightRoot counter)]
  · intro coordinate
    rfl
  · intro input guess hguess hguessLeft hguessRight
    rfl

theorem rootInputAvoids_classify
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest} {input : HashInput}
    (havoid : RootInputAvoids parameter target leftRoot rightRoot input) :
    ¬EncodingInputNamesRoot parameter target input ∨
      ∃ guess, EncodingInputGuessesRoot parameter target guess input ∧
        guess ≠ leftRoot ∧ guess ≠ rightRoot := by
  by_cases hnames : EncodingInputNamesRoot parameter target input
  · obtain ⟨candidate, hdecode, hcoordinate⟩ := hnames
    let guess := candidate.candidate
    have hcandidate : candidate = ⟨.position target, guess⟩ := by
      cases candidate with
      | mk coordinate candidate =>
          simp only at hcoordinate
          subst coordinate
          rfl
    have hguess : EncodingInputGuessesRoot parameter target guess input := by
      unfold EncodingInputGuessesRoot
      rwa [← hcandidate]
    exact Or.inr ⟨guess, hguess,
      fun heq => havoid.1 (heq ▸ hguess),
      fun heq => havoid.2 (heq ▸ hguess)⟩
  · exact Or.inl hnames

theorem RootEncodingCacheRel.lookup_avoids
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingCacheRel parameter target leftRoot rightRoot left right)
    (input : HashInput) (havoid : RootInputAvoids parameter target leftRoot rightRoot input) :
    left (.ordinary input) = right (.ordinary input) := by
  rcases rootInputAvoids_classify havoid with hnonroot | ⟨guess, hguess, hleft, hright⟩
  · exact hrel.nonroot input hnonroot
  · exact hrel.wrong input guess hguess hleft hright

theorem RootEncodingCacheRel.update_same_avoids
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingCacheRel parameter target leftRoot rightRoot left right)
    (input : HashInput) (havoid : RootInputAvoids parameter target leftRoot rightRoot input)
    (output : HashOutput) :
    RootEncodingCacheRel parameter target leftRoot rightRoot
      (Function.update left (.ordinary input) (some output))
      (Function.update right (.ordinary input) (some output)) := by
  rcases rootInputAvoids_classify havoid with hnonroot | ⟨guess, hguess, hleft, hright⟩
  · exact hrel.update_same_nonroot (.ordinary input) output hnonroot
  · exact hrel.update_same_wrong input guess hguess hleft hright output

theorem Probe.exists_atPosition_of_matchesInput
    {parameter : PublicParameter} {input : HashInput} {probe : Probe}
    (hmatch : probe.MatchesInput parameter input) :
    ∃ position, AtPosition parameter input position := by
  rcases probe with ⟨coordinate, candidate⟩
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      obtain ⟨step, _hstep, hinput⟩ := hmatch
      exact ⟨.chain lay tree leafIdx chainIdx step, digestBytes candidate, hinput⟩
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hnext : step.val + 1 < chainLength - 1
          · simp only [Probe.MatchesInput, hnext, ↓reduceDIte] at hmatch
            obtain ⟨nextStep, _hstep, hinput⟩ := hmatch
            exact ⟨.chain lay tree leafIdx chainIdx nextStep, digestBytes candidate, hinput⟩
          · simp only [Probe.MatchesInput, hnext, ↓reduceDIte] at hmatch
            obtain ⟨_hchain, payload, hinput, _hslot⟩ := hmatch
            exact ⟨.leaf lay tree leafIdx, payload, hinput⟩
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp [Probe.MatchesInput] at hmatch

theorem decodeProbe?_eq_none_of_atEncodingPosition
    {parameter : PublicParameter} {input : HashInput}
    {position : EncodingPosition}
    (hencoding : AtEncodingPosition parameter input position) :
    decodeProbe? parameter input = none := by
  rw [decodeProbe?_eq_none_iff]
  intro probe hmatch
  obtain ⟨structuralPosition, hposition⟩ := probe.exists_atPosition_of_matchesInput hmatch
  exact hencoding.not_atPosition structuralPosition hposition

theorem decodePosition?_eq_none_of_atEncodingPosition
    {parameter : PublicParameter} {input : HashInput}
    {position : EncodingPosition}
    (hencoding : AtEncodingPosition parameter input position) :
    decodePosition? parameter input = none := by
  classical
  unfold decodePosition?
  rw [dif_neg]
  rintro ⟨structuralPosition, hposition⟩
  exact hencoding.not_atPosition structuralPosition hposition

end SphincsSecurity.Concrete.OtsProbeSimulation
