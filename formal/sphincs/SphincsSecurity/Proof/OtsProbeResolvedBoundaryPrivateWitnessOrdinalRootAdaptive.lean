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

theorem encodingInputNamesRoot_of_guessesRoot
    {parameter : PublicParameter} {target : Position}
    {guess : Digest} {input : HashInput}
    (hguess : EncodingInputGuessesRoot parameter target guess input) :
    EncodingInputNamesRoot parameter target input :=
  ⟨⟨.position target, guess⟩, hguess, rfl⟩

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
  refine ⟨?_, ?_, ?_⟩
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

theorem RootEncodingFullCacheRel.update_same_wrong
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingFullCacheRel parameter target leftRoot rightRoot left right)
    (input : HashInput) (guess : Digest)
    (hguess : EncodingInputGuessesRoot parameter target guess input)
    (hleft : guess ≠ leftRoot) (hright : guess ≠ rightRoot)
    (output : HashOutput) :
    RootEncodingFullCacheRel parameter target leftRoot rightRoot
      (Function.update left (.ordinary input) (some output))
      (Function.update right (.ordinary input) (some output)) :=
  ⟨hrel.1.update_same_wrong input guess hguess hleft hright output,
    hrel.2.update_same (.ordinary input) output⟩

theorem RootEncodingFullCacheRel.lookup_guess
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingFullCacheRel parameter target leftRoot rightRoot left right)
    (input : HashInput) (guess : Digest)
    (hguess : EncodingInputGuessesRoot parameter target guess input) :
    guess = leftRoot ∨ guess = rightRoot ∨
      left (.ordinary input) = right (.ordinary input) := by
  by_cases hleft : guess = leftRoot
  · exact Or.inl hleft
  · by_cases hright : guess = rightRoot
    · exact Or.inr (Or.inl hright)
    · exact Or.inr (Or.inr (hrel.2 input guess hguess hleft hright))

def RootEncodingFullCleanSameRel
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) :
    Option (CleanRunResult (α × SplitHashCache)) →
      Option (CleanRunResult (α × SplitHashCache)) → Prop
  | some left, some right =>
      left.state = right.state ∧ left.remaining = right.remaining ∧
        left.table = right.table ∧ left.value.1 = right.value.1 ∧
        RootEncodingFullCacheRel parameter target leftRoot rightRoot left.value.2 right.value.2
  | none, none => True
  | _, _ => False

theorem relTriple_splitHashQuery_same_wrong
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput) (guess : Digest)
    (hguess : EncodingInputGuessesRoot parameter target guess input)
    (hleft : guess ≠ leftRoot) (hright : guess ≠ rightRoot)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingFullCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runCleanFromTable state fuel table ((splitHashQuery (.ordinary input)).run leftCache))
      (runCleanFromTable state fuel table ((splitHashQuery (.ordinary input)).run rightCache))
      (RootEncodingFullCleanSameRel parameter target leftRoot rightRoot) := by
  have hlookup := hcache.2 input guess hguess hleft hright
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  cases hleftLookup : leftCache (.ordinary input) with
  | some output =>
      have hrightLookup : rightCache (.ordinary input) = some output := by
        rw [← hlookup]
        exact hleftLookup
      simp only [hrightLookup, runCleanFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩
  | none =>
      have hrightLookup : rightCache (.ordinary input) = none := by
        rw [← hlookup]
        exact hleftLookup
      simp only [hrightLookup]
      unfold LazyRevealProbe.hashOutputQuery
      rw [runCleanFromTable_hashOutput_query_bind,
        runCleanFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput houtput
      subst rightOutput
      simp only [runCleanFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
        hcache.update_same_wrong input guess hguess hleft hright leftOutput⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
