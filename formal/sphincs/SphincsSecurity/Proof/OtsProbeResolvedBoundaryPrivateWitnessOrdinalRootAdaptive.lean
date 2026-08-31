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

theorem RootEncodingCacheRel.lookup_guess
    {parameter : PublicParameter} {target : Position} {leftRoot rightRoot : Digest}
    {left right : SplitHashCache}
    (hrel : RootEncodingCacheRel parameter target leftRoot rightRoot left right)
    (input : HashInput) (guess : Digest)
    (hguess : EncodingInputGuessesRoot parameter target guess input) :
    guess = leftRoot ∨ guess = rightRoot ∨
      left (.ordinary input) = right (.ordinary input) := by
  by_cases hleft : guess = leftRoot
  · exact Or.inl hleft
  · by_cases hright : guess = rightRoot
    · exact Or.inr (Or.inl hright)
    · exact Or.inr (Or.inr (hrel.wrong input guess hguess hleft hright))

theorem relTriple_splitHashQuery_same_wrong
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput) (guess : Digest)
    (hguess : EncodingInputGuessesRoot parameter target guess input)
    (hleft : guess ≠ leftRoot) (hright : guess ≠ rightRoot)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runCleanFromTable state fuel table ((splitHashQuery (.ordinary input)).run leftCache))
      (runCleanFromTable state fuel table ((splitHashQuery (.ordinary input)).run rightCache))
      (RootEncodingCleanSameRel parameter target leftRoot rightRoot) := by
  have hlookup := hcache.wrong input guess hguess hleft hright
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

theorem splitHashQuery_root_guess_trichotomy
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput) (guess : Digest)
    (hguess : EncodingInputGuessesRoot parameter target guess input)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    guess = leftRoot ∨ guess = rightRoot ∨
      RelTriple
        (runCleanFromTable state fuel table ((splitHashQuery (.ordinary input)).run leftCache))
        (runCleanFromTable state fuel table ((splitHashQuery (.ordinary input)).run rightCache))
        (RootEncodingCleanSameRel parameter target leftRoot rightRoot) := by
  by_cases hleft : guess = leftRoot
  · exact Or.inl hleft
  · by_cases hright : guess = rightRoot
    · exact Or.inr (Or.inl hright)
    · exact Or.inr (Or.inr
        (relTriple_splitHashQuery_same_wrong parameter target leftRoot rightRoot input guess
          hguess hleft hright leftCache rightCache hcache state fuel table))

end SphincsSecurity.Concrete.OtsProbeSimulation
