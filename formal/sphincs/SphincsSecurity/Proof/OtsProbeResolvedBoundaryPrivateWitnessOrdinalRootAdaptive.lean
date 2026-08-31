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

theorem relTriple_splitHashQuery_same_avoids
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput)
    (havoid : RootInputAvoids parameter target leftRoot rightRoot input)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runCleanFromTable state fuel table ((splitHashQuery (.ordinary input)).run leftCache))
      (runCleanFromTable state fuel table ((splitHashQuery (.ordinary input)).run rightCache))
      (RootEncodingCleanSameRel parameter target leftRoot rightRoot) := by
  have hlookup := hcache.lookup_avoids input havoid
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
        hcache.update_same_avoids input havoid leftOutput⟩

theorem rootEncodingCacheCouples_modifyOrdinary_avoids
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput)
    (havoid : RootInputAvoids parameter target leftRoot rightRoot input)
    (output : HashOutput) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (modify fun cache : SplitHashCache =>
        Function.update cache (.ordinary input) (some output)) := by
  intro leftCache rightCache hcache state fuel table
  simp only [StateT.run_modify, runCleanFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl,
    hcache.update_same_avoids input havoid output⟩

theorem rootEncodingCacheCouples_resolveKnownInput_avoids
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (coordinate : Coordinate) (input : HashInput)
    (havoid : RootInputAvoids parameter target leftRoot rightRoot input) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (resolveKnownInput parameter coordinate input) := by
  unfold resolveKnownInput
  apply (rootEncodingCacheCouples_peekTableInput parameter target leftRoot rightRoot
    coordinate).bind
  intro knownInput
  cases knownInput with
  | none =>
      intro leftCache rightCache hcache state fuel table
      exact relTriple_splitHashQuery_same_avoids parameter target leftRoot rightRoot input havoid
        leftCache rightCache hcache state fuel table
  | some knownInput =>
      simp only
      by_cases heq : knownInput = input
      · rw [if_pos heq]
        apply (rootEncodingCacheCouples_revealCoordinateOutput parameter target leftRoot rightRoot
          coordinate).bind
        intro output
        exact (rootEncodingCacheCouples_publishCoordinate parameter target leftRoot rightRoot
          coordinate).bind fun _ =>
            (rootEncodingCacheCouples_modifyOrdinary_avoids parameter target leftRoot rightRoot
              input havoid output).bind fun _ =>
                rootEncodingCacheCouples_pure parameter target leftRoot rightRoot output
      · rw [if_neg heq]
        intro leftCache rightCache hcache state fuel table
        exact relTriple_splitHashQuery_same_avoids parameter target leftRoot rightRoot input havoid
          leftCache rightCache hcache state fuel table

theorem rootEncodingCacheCouples_executeCandidate
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (candidate? : Option Probe) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (executeCandidate? candidate?) := by
  cases candidate? with
  | none =>
      simp only [executeCandidate?]
      exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot ()
  | some candidate =>
      simp only [executeCandidate?]
      exact rootEncodingCacheCouples_probe parameter target leftRoot rightRoot candidate

theorem rootEncodingCacheCouples_probingHashQueryAfterPlan_avoids
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput) (plan : PlannedHashQuery)
    (havoid : RootInputAvoids parameter target leftRoot rightRoot input) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (probingHashQueryAfterPlan parameter input plan) := by
  unfold probingHashQueryAfterPlan executePlannedHashQuery
  apply (rootEncodingCacheCouples_executeCandidate parameter target leftRoot rightRoot
    plan.candidate?).bind
  intro _
  cases plan.action with
  | ordinary =>
      intro leftCache rightCache hcache state fuel table
      exact relTriple_splitHashQuery_same_avoids parameter target leftRoot rightRoot input havoid
        leftCache rightCache hcache state fuel table
  | resolve coordinate =>
      exact rootEncodingCacheCouples_resolveKnownInput_avoids parameter target leftRoot rightRoot
        coordinate input havoid

theorem rootInput_hit_or_avoids
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput) :
    EncodingInputGuessesRoot parameter target leftRoot input ∨
      EncodingInputGuessesRoot parameter target rightRoot input ∨
        RootInputAvoids parameter target leftRoot rightRoot input := by
  by_cases hleft : EncodingInputGuessesRoot parameter target leftRoot input
  · exact Or.inl hleft
  · by_cases hright : EncodingInputGuessesRoot parameter target rightRoot input
    · exact Or.inr (Or.inl hright)
    · exact Or.inr (Or.inr ⟨hleft, hright⟩)

theorem probingHashQueryAfterPlan_root_trichotomy
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput) (plan : PlannedHashQuery) :
    EncodingInputGuessesRoot parameter target leftRoot input ∨
      EncodingInputGuessesRoot parameter target rightRoot input ∨
        RootEncodingCacheRelatesStored parameter target leftRoot rightRoot
          (probingHashQueryAfterPlan parameter input plan)
          (probingHashQueryAfterPlan parameter input plan) := by
  rcases rootInput_hit_or_avoids parameter target leftRoot rightRoot input with
      hleft | hright | hsafe
  · exact Or.inl hleft
  · exact Or.inr (Or.inl hright)
  · exact Or.inr (Or.inr
      ((rootEncodingCacheCouples_probingHashQueryAfterPlan_avoids parameter target leftRoot
        rightRoot input plan hsafe).relates.toStored))

end SphincsSecurity.Concrete.OtsProbeSimulation
