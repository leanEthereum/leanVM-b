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

theorem rootEncodingCacheCouples_planFirstMissingInputCoordinate
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput) :
    ∀ slot coordinates,
      RootEncodingCacheCouples parameter target leftRoot rightRoot
        (planFirstMissingInputCoordinate input slot coordinates) := by
  intro slot coordinates
  induction coordinates generalizing slot with
  | nil =>
      rw [planFirstMissingInputCoordinate]
      exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot none
  | cons coordinate remaining ih =>
      rw [planFirstMissingInputCoordinate]
      apply (rootEncodingCacheCouples_peekCoordinate parameter target leftRoot rightRoot
        coordinate).bind
      intro value
      cases value with
      | none =>
          exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot
            (some (⟨coordinate, slotDigest slot input⟩ : Probe))
      | some output => exact ih (slot + 1)

theorem rootEncodingCacheCouples_planLeafInputProbe
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (planLeafInputProbe input candidate lay tree leafIdx) := by
  unfold planLeafInputProbe
  apply (rootEncodingCacheCouples_peekCoordinate parameter target leftRoot rightRoot
    candidate.coordinate).bind
  intro value
  cases value with
  | none =>
      exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot (some candidate)
  | some output =>
      exact rootEncodingCacheCouples_planFirstMissingInputCoordinate parameter target leftRoot
        rightRoot input 0 ((Position.leaf lay tree leafIdx).children.map Coordinate.position)

theorem rootEncodingCacheCouples_planProbingHashQuery
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (planProbingHashQuery parameter input) := by
  unfold planProbingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases hposition : decodePosition? parameter input with
      | none =>
          exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot
            (⟨some candidate, .resolve candidate.outputCoordinate⟩ : PlannedHashQuery)
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              apply (rootEncodingCacheCouples_planLeafInputProbe parameter target leftRoot
                rightRoot input candidate lay tree leafIdx).bind
              intro candidate?
              exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot
                (⟨candidate?, .resolve candidate.outputCoordinate⟩ : PlannedHashQuery)
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot
                (⟨some candidate, .resolve candidate.outputCoordinate⟩ : PlannedHashQuery)
  | none =>
      cases hposition : decodePosition? parameter input with
      | none =>
          exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot
            (⟨none, .ordinary⟩ : PlannedHashQuery)
      | some position =>
          cases position with
          | chain lay tree leafIdx chainIdx step =>
              exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot
                (⟨none, .resolve (.position (.chain lay tree leafIdx chainIdx step))⟩ :
                  PlannedHashQuery)
          | leaf lay tree leafIdx =>
              exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot
                (⟨none, .resolve (.position (.leaf lay tree leafIdx))⟩ : PlannedHashQuery)
          | node lay tree level nodeIdx =>
              apply (rootEncodingCacheCouples_planFirstMissingInputCoordinate parameter target
                leftRoot rightRoot input 0
                ((Position.node lay tree level nodeIdx).children.map Coordinate.position)).bind
              intro candidate?
              exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot
                (⟨candidate?, .resolve (.position (.node lay tree level nodeIdx))⟩ :
                  PlannedHashQuery)
          | ftsLeaf | ftsNode | ftsRoots =>
              exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot
                (⟨none, .ordinary⟩ : PlannedHashQuery)

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

theorem rootEncodingCacheCouples_probingHashQuery_avoids
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput)
    (havoid : RootInputAvoids parameter target leftRoot rightRoot input) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (probingHashQuery parameter input) := by
  have hcoupled : RootEncodingCacheCouples parameter target leftRoot rightRoot (do
      let plan ← planProbingHashQuery parameter input
      probingHashQueryAfterPlan parameter input plan) :=
    (rootEncodingCacheCouples_planProbingHashQuery parameter target leftRoot rightRoot input).bind
      fun plan => rootEncodingCacheCouples_probingHashQueryAfterPlan_avoids parameter target
        leftRoot rightRoot input plan havoid
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases hposition : decodePosition? parameter input with
      | none =>
          rw [probingHashQuery_eq_plan_then_afterPlan_of_probe_some_nonleaf parameter input
            candidate hprobe (by
              rintro ⟨lay, tree, leafIdx, heq⟩
              simp [hposition] at heq)]
          exact hcoupled
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              rw [probingHashQuery_eq_plan_then_afterPlan_leaf parameter input candidate lay tree
                leafIdx hprobe hposition]
              exact hcoupled
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              rw [probingHashQuery_eq_plan_then_afterPlan_of_probe_some_nonleaf parameter input
                candidate hprobe (by
                  rintro ⟨lay, tree, leafIdx, heq⟩
                  simp [hposition] at heq)]
              exact hcoupled
  | none =>
      cases hposition : decodePosition? parameter input with
      | none =>
          rw [probingHashQuery_eq_plan_then_afterPlan_of_probe_none_nonnode parameter input hprobe
            (by
              rintro ⟨lay, tree, level, nodeIdx, heq⟩
              simp [hposition] at heq)]
          exact hcoupled
      | some position =>
          cases position with
          | node lay tree level nodeIdx =>
              rw [probingHashQuery_eq_plan_then_afterPlan_node parameter input lay tree level
                nodeIdx hprobe hposition]
              exact hcoupled
          | chain | leaf | ftsLeaf | ftsNode | ftsRoots =>
              rw [probingHashQuery_eq_plan_then_afterPlan_of_probe_none_nonnode parameter input
                hprobe (by
                  rintro ⟨lay, tree, level, nodeIdx, heq⟩
                  simp [hposition] at heq)]
              exact hcoupled

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

noncomputable def maskedComparisonSigningImpl
    (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (comparisonRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    QueryImpl SigningSpec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))) :=
  fun message =>
    maskedSignWithTargetComparison parameter publicRoot target comparisonRoot ftsSecret message

noncomputable def maskedExpandedAdversaryImplWithTargetComparison
    (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (comparisonRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))) :=
  probingRomImpl parameter +
    maskedComparisonSigningImpl parameter publicRoot target comparisonRoot ftsSecret

def ExpandedQueryGuessesRoot
    (parameter : PublicParameter) (target : Position) (root : Digest)
    (query : (OracleWorld + SigningSpec).Domain) : Prop :=
  ∃ input, query = .inl (.inr input) ∧
    EncodingInputGuessesRoot parameter target root input

def ExpandedQueryAvoidsRoots
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (query : (OracleWorld + SigningSpec).Domain) : Prop :=
  match query with
  | .inl (.inr input) => RootInputAvoids parameter target leftRoot rightRoot input
  | _ => True

theorem not_expandedQueryGuessesRoot_of_avoids
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest}
    {query : (OracleWorld + SigningSpec).Domain}
    (havoid : ExpandedQueryAvoidsRoots parameter target leftRoot rightRoot query) :
    ¬ExpandedQueryGuessesRoot parameter target leftRoot query ∧
      ¬ExpandedQueryGuessesRoot parameter target rightRoot query := by
  cases query with
  | inl worldQuery =>
      cases worldQuery with
      | inl n => simp [ExpandedQueryGuessesRoot]
      | inr input =>
          constructor
          · rintro ⟨otherInput, heq, hguess⟩
            cases heq
            exact havoid.1 hguess
          · rintro ⟨otherInput, heq, hguess⟩
            cases heq
            exact havoid.2 hguess
  | inr message => simp [ExpandedQueryGuessesRoot]

theorem maskedExpandedAdversaryImpl_step_root_trichotomy
    (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain) :
    ExpandedQueryGuessesRoot parameter target leftRoot query ∨
      ExpandedQueryGuessesRoot parameter target rightRoot query ∨
        RootEncodingCacheRelatesStored parameter target leftRoot rightRoot
          (maskedExpandedAdversaryImpl parameter publicRoot ftsSecret query)
          (maskedExpandedAdversaryImplWithTargetComparison parameter publicRoot target rightRoot
            ftsSecret query) := by
  cases query with
  | inl worldQuery =>
      cases worldQuery with
      | inl n =>
          exact Or.inr (Or.inr
            ((rootEncodingCacheCouples_splitUniformImpl parameter target leftRoot rightRoot
              n).relates.toStored))
      | inr input =>
          rcases rootInput_hit_or_avoids parameter target leftRoot rightRoot input with
              hleft | hright | hsafe
          · exact Or.inl ⟨input, rfl, hleft⟩
          · exact Or.inr (Or.inl ⟨input, rfl, hright⟩)
          · exact Or.inr (Or.inr
              ((rootEncodingCacheCouples_probingHashQuery_avoids parameter target leftRoot
                rightRoot input hsafe).relates.toStored))
  | inr message =>
      exact Or.inr (Or.inr
        (rootEncodingCacheRelatesStored_maskedSign_targetComparison parameter publicRoot target
          hroot leftRoot rightRoot ftsSecret message))

theorem rootEncodingCacheRelatesStored_maskedExpandedAdversaryImpl_of_avoids
    (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain)
    (havoid : ExpandedQueryAvoidsRoots parameter target leftRoot rightRoot query) :
    RootEncodingCacheRelatesStored parameter target leftRoot rightRoot
      (maskedExpandedAdversaryImpl parameter publicRoot ftsSecret query)
      (maskedExpandedAdversaryImplWithTargetComparison parameter publicRoot target rightRoot
        ftsSecret query) := by
  have hnot := not_expandedQueryGuessesRoot_of_avoids havoid
  rcases maskedExpandedAdversaryImpl_step_root_trichotomy parameter publicRoot target hroot
      leftRoot rightRoot ftsSecret query with hleft | hright | hsafe
  · exact False.elim (hnot.1 hleft)
  · exact False.elim (hnot.2 hright)
  · exact hsafe

noncomputable def rootAvoidingComputation
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    OracleComp (OracleWorld + SigningSpec) (Option α) := by
  classical
  exact OracleComp.construct
    (C := fun _ => OracleComp (OracleWorld + SigningSpec) (Option α))
    (fun value => pure (some value))
    (fun query _next recursivelyRun =>
      if ExpandedQueryAvoidsRoots parameter target leftRoot rightRoot query then do
        let output ← liftM ((OracleWorld + SigningSpec).query query)
        recursivelyRun output
      else pure none)
    computation

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem rootEncodingCacheRelatesStored_simulateQ_rootAvoidingComputation
    (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    RootEncodingCacheRelatesStored parameter target leftRoot rightRoot
      (simulateQ (maskedExpandedAdversaryImpl parameter publicRoot ftsSecret)
        (rootAvoidingComputation parameter target leftRoot rightRoot computation))
      (simulateQ (maskedExpandedAdversaryImplWithTargetComparison parameter publicRoot target
          rightRoot ftsSecret)
        (rootAvoidingComputation parameter target leftRoot rightRoot computation)) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      rw [rootAvoidingComputation, OracleComp.construct_pure, simulateQ_pure, simulateQ_pure]
      exact ((rootEncodingCacheCouples_pure parameter target leftRoot rightRoot
        (some value)).relates).toStored
  | query_bind query next ih =>
      rw [rootAvoidingComputation, OracleComp.construct_query_bind]
      by_cases hsafe : ExpandedQueryAvoidsRoots parameter target leftRoot rightRoot query
      · rw [if_pos hsafe, simulateQ_query_bind, simulateQ_query_bind]
        apply (rootEncodingCacheRelatesStored_maskedExpandedAdversaryImpl_of_avoids parameter
          publicRoot target hroot leftRoot rightRoot ftsSecret query hsafe).bind
        intro leftOutput rightOutput houtput
        subst rightOutput
        exact ih leftOutput
      · rw [if_neg hsafe, simulateQ_pure, simulateQ_pure]
        exact ((rootEncodingCacheCouples_pure parameter target leftRoot rightRoot none).relates).toStored

theorem rootAwarePlannedCandidate_root_plan_or_encodingGuess
    {parameter : PublicParameter} {input : HashInput}
    {state : LazyRevealProbe.State Coordinate} {candidate : Probe}
    {target : Position}
    (hcandidate : rootAwarePlannedCandidate? parameter input state = some candidate)
    (hcoordinate : candidate.coordinate = .position target) :
    (purePlanProbingHashQuery parameter input state).candidate? = some candidate ∨
      EncodingInputGuessesRoot parameter target candidate.candidate input := by
  unfold rootAwarePlannedCandidate? at hcandidate
  cases hplan : (purePlanProbingHashQuery parameter input state).candidate? with
  | some planned =>
      simp only [hplan] at hcandidate
      have heq : planned = candidate := Option.some.inj hcandidate
      subst candidate
      exact Or.inl rfl
  | none =>
      simp only [hplan] at hcandidate
      right
      unfold EncodingInputGuessesRoot
      cases candidate with
      | mk coordinate candidateDigest =>
          simp only at hcoordinate ⊢
          subst coordinate
          exact hcandidate

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

theorem rootAwarePlannedCandidate?_eq_some_of_encodingInputGuessesRoot
    {parameter : PublicParameter} {target : Position} {root : Digest}
    {input : HashInput} (state : LazyRevealProbe.State Coordinate)
    (hguess : EncodingInputGuessesRoot parameter target root input) :
    rootAwarePlannedCandidate? parameter input state =
      some ⟨.position target, root⟩ := by
  have hdecode : decodeEncodingLayerRootCandidate? parameter input =
      some ⟨.position target, root⟩ := hguess
  have hcandidate :=
    (decodeEncodingLayerRootCandidate?_eq_some_iff parameter input
      ⟨.position target, root⟩).mp hdecode
  obtain ⟨position, index, hencoding, _htree, _hleaf, _hlayer, _hcandidate⟩ := hcandidate
  have hprobe := decodeProbe?_eq_none_of_atEncodingPosition hencoding
  have hposition := decodePosition?_eq_none_of_atEncodingPosition hencoding
  unfold rootAwarePlannedCandidate? purePlanProbingHashQuery
  rw [hprobe, hposition]
  exact hdecode

def RootAwareCandidateAvoidsRoots
    (target : Position) (leftRoot rightRoot : Digest)
    (candidate? : Option Probe) : Prop :=
  candidate? ≠ some ⟨.position target, leftRoot⟩ ∧
    candidate? ≠ some ⟨.position target, rightRoot⟩

theorem rootInputAvoids_of_rootAwareCandidateAvoidsRoots
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest} {input : HashInput}
    {state : LazyRevealProbe.State Coordinate}
    (havoid : RootAwareCandidateAvoidsRoots target leftRoot rightRoot
      (rootAwarePlannedCandidate? parameter input state)) :
    RootInputAvoids parameter target leftRoot rightRoot input := by
  constructor
  · intro hguess
    exact havoid.1
      (rootAwarePlannedCandidate?_eq_some_of_encodingInputGuessesRoot state hguess)
  · intro hguess
    exact havoid.2
      (rootAwarePlannedCandidate?_eq_some_of_encodingInputGuessesRoot state hguess)

def cleanRunReturnedValue? : Option (CleanRunResult (α × SplitHashCache)) → Option α
  | none => none
  | some result => some result.value.1

theorem evalDist_cleanRunReturnedValue_eq_of_rootEncodingStored
    {parameter : PublicParameter} {target : Position}
    {leftRoot rightRoot : Digest}
    {left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (hrelates : RootEncodingCacheRelatesStored parameter target leftRoot rightRoot left right)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hstored : StoredLayerRoot state target leftRoot) :
    evalDist (cleanRunReturnedValue? <$>
        runCleanFromTable state fuel table (left.run leftCache)) =
      evalDist (cleanRunReturnedValue? <$>
        runCleanFromTable state fuel table (right.run rightCache)) := by
  have hrun := hrelates leftCache rightCache hcache state fuel table hstored
  have hprojected : RelTriple
      (runCleanFromTable state fuel table (left.run leftCache))
      (runCleanFromTable state fuel table (right.run rightCache))
      (fun leftResult rightResult =>
        cleanRunReturnedValue? leftResult = cleanRunReturnedValue? rightResult) := by
    apply relTriple_post_mono hrun
    intro leftResult rightResult hresult
    cases leftResult with
    | none =>
        cases rightResult with
        | none => rfl
        | some rightResult => simp [RootEncodingStoredCleanSameRel] at hresult
    | some leftResult =>
        cases rightResult with
        | none => simp [RootEncodingStoredCleanSameRel] at hresult
        | some rightResult =>
            simp only [RootEncodingStoredCleanSameRel, RootEncodingCleanSameRel] at hresult
            simp [cleanRunReturnedValue?, hresult.1.2.2.2.1]
  have hmapped : RelTriple
      (cleanRunReturnedValue? <$>
        runCleanFromTable state fuel table (left.run leftCache))
      (cleanRunReturnedValue? <$>
        runCleanFromTable state fuel table (right.run rightCache))
      (fun leftValue rightValue => leftValue = rightValue) :=
    relTriple_map hprojected
  exact evalDist_eq_of_relTriple_eqRel hmapped

theorem evalDist_rootAvoidingComputation_returnedValue_eq
    (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target leftRoot rightRoot leftCache rightCache)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hstored : StoredLayerRoot state target leftRoot) :
    evalDist (cleanRunReturnedValue? <$>
        runCleanFromTable state fuel table
          ((simulateQ (maskedExpandedAdversaryImpl parameter publicRoot ftsSecret)
            (rootAvoidingComputation parameter target leftRoot rightRoot computation)).run
              leftCache)) =
      evalDist (cleanRunReturnedValue? <$>
        runCleanFromTable state fuel table
          ((simulateQ
            (maskedExpandedAdversaryImplWithTargetComparison parameter publicRoot target
              rightRoot ftsSecret)
            (rootAvoidingComputation parameter target leftRoot rightRoot computation)).run
              rightCache)) :=
  evalDist_cleanRunReturnedValue_eq_of_rootEncodingStored
    (rootEncodingCacheRelatesStored_simulateQ_rootAvoidingComputation parameter publicRoot target
      hroot leftRoot rightRoot ftsSecret computation)
    leftCache rightCache hcache state fuel table hstored

theorem probEvent_uniform_root_matches_distribution_independent_guess_le
    (run : Digest → ProbComp α) (reference : ProbComp α)
    (heq : ∀ root, evalDist (run root) = evalDist reference)
    (guess : α → Digest) :
    Pr[fun result : Digest × α => result.1 = guess result.2 | do
        let root ← ($ᵗ Digest : ProbComp Digest)
        let result ← run root
        pure (root, result)] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let sampled := ($ᵗ Digest : ProbComp Digest)
  let dependent : ProbComp (Digest × α) := do
    let root ← sampled
    let result ← run root
    pure (root, result)
  let independent : ProbComp (Digest × α) := do
    let result ← reference
    let root ← sampled
    pure (root, result)
  have hreplace : evalDist dependent = evalDist (do
      let root ← sampled
      let result ← reference
      pure (root, result)) := by
    unfold dependent
    apply evalDist_bind_congr
    intro root _hroot
    rw [evalDist_bind, evalDist_bind, heq root]
  have hcommute : evalDist (do
      let root ← sampled
      let result ← reference
      pure (root, result)) = evalDist independent := by
    unfold independent
    exact OracleComp.DeferredSampling.evalDist_bind_comm sampled reference
      (fun root result => pure (root, result))
  change Pr[fun result : Digest × α => result.1 = guess result.2 | dependent] ≤ _
  calc
    _ = Pr[fun result : Digest × α => result.1 = guess result.2 | independent] := by
      exact OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) (hreplace.trans hcommute)
    _ ≤ ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      unfold independent
      apply probEvent_bind_le_of_forall_le
      intro result _hresult
      rw [show (do
          let root ← sampled
          pure (root, result)) =
        (fun root => (root, result)) <$> sampled by
          simp [map_eq_bind_pure_comp], probEvent_map]
      change Pr[fun root : Digest => root = guess result | sampled] ≤ _
      rw [probEvent_eq_eq_probOutput, probOutput_uniformSample]
      rw [show Fintype.card Digest = 2 ^ digestBits by simp]

theorem probEvent_uniform_root_matches_symmetric_two_root_run_le
    (run : Digest → Digest → ProbComp α)
    (reference : Digest → ProbComp α)
    (hright : ∀ leftRoot rightRoot,
      evalDist (run leftRoot rightRoot) = evalDist (reference leftRoot))
    (hswap : ∀ leftRoot rightRoot,
      evalDist (run leftRoot rightRoot) = evalDist (run rightRoot leftRoot))
    (guess : α → Digest) :
    Pr[fun result : Digest × α => result.1 = guess result.2 | do
        let leftRoot ← ($ᵗ Digest : ProbComp Digest)
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        let result ← run leftRoot rightRoot
        pure (leftRoot, result)] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let sampled := ($ᵗ Digest : ProbComp Digest)
  let outerRun (leftRoot : Digest) : ProbComp α := do
    let rightRoot ← sampled
    run leftRoot rightRoot
  have hreference (leftRoot : Digest) :
      evalDist (reference leftRoot) = evalDist (reference (default : Digest)) := by
    calc
      _ = evalDist (run leftRoot default) := (hright leftRoot default).symm
      _ = evalDist (run default leftRoot) := hswap leftRoot default
      _ = _ := hright default leftRoot
  have houter (leftRoot : Digest) :
      evalDist (outerRun leftRoot) = evalDist (reference (default : Digest)) := by
    calc
      _ = evalDist (sampled >>= fun _ => reference leftRoot) := by
        unfold outerRun
        apply evalDist_bind_congr
        intro rightRoot _hrightRoot
        exact hright leftRoot rightRoot
      _ = evalDist (reference leftRoot) :=
        OracleComp.DeferredSampling.evalDist_bind_const_neverFails sampled (by simp [sampled])
          (reference leftRoot)
      _ = _ := hreference leftRoot
  have hbound := probEvent_uniform_root_matches_distribution_independent_guess_le
    outerRun (reference default) houter guess
  simpa only [outerRun, sampled, bind_assoc] using hbound

theorem privateWitnessAtOrdinal_of_firstPrivateWitnessOrdinal?_eq_some
    {witness : PrivateHitWitness} {candidates : List Probe}
    {ordinal : Fin candidates.length}
    (hfirst : firstPrivateWitnessOrdinal? witness candidates = some ordinal) :
    PrivateWitnessAtOrdinal witness candidates ordinal := by
  classical
  let matching := Finset.univ.filter fun selected : Fin candidates.length =>
    PrivateWitnessAtOrdinal witness candidates selected
  have hmatching : matching.Nonempty := by
    by_contra hnone
    unfold firstPrivateWitnessOrdinal? at hfirst
    simp [matching, hnone] at hfirst
  unfold firstPrivateWitnessOrdinal? at hfirst
  simp only [matching, hmatching, dif_pos, Option.some.injEq] at hfirst
  subst ordinal
  exact (Finset.mem_filter.mp (matching.min'_mem hmatching)).2

theorem earlier_candidate_ne_of_witnessFirstUsesOrdinal
    {ordinal : Nat} {output : PrivateWitnessPlanOutput}
    (hfirst : WitnessFirstUsesOrdinal ordinal output)
    (witness : PrivateHitWitness) (hwitness : output.1 = some witness)
    (earlier : Fin output.2.length) (hlt : earlier.val < ordinal)
    (target : Position)
    (hcoordinate : (output.2.get earlier).coordinate = .position target)
    (hposition : witness.position = target) :
    (output.2.get earlier).candidate ≠ truncateHash witness.output := by
  intro heq
  apply not_privateWitnessAtOrdinal_of_witnessFirstUsesOrdinal_of_lt hfirst earlier hlt
    witness hwitness
  unfold PrivateWitnessAtOrdinal
  exact ⟨hcoordinate.trans (congrArg Coordinate.position hposition.symm), heq.symm⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
