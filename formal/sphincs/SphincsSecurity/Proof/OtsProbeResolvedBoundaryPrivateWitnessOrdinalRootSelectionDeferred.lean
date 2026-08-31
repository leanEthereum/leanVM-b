import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionProbability

/-!
# Deferred selection to materialized selection

The ordinary refinement relation is generalized to two computations. This is the semantic bridge
between the real deferred planned suffix and the materialized suffix that executes the same public
plan. A private first fire on the deferred side remains an admissible stopped outcome; a
materialization-only discrepancy makes the right side doomed.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def Probe.AvoidsRoots
    (target : Position) (leftRoot rightRoot : Digest) (candidate : Probe) : Prop :=
  candidate ≠ ⟨.position target, leftRoot⟩ ∧
    candidate ≠ ⟨.position target, rightRoot⟩

def CandidatesAvoidRoots
    (target : Position) (leftRoot rightRoot : Digest)
    (candidates : List Probe) : Prop :=
  ∀ candidate ∈ candidates, candidate.AvoidsRoots target leftRoot rightRoot

def PrivateOrdinalSelection.GoodForRoots
    (target : Position) (leftOutput : HashOutput)
    (rightRoot : Digest) (ordinal : Nat)
    (selection : PrivateOrdinalSelection) : Prop :=
  selection.candidate = ⟨.position target, truncateHash leftOutput⟩ ∧
    selection.context.state.values (.position target) = none ∧
    Coordinate.position target ∉ selection.context.state.revealed ∧
    selection.context.values target = some leftOutput ∧
    CandidatesAvoidRoots target (truncateHash leftOutput) rightRoot
      (selection.candidates.take ordinal)

def privateOrdinalSelectionGoodForRoots
    (target : Position) (leftOutput : HashOutput)
    (rightRoot : Digest) (ordinal : Nat) :
    Option PrivateOrdinalSelection → Prop
  | none => False
  | some selection => selection.GoodForRoots target leftOutput rightRoot ordinal

def materializedOrdinalSelectionMatches
    (target : Position) (root : Digest) : Option Probe → Prop
  | none => False
  | some candidate => candidate = ⟨.position target, root⟩

theorem canonicalized_right_values_eq_of_finalizationContextLE
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextLE table left right)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hcanonical : CanonicalMaterializedValues table left) :
    (canonicalizeMaterializedValues table right).state.values = left.state.values := by
  funext coordinate
  rw [hcanonical]
  unfold canonicalizeMaterializedValues publicMaterializedValues
  by_cases hleftRevealed : coordinate ∈ left.state.revealed
  · have hrightRevealed : coordinate ∈ right.state.revealed := by
      rw [← hrevealed]
      exact hleftRevealed
    simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
    exact (congrFun hcontext.view.valueEq coordinate).symm
  · have hrightRevealed : coordinate ∉ right.state.revealed := by
      intro hmem
      exact hleftRevealed (by rwa [hrevealed])
    simp [hleftRevealed, hrightRevealed]

theorem CandidatesAvoidRoots.nil
    (target : Position) (leftRoot rightRoot : Digest) :
    CandidatesAvoidRoots target leftRoot rightRoot [] := by
  simp [CandidatesAvoidRoots]

theorem CandidatesAvoidRoots.append
    {target : Position} {leftRoot rightRoot : Digest}
    {candidates : List Probe}
    (hprefix : CandidatesAvoidRoots target leftRoot rightRoot candidates)
    (candidate : Probe) (hcandidate : candidate.AvoidsRoots target leftRoot rightRoot) :
    CandidatesAvoidRoots target leftRoot rightRoot (candidates ++ [candidate]) := by
  intro other hmem
  rcases List.mem_append.mp hmem with hleft | hright
  · exact hprefix other hleft
  · have heq : other = candidate := by simpa using hright
    subst other
    exact hcandidate

theorem rootAwareCandidateAvoidsRoots_iff
    (target : Position) (leftRoot rightRoot : Digest) (candidate : Probe) :
    RootAwareCandidateAvoidsRoots target leftRoot rightRoot (some candidate) ↔
      candidate.AvoidsRoots target leftRoot rightRoot := by
  simp [RootAwareCandidateAvoidsRoots, Probe.AvoidsRoots]

theorem not_goodForRoots_of_unsafe_prefix
    {target : Position} {leftOutput : HashOutput} {rightRoot : Digest}
    {ordinal : Nat} {selection : PrivateOrdinalSelection}
    {initial : List Probe} {candidate : Probe}
    (hgood : selection.GoodForRoots target leftOutput rightRoot ordinal)
    (hprefix : initial.IsPrefix selection.candidates)
    (hlength : initial.length ≤ ordinal)
    (hmem : candidate ∈ initial)
    (hunsafe : ¬candidate.AvoidsRoots target (truncateHash leftOutput) rightRoot) : False := by
  have htake := hprefix.take ordinal
  have htakePrefix : initial.IsPrefix (selection.candidates.take ordinal) := by
    rw [(List.take_eq_self_iff initial).2 hlength] at htake
    exact htake
  have hcandidate : candidate ∈ selection.candidates.take ordinal :=
    htakePrefix.sublist.subset hmem
  exact hunsafe (hgood.2.2.2.2 candidate hcandidate)

theorem firstMissingInputCoordinatePlan_eq_of_values_eq
    {left right : LazyRevealProbe.State Coordinate}
    (hvalues : left.values = right.values)
    (input : HashInput) : ∀ slot coordinates,
    firstMissingInputCoordinatePlan left input slot coordinates =
      firstMissingInputCoordinatePlan right input slot coordinates := by
  intro slot coordinates
  induction coordinates generalizing slot with
  | nil => rfl
  | cons coordinate remaining ih =>
      rw [firstMissingInputCoordinatePlan, firstMissingInputCoordinatePlan]
      have hvalue := congrFun hvalues coordinate
      cases hleft : left.values coordinate with
      | none =>
          have hright : right.values coordinate = none := by rwa [← hvalue]
          rw [hright]
      | some output =>
          have hright : right.values coordinate = some output := by rwa [← hvalue]
          rw [hright]
          exact ih (slot + 1)

theorem leafInputProbePlan_eq_of_values_eq
    {left right : LazyRevealProbe.State Coordinate}
    (hvalues : left.values = right.values)
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    leafInputProbePlan left input candidate lay tree leafIdx =
      leafInputProbePlan right input candidate lay tree leafIdx := by
  unfold leafInputProbePlan
  have hvalue := congrFun hvalues candidate.coordinate
  cases hleft : left.values candidate.coordinate with
  | none =>
      have hright : right.values candidate.coordinate = none := by rwa [← hvalue]
      rw [hright]
  | some output =>
      have hright : right.values candidate.coordinate = some output := by rwa [← hvalue]
      rw [hright]
      exact firstMissingInputCoordinatePlan_eq_of_values_eq hvalues input 0 _

theorem purePlanProbingHashQuery_eq_of_values_eq
    {left right : LazyRevealProbe.State Coordinate}
    (hvalues : left.values = right.values)
    (parameter : PublicParameter) (input : HashInput) :
    purePlanProbingHashQuery parameter input left =
      purePlanProbingHashQuery parameter input right := by
  unfold purePlanProbingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases hposition : decodePosition? parameter input with
      | none => rfl
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              simp only
              rw [leafInputProbePlan_eq_of_values_eq hvalues]
          | chain | node | ftsLeaf | ftsNode | ftsRoots => rfl
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => rfl
      | some position =>
          cases position with
          | node lay tree level nodeIdx =>
              simp only
              rw [firstMissingInputCoordinatePlan_eq_of_values_eq hvalues]
          | chain | leaf | ftsLeaf | ftsNode | ftsRoots => rfl

def OrdinaryMaterializedStableCouplesBetween
    (table : OtsSecretIndex → HashOutput)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftContext rightContext leftFuel rightFuel leftCache rightCache,
    FinalizationContextLE table leftContext rightContext →
    leftFuel ≤ rightFuel →
    ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
    leftContext.state.revealed = rightContext.state.revealed →
    LazyRevealProbe.ValuesLE leftContext.state rightContext.state →
    PublishedValues leftContext.state →
    rightContext = directDeferredContext rightContext.state →
    RelTriple
      (runDirectResolvedDetailedFromTable leftContext leftFuel table
        (left.run leftCache))
      (runDirectResolvedDetailedFromTable rightContext rightFuel table
        (right.run rightCache))
      (DirectDetailedOrdinaryStableRunEq table)

theorem OrdinaryMaterializedStableCouples.toBetween
    {table : OtsSecretIndex → HashOutput}
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (hcomputation : OrdinaryMaterializedStableCouples table computation) :
    OrdinaryMaterializedStableCouplesBetween table computation computation :=
  hcomputation

theorem ordinaryMaterializedStableCouplesBetween_pure
    (table : OtsSecretIndex → HashOutput) (leftValue rightValue : α)
    (hvalue : leftValue = rightValue) :
    OrdinaryMaterializedStableCouplesBetween table
      (pure leftValue) (pure rightValue) := by
  subst rightValue
  exact (ordinaryMaterializedStableCouples_pure table leftValue).toBetween

theorem OrdinaryMaterializedStableCouplesBetween.bind
    {table : OtsSecretIndex → HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {leftNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    {rightNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hfirst : OrdinaryMaterializedStableCouplesBetween table left right)
    (hnext : ∀ value,
      OrdinaryMaterializedStableCouplesBetween table
        (leftNext value) (rightNext value)) :
    OrdinaryMaterializedStableCouplesBetween table
      (left >>= leftNext) (right >>= rightNext) := by
  intro leftContext rightContext leftFuel rightFuel leftCache rightCache hcontext hfuel hcache
    hrevealed hvalues hpublished hrightMaterialized
  rw [StateT.run_bind, StateT.run_bind]
  apply relTriple_runDirectResolvedDetailed_bind_stable table
    (left.run leftCache) (right.run rightCache)
    (fun value cache => (leftNext value).run cache)
    (fun value cache => (rightNext value).run cache)
    leftContext rightContext leftFuel rightFuel
  · exact hfirst leftContext rightContext leftFuel rightFuel leftCache rightCache hcontext hfuel
      hcache hrevealed hvalues hpublished hrightMaterialized
  · intro leftResult rightResult hrelation
    have hvalue : leftResult.value.1 = rightResult.value.1 := hrelation.value_eq
    rw [← hvalue]
    rw [hrelation.left_table, hrelation.right_table]
    exact hnext leftResult.value.1
      leftResult.context rightResult.context leftResult.remaining rightResult.remaining
      leftResult.value.2 rightResult.value.2 hrelation.context_le hrelation.remaining_le
      hrelation.cache_eq hrelation.revealed_eq hrelation.values_le hrelation.left_published
      hrelation.right_materialized

def OrdinaryMaterializedStableCouplesBetweenPositive
    (table : OtsSecretIndex → HashOutput)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftContext rightContext leftFuel rightFuel leftCache rightCache,
    0 < leftFuel →
    FinalizationContextLE table leftContext rightContext →
    leftFuel ≤ rightFuel →
    ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
    leftContext.state.revealed = rightContext.state.revealed →
    LazyRevealProbe.ValuesLE leftContext.state rightContext.state →
    PublishedValues leftContext.state →
    rightContext = directDeferredContext rightContext.state →
    RelTriple
      (runDirectResolvedDetailedFromTable leftContext leftFuel table
        (left.run leftCache))
      (runDirectResolvedDetailedFromTable rightContext rightFuel table
        (right.run rightCache))
      (DirectDetailedOrdinaryStableRunEq table)

theorem OrdinaryMaterializedStableCouplesBetweenPositive.bind
    {table : OtsSecretIndex → HashOutput}
    {left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {leftNext rightNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hfirst : OrdinaryMaterializedStableCouplesBetweenPositive table left right)
    (hnext : ∀ value, OrdinaryMaterializedStableCouplesBetween table
      (leftNext value) (rightNext value)) :
    OrdinaryMaterializedStableCouplesBetweenPositive table
      (left >>= leftNext) (right >>= rightNext) := by
  intro leftContext rightContext leftFuel rightFuel leftCache rightCache hpositive hcontext hfuel
    hcache hrevealed hvalues hpublished hrightMaterialized
  rw [StateT.run_bind, StateT.run_bind]
  apply relTriple_runDirectResolvedDetailed_bind_stable table
    (left.run leftCache) (right.run rightCache)
    (fun value cache => (leftNext value).run cache)
    (fun value cache => (rightNext value).run cache)
    leftContext rightContext leftFuel rightFuel
  · exact hfirst leftContext rightContext leftFuel rightFuel leftCache rightCache hpositive
      hcontext hfuel hcache hrevealed hvalues hpublished hrightMaterialized
  · intro leftResult rightResult hrelation
    have hvalue : leftResult.value.1 = rightResult.value.1 := hrelation.value_eq
    rw [← hvalue, hrelation.left_table, hrelation.right_table]
    exact hnext leftResult.value.1
      leftResult.context rightResult.context leftResult.remaining rightResult.remaining
      leftResult.value.2 rightResult.value.2 hrelation.context_le hrelation.remaining_le
      hrelation.cache_eq hrelation.revealed_eq hrelation.values_le hrelation.left_published
      hrelation.right_materialized

set_option maxRecDepth 100000 in
theorem ordinaryMaterializedStableCouplesBetween_probe
    (table : OtsSecretIndex → HashOutput) (candidate : Probe) :
    OrdinaryMaterializedStableCouplesBetweenPositive table
      (probe candidate) (probe candidate) := by
  intro left right leftFuel rightFuel leftCache rightCache hpositive hcontext hfuel hcache hrevealed
    hvalues hpublished hrightMaterialized
  cases leftFuel with
  | zero => omega
  | succ leftRemaining =>
      obtain ⟨rightRemaining, hrightFuel⟩ : ∃ rightRemaining,
          rightFuel = rightRemaining + 1 := by
        refine ⟨rightFuel - 1, ?_⟩
        omega
      subst rightFuel
      unfold probe
      simp only [StateT.run_liftM]
      unfold LazyRevealProbe.probeQuery
      rw [runDirectResolvedDetailedFromTable_probe_query_bind,
        runDirectResolvedDetailedFromTable_probe_query_bind]
      by_cases hleftRevealed : candidate.coordinate ∈ left.state.revealed
      · have hrightRevealed : candidate.coordinate ∈ right.state.revealed := by
          rw [← hrevealed]
          exact hleftRevealed
        simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
        exact (ordinaryMaterializedStableCouples_pure table ()).toBetween
          left right leftRemaining rightRemaining leftCache rightCache hcontext (by omega)
          hcache hrevealed hvalues hpublished hrightMaterialized
      · have hrightRevealed : candidate.coordinate ∉ right.state.revealed := by
          rwa [← hrevealed]
        simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
        let nextLeft : DeferredContext :=
          { left with state := left.state.addPending candidate.coordinate candidate.candidate }
        let nextRight : DeferredContext :=
          { right with state := right.state.addPending candidate.coordinate candidate.candidate }
        by_cases hcompletable : DeferredCompletable table nextRight
        · have hnext := hcontext.addPending_both_of_right_completable
            candidate.coordinate candidate.candidate hcompletable
          have hnextPublished : PublishedValues nextLeft.state := by
            simpa [nextLeft, PublishedValues, LazyRevealProbe.State.addPending] using hpublished
          exact (ordinaryMaterializedStableCouples_pure table ()).toBetween
            nextLeft nextRight leftRemaining rightRemaining leftCache rightCache hnext (by omega)
            hcache hrevealed hvalues hnextPublished (by
              show nextRight = directDeferredContext nextRight.state
              dsimp [nextRight]
              rw [hrightMaterialized]
              simp [directDeferredContext, directDeferredValues_addPending])
        · rw [runDirectResolvedDetailedFromTable_pure,
            runDirectResolvedDetailedFromTable_pure]
          apply relTriple_pure_pure
          right
          exact ⟨⟨rfl, hcontext.view.rightConsistent.addPending
                candidate.coordinate candidate.candidate,
                hcontext.view.rightStarts.addPending
                  candidate.coordinate candidate.candidate, hcompletable⟩, by
                show nextRight = directDeferredContext nextRight.state
                dsimp [nextRight]
                rw [hrightMaterialized]
                simp [directDeferredContext, directDeferredValues_addPending]⟩

theorem ordinaryMaterializedStableCouplesBetween_executeCandidate
    (table : OtsSecretIndex → HashOutput) (candidate? : Option Probe) :
    OrdinaryMaterializedStableCouplesBetweenPositive table
      (executeCandidate? candidate?) (executeCandidate? candidate?) := by
  cases candidate? with
  | none =>
      intro left right leftFuel rightFuel leftCache rightCache _hpositive
      exact ordinaryMaterializedStableCouplesBetween_pure table () () rfl
        left right leftFuel rightFuel leftCache rightCache
  | some candidate => exact ordinaryMaterializedStableCouplesBetween_probe table candidate

theorem relTriple_runDirectResolvedDetailed_publishOrdinaryInput_stable
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (input : HashInput) (output : HashOutput)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hleftValue : left.state.values coordinate = some output)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((publishOrdinaryInput coordinate input output).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((publishOrdinaryInput coordinate input output).run rightCache))
      (DirectDetailedOrdinaryStableRunEq table) := by
  have hrightValue : right.state.values coordinate = some output :=
    hvalues coordinate output hleftValue
  rw [runDirectResolvedDetailedFromTable_publishOrdinaryInput,
    runDirectResolvedDetailedFromTable_publishOrdinaryInput]
  apply relTriple_pure_pure
  left
  exact
    { value_eq := rfl
      context_le := hcontext.publish coordinate
      remaining_le := hfuel
      left_table := rfl
      right_table := rfl
      cache_eq := by
        rw [ordinaryQueryCache_update, ordinaryQueryCache_update, hcache]
      revealed_eq := by
        simpa [LazyRevealProbe.State.publish] using congrArg (insert coordinate) hrevealed
      values_le := hvalues
      left_published := hpublished.publish_of_value coordinate output hleftValue
      right_materialized := by
        rw [hrightMaterialized]
        simp [directDeferredContext, directDeferredValues_publish] }

set_option maxRecDepth 100000 in
theorem ordinaryMaterializedStableCouplesBetween_revealPublishOrdinaryInput
    (table : OtsSecretIndex → HashOutput)
    (coordinate : Coordinate) (input : HashInput) :
    OrdinaryMaterializedStableCouplesBetween table
      (revealPublishOrdinaryInput coordinate input)
      (revealPublishOrdinaryInput coordinate input) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed
    hvalues hpublished hrightMaterialized
  unfold revealPublishOrdinaryInput
  rw [StateT.run_bind, StateT.run_bind]
  apply relTriple_runDirectResolvedDetailed_bind_with_support_stable table
    ((revealCoordinateOutput coordinate).run leftCache)
    ((revealCoordinateOutput coordinate).run rightCache)
    (fun output cache => (publishOrdinaryInput coordinate input output).run cache)
    (fun output cache => (publishOrdinaryInput coordinate input output).run cache)
    left right leftFuel rightFuel
  · exact ordinaryMaterializedStableCouples_revealCoordinateOutput table coordinate
      left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed hvalues
      hpublished hrightMaterialized
  · intro leftResult rightResult hleftSupport _hrightSupport hrelation
    have hleftValue :=
      value_of_done_runDirectResolvedDetailedFromTable_revealCoordinateOutput table coordinate
        left leftFuel leftCache leftResult hleftSupport
    rw [hrelation.left_table, hrelation.right_table, ← hrelation.value_eq]
    exact relTriple_runDirectResolvedDetailed_publishOrdinaryInput_stable table coordinate input
      leftResult.value.1 leftResult.context rightResult.context leftResult.remaining
      rightResult.remaining leftResult.value.2 rightResult.value.2 hrelation.context_le
      hrelation.remaining_le hrelation.cache_eq hrelation.revealed_eq hrelation.values_le
      hrelation.left_published hleftValue hrelation.right_materialized

theorem ordinaryMaterializedStableCouplesBetween_resolvePublicKnownInput
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (publicState : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (input : HashInput) :
    OrdinaryMaterializedStableCouplesBetween table
      (resolvePublicKnownInput parameter publicState coordinate input)
      (resolvePublicKnownInput parameter publicState coordinate input) := by
  unfold resolvePublicKnownInput
  cases hknown : purePeekTableInput parameter publicState coordinate with
  | none =>
      exact (ordinaryMaterializedStableCouples_splitHashQuery_ordinary table input).toBetween
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        simpa [revealPublishOrdinaryInput, publishOrdinaryInput] using
          ordinaryMaterializedStableCouplesBetween_revealPublishOrdinaryInput table coordinate
            input
      · simp only [heq, ↓reduceIte]
        exact (ordinaryMaterializedStableCouples_splitHashQuery_ordinary table input).toBetween

theorem ordinaryMaterializedStableCouplesBetweenPositive_publicPlan
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery) :
    OrdinaryMaterializedStableCouplesBetweenPositive table
      (probingHashQueryAfterPublicPlan parameter input publicState plan)
      (probingHashQueryAfterPublicPlan parameter input publicState plan) := by
  unfold probingHashQueryAfterPublicPlan
  apply (ordinaryMaterializedStableCouplesBetween_executeCandidate table plan.candidate?).bind
  intro _
  cases plan.action with
  | ordinary =>
      exact (ordinaryMaterializedStableCouples_splitHashQuery_ordinary table input).toBetween
  | resolve coordinate =>
      exact ordinaryMaterializedStableCouplesBetween_resolvePublicKnownInput table parameter
        publicState coordinate input

theorem ordinaryMaterializedStableCouplesBetween_publicPlan_of_none
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (hcandidate : plan.candidate? = none) :
    OrdinaryMaterializedStableCouplesBetween table
      (probingHashQueryAfterPublicPlan parameter input publicState plan)
      (probingHashQueryAfterPublicPlan parameter input publicState plan) := by
  unfold probingHashQueryAfterPublicPlan
  rw [show executeCandidate? plan.candidate? = pure () by simp [hcandidate]]
  simp only [pure_bind]
  cases plan.action with
  | ordinary =>
      exact (ordinaryMaterializedStableCouples_splitHashQuery_ordinary table input).toBetween
  | resolve coordinate =>
      exact ordinaryMaterializedStableCouplesBetween_resolvePublicKnownInput table parameter
        publicState coordinate input

theorem runDirectResolvedDetailedFromTable_peekPositionValues_eq_pure
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ∀ positions,
    runDirectResolvedDetailedFromTable context fuel table
        ((peekPositionValues positions).run cache) =
      pure (.done ⟨context, fuel,
        (purePeekPositionValues context.state positions, cache), table⟩)
  | [] => by
      simp [peekPositionValues, purePeekPositionValues,
        runDirectResolvedDetailedFromTable]
  | position :: remaining => by
      rw [peekPositionValues, StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
        runDirectResolvedDetailedFromTable_peekCoordinate]
      cases hvalue : truncateHash <$> context.state.values (.position position) with
      | none =>
          simp [purePeekPositionValues, hvalue, runDirectResolvedDetailedFromTable]
      | some value =>
          simp only [pure_bind]
          rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_eq_pure context fuel table cache
              remaining]
          cases htail : purePeekPositionValues context.state remaining <;>
            simp [purePeekPositionValues, hvalue, htail, runDirectResolvedDetailedFromTable]

set_option maxRecDepth 100000 in
theorem runDirectResolvedDetailedFromTable_peekTableInput_eq_pure
    (parameter : PublicParameter) (coordinate : Coordinate)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runDirectResolvedDetailedFromTable context fuel table
        ((peekTableInput parameter coordinate).run cache) =
      pure (.done ⟨context, fuel,
        (purePeekTableInput parameter context.state coordinate, cache), table⟩) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [peekTableInput, purePeekTableInput, runDirectResolvedDetailedFromTable]
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput.eq_2]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero]
            rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
              runDirectResolvedDetailedFromTable_peekCoordinate]
            cases hvalue : truncateHash <$>
                context.state.values (.chainStart lay tree leafIdx chainIdx) <;>
              simp [purePeekTableInput, hzero, hvalue,
                runDirectResolvedDetailedFromTable]
          · rw [if_neg hzero]
            rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
              runDirectResolvedDetailedFromTable_peekPositionValues_eq_pure]
            cases hvalues : purePeekPositionValues context.state
                (Position.chain lay tree leafIdx chainIdx step).children <;>
              simp [purePeekTableInput, hzero, hvalues,
                runDirectResolvedDetailedFromTable]
      | leaf lay tree leafIdx =>
          simp only [peekTableInput]
          rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_eq_pure]
          cases hvalues : purePeekPositionValues context.state _ <;>
            simp [purePeekTableInput, hvalues, runDirectResolvedDetailedFromTable]
      | node lay tree level nodeIdx =>
          simp only [peekTableInput]
          rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_eq_pure]
          cases hvalues : purePeekPositionValues context.state _ <;>
            simp [purePeekTableInput, hvalues, runDirectResolvedDetailedFromTable]
      | ftsLeaf index tree leafIdx =>
          simp only [peekTableInput]
          rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_eq_pure]
          cases hvalues : purePeekPositionValues context.state _ <;>
            simp [purePeekTableInput, hvalues, runDirectResolvedDetailedFromTable]
      | ftsNode index tree level nodeIdx =>
          simp only [peekTableInput]
          rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_eq_pure]
          cases hvalues : purePeekPositionValues context.state _ <;>
            simp [purePeekTableInput, hvalues, runDirectResolvedDetailedFromTable]
      | ftsRoots index =>
          simp only [peekTableInput]
          rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_eq_pure]
          cases hvalues : purePeekPositionValues context.state _ <;>
            simp [purePeekTableInput, hvalues, runDirectResolvedDetailedFromTable]

set_option maxRecDepth 100000 in
theorem runDirectResolvedDetailedFromTable_resolveKnownInput_eq_public
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runDirectResolvedDetailedFromTable context fuel table
        ((resolveKnownInput parameter coordinate input).run cache) =
      runDirectResolvedDetailedFromTable context fuel table
        ((resolvePublicKnownInput parameter context.state coordinate input).run cache) := by
  unfold resolveKnownInput resolvePublicKnownInput
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_peekTableInput_eq_pure]
  simp only [pure_bind]
  cases hknown : purePeekTableInput parameter context.state coordinate with
  | none => rfl
  | some knownInput =>
      by_cases heq : knownInput = input <;> simp [heq]

theorem purePeekPositionValues_eq_of_values_eq
    {left right : LazyRevealProbe.State Coordinate}
    (hvalues : left.values = right.values) : ∀ positions,
    purePeekPositionValues left positions = purePeekPositionValues right positions
  | [] => rfl
  | position :: remaining => by
      simp only [purePeekPositionValues]
      rw [hvalues]
      cases truncateHash <$> right.values (.position position) with
      | none => rfl
      | some value => rw [purePeekPositionValues_eq_of_values_eq hvalues remaining]

theorem purePeekTableInput_eq_of_values_eq
    (parameter : PublicParameter)
    {left right : LazyRevealProbe.State Coordinate}
    (hvalues : left.values = right.values) (coordinate : Coordinate) :
    purePeekTableInput parameter left coordinate =
      purePeekTableInput parameter right coordinate := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx => rfl
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          simp only [purePeekTableInput]
          by_cases hzero : step.val = 0
          · simp only [hzero, ↓reduceIte]
            rw [hvalues]
          · simp only [hzero, ↓reduceIte]
            rw [purePeekPositionValues_eq_of_values_eq hvalues]
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp only [purePeekTableInput]
          rw [purePeekPositionValues_eq_of_values_eq hvalues]

theorem resolvePublicKnownInput_eq_of_values_eq
    (parameter : PublicParameter)
    {left right : LazyRevealProbe.State Coordinate}
    (hvalues : left.values = right.values)
    (coordinate : Coordinate) (input : HashInput) :
    resolvePublicKnownInput parameter left coordinate input =
      resolvePublicKnownInput parameter right coordinate input := by
  unfold resolvePublicKnownInput
  rw [purePeekTableInput_eq_of_values_eq parameter hvalues coordinate]

theorem probingHashQueryAfterPublicPlan_eq_of_values_eq
    (parameter : PublicParameter) (input : HashInput)
    {left right : LazyRevealProbe.State Coordinate}
    (hvalues : left.values = right.values) (plan : PlannedHashQuery) :
    probingHashQueryAfterPublicPlan parameter input left plan =
      probingHashQueryAfterPublicPlan parameter input right plan := by
  unfold probingHashQueryAfterPublicPlan
  apply bind_congr
  intro _
  cases plan.action with
  | ordinary => rfl
  | resolve coordinate =>
      exact resolvePublicKnownInput_eq_of_values_eq parameter hvalues coordinate input

set_option maxRecDepth 100000 in
theorem runDirectResolvedDetailedFromTable_afterPlan_eq_publicPlan
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runDirectResolvedDetailedFromTable context fuel table
        ((probingHashQueryAfterPlan parameter input plan).run cache) =
      runDirectResolvedDetailedFromTable context fuel table
        ((probingHashQueryAfterPublicPlan parameter input context.state plan).run cache) := by
  unfold probingHashQueryAfterPlan probingHashQueryAfterPublicPlan executePlannedHashQuery
  cases hcandidate : plan.candidate? with
  | none =>
      simp only [executeCandidate?, pure_bind]
      cases haction : plan.action with
      | ordinary => rfl
      | resolve coordinate =>
          exact runDirectResolvedDetailedFromTable_resolveKnownInput_eq_public parameter
            coordinate input context fuel table cache
  | some candidate =>
      simp only [executeCandidate?]
      rw [StateT.run_bind, StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
        runDirectResolvedDetailedFromTable_bind]
      simp only [probe, StateT.run_liftM, LazyRevealProbe.probeQuery,
        runDirectResolvedDetailedFromTable_probe_query_bind]
      cases fuel with
      | zero => rfl
      | succ remaining =>
          by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
          · simp only [hrevealed, ↓reduceIte]
            rw [runDirectResolvedDetailedFromTable_pure, pure_bind]
            cases haction : plan.action with
            | ordinary => rfl
            | resolve coordinate =>
                exact runDirectResolvedDetailedFromTable_resolveKnownInput_eq_public parameter
                  coordinate input context remaining table cache
          · simp only [hrevealed, ↓reduceIte]
            let nextContext : DeferredContext :=
              { context with state :=
                  context.state.addPending candidate.coordinate candidate.candidate }
            rw [show
              runDirectResolvedDetailedFromTable nextContext remaining table (pure ((), cache)) =
                pure (.done ⟨nextContext, remaining, ((), cache), table⟩) by
              exact runDirectResolvedDetailedFromTable_pure _ _ _ _]
            simp only [pure_bind]
            cases haction : plan.action with
            | ordinary => rfl
            | resolve coordinate =>
                have hbase := runDirectResolvedDetailedFromTable_resolveKnownInput_eq_public
                  parameter coordinate input nextContext remaining table cache
                have hpublic := resolvePublicKnownInput_eq_of_values_eq parameter
                  (left := nextContext.state) (right := context.state) (by
                    rfl) coordinate input
                rw [hpublic] at hbase
                exact hbase

theorem relTriple_runDirectResolvedDetailed_afterPlan_publicPlan
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hpositive : 0 < leftFuel)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((probingHashQueryAfterPlan parameter input plan).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((probingHashQueryAfterPublicPlan parameter input left.state plan).run rightCache))
      (DirectDetailedOrdinaryStableRunEq table) := by
  rw [runDirectResolvedDetailedFromTable_afterPlan_eq_publicPlan parameter input plan left
    leftFuel table leftCache]
  exact ordinaryMaterializedStableCouplesBetweenPositive_publicPlan table parameter input
    left.state plan left right leftFuel rightFuel leftCache rightCache hpositive hcontext hfuel
    hcache hrevealed hvalues hpublished hrightMaterialized

theorem relTriple_runDirectResolvedDetailed_afterPlan_publicPlan_of_none
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcandidate : plan.candidate? = none)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedDetailedFromTable left leftFuel table
        ((probingHashQueryAfterPlan parameter input plan).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((probingHashQueryAfterPublicPlan parameter input left.state plan).run rightCache))
      (DirectDetailedOrdinaryStableRunEq table) := by
  rw [runDirectResolvedDetailedFromTable_afterPlan_eq_publicPlan parameter input plan left
    leftFuel table leftCache]
  exact ordinaryMaterializedStableCouplesBetween_publicPlan_of_none table parameter input
    left.state plan hcandidate left right leftFuel rightFuel leftCache rightCache hcontext hfuel
    hcache hrevealed hvalues hpublished hrightMaterialized

noncomputable def finishDirectDetailedPrivateOrdinalSelection
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (candidates : List Probe) : DirectDetailedResult α →
      ProbComp (Option PrivateOrdinalSelection)
  | .stopped _ => pure none
  | .done result => observe result.context result.remaining result.value candidates

theorem finishDirectPrivateOrdinalSelection_eq_detailed
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (candidates : List Probe) (result : DirectWitnessResult α) :
    finishDirectPrivateOrdinalSelection observe candidates result =
      finishDirectDetailedPrivateOrdinalSelection observe candidates result.erase := by
  cases result <;> rfl

theorem evalDist_runWitnessSelection_eq_detailed
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    evalDist
        (runDirectResolvedWitnessFromTable context fuel table computation >>=
          finishDirectPrivateOrdinalSelection observe candidates) =
      evalDist
        (runDirectResolvedDetailedFromTable context fuel table computation >>=
          finishDirectDetailedPrivateOrdinalSelection observe candidates) := by
  have herase := map_erase_runDirectResolvedWitnessFromTable computation context fuel table
  calc
    _ = evalDist
        ((DirectWitnessResult.erase <$>
            runDirectResolvedWitnessFromTable context fuel table computation) >>=
          finishDirectDetailedPrivateOrdinalSelection observe candidates) := by
      rw [map_eq_bind_pure_comp, bind_assoc]
      apply evalDist_bind_congr
      intro result _hresult
      simp only [Function.comp_apply, pure_bind]
      exact congrArg evalDist
        (finishDirectPrivateOrdinalSelection_eq_detailed observe candidates result)
    _ = _ := by rw [herase]

def projectDirectDetailedClean
    (result : DirectDetailedResult α) : Option (CleanRunResult α) :=
  projectResolvedRunResult result.toOption

theorem map_projectDirectDetailedClean_run_eq_clean
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    projectDirectDetailedClean <$>
        runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table computation =
      runCleanFromTable state fuel table computation := by
  unfold projectDirectDetailedClean
  rw [← Functor.map_map, map_toOption_runDirectResolvedDetailedFromTable,
    map_projectResolvedRunResult_runDirect_eq_runClean]

noncomputable def finishDirectDetailedMaterializedSelection
    (target : Position)
    (observe : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp (Option Probe))
    (candidates : List Probe) :
    DirectDetailedResult (α × SplitHashCache) → ProbComp (Option Probe)
  | .stopped _ => pure none
  | .done result =>
      continueMaterializedPrivateOrdinalSelection target observe result.context.state result.remaining
        result.value.1 result.value.2 candidates

theorem finishDirectDetailedMaterializedSelection_eq_clean
    (target : Position)
    (observe : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp (Option Probe))
    (candidates : List Probe)
    (result : DirectDetailedResult (α × SplitHashCache)) :
    finishDirectDetailedMaterializedSelection target observe candidates result =
      finishMaterializedPrivateOrdinalSelection
        (continueMaterializedPrivateOrdinalSelection target observe) candidates
      (projectDirectDetailedClean result) := by
  cases result with
  | stopped reason => rfl
  | done result =>
      simp [finishDirectDetailedMaterializedSelection,
        finishMaterializedPrivateOrdinalSelection, projectDirectDetailedClean,
        DirectDetailedResult.toOption, projectResolvedRunResult]

theorem evalDist_runDetailedMaterializedSelection_eq_clean
    (target : Position)
    (observe : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp (Option Probe))
    (candidates : List Probe)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate)
      (α × SplitHashCache)) :
    evalDist
        (runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table computation >>=
          finishDirectDetailedMaterializedSelection target observe candidates) =
      evalDist
        (runCleanFromTable state fuel table computation >>=
          finishMaterializedPrivateOrdinalSelection
            (continueMaterializedPrivateOrdinalSelection target observe) candidates) := by
  have hproject := map_projectDirectDetailedClean_run_eq_clean computation state fuel table
  calc
    _ = evalDist
        ((projectDirectDetailedClean <$>
            runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
              computation) >>=
          finishMaterializedPrivateOrdinalSelection
            (continueMaterializedPrivateOrdinalSelection target observe) candidates) := by
      rw [map_eq_bind_pure_comp, bind_assoc]
      apply evalDist_bind_congr
      intro result _hresult
      simp only [Function.comp_apply, pure_bind]
      exact congrArg evalDist
        (finishDirectDetailedMaterializedSelection_eq_clean target observe candidates result)
    _ = _ := by rw [hproject]

end SphincsSecurity.Concrete.OtsProbeSimulation
